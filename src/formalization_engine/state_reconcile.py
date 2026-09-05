from __future__ import annotations

import base64
import io
import json
import os
import re
import subprocess
import tarfile
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Iterable

from formalization_engine.block_id_naming import (
    canonicalize_block_id,
    extract_chapter,
    is_canonical_base_id,
    is_canonical_block_id,
)
from formalization_engine.core.canonical_resolver import canonical_resolver
from formalization_engine.core.legacy_support_projection import (
    LegacySupportProjectionError,
    read_legacy_support_projection,
)

from .phase1_plan_audit import normalize_phase1_task_type
from .review_versions import profile_for_catalog

from .state_store import (
    SubjectBundle,
    WorkspaceStateStore,
    canonical_subject_bytes,
    sha256_bytes,
    utc_now,
)


CHAPTER_RE = re.compile(r"chapter_?(\d+)", re.IGNORECASE)
KENNETH_REPO = "wkshum/ProbabilityTheory"

FORMAL_PLAN_TYPE_PREFIXES = {
    "Definition": "def_",
    "Theorem_Statement": "thm_",
    "Theorem_with_Proof": "thm_",
    "Example_Proof": "ex_",
    "Problem": "prob_",
}

# Kenneth's repository uses this filename for the implementation of part 4 of
# Theorem 1.2.  In the ToyApollo ledger it is support owned by task `thm_1_2`,
# not a second textbook task.  Keep the target filename while preserving one
# canonical task identity across repositories.
TASK_PARENT_ALIASES = {
    "thm_1_2_4": "thm_1_2",
}


class ReconciliationError(RuntimeError):
    pass


@dataclass(frozen=True)
class CommandResult:
    returncode: int
    stdout: bytes
    stderr: bytes

    @property
    def text(self) -> str:
        return self.stdout.decode("utf-8", errors="replace")

    @property
    def error_text(self) -> str:
        return self.stderr.decode("utf-8", errors="replace")


def run_command(argv: list[str], *, cwd: Path | None = None, timeout: int = 30) -> CommandResult:
    try:
        completed = subprocess.run(
            argv,
            cwd=str(cwd) if cwd else None,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise ReconciliationError(f"Command failed to run: {argv!r}: {exc}") from exc
    return CommandResult(completed.returncode, completed.stdout, completed.stderr)


def discover_formal_plan_task_ids(
    plans_dir: Path,
    *,
    chapters: Iterable[int] | None = None,
) -> set[str]:
    """Return canonical non-Remark task ids declared by Phase 1 plans.

    Plan type decides whether an entry is a formal task.  Canonical block-id
    utilities decide whether its id is valid.  This keeps named formal entries
    distinct from similarly prefixed support files.
    """

    requested_chapters = set(chapters or [])
    task_ids: set[str] = set()
    if not plans_dir.is_dir():
        return task_ids
    for plan_path in sorted(plans_dir.rglob("*_plan.json")):
        try:
            payload = json.loads(plan_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        entries = payload if isinstance(payload, list) else []
        for raw in entries:
            if not isinstance(raw, dict):
                continue
            normalized_type, _note = normalize_phase1_task_type(raw.get("type", ""))
            expected_prefix = FORMAL_PLAN_TYPE_PREFIXES.get(str(normalized_type or ""))
            if not expected_prefix:
                continue
            task_id = canonicalize_block_id(str(raw.get("block_id", "") or ""))
            if not is_canonical_block_id(task_id) or not task_id.startswith(expected_prefix):
                continue
            chapter = extract_chapter(task_id)
            if requested_chapters and chapter not in requested_chapters:
                continue
            task_ids.add(task_id)
    return task_ids


def task_id_from_path(
    path: str,
    *,
    formal_task_ids: Iterable[str] | None = None,
) -> str:
    stem = Path(path).stem
    task_id = canonicalize_block_id(stem)
    task_id = TASK_PARENT_ALIASES.get(task_id, task_id)
    if not is_canonical_base_id(task_id):
        return ""
    if formal_task_ids is not None:
        allowed = {canonicalize_block_id(item) for item in formal_task_ids}
        if task_id not in allowed:
            return ""
    return task_id


def chapter_for_task(task_id: str) -> int | None:
    match = re.match(r"^[a-z]+_(\d+)(?:_|$)", task_id, re.IGNORECASE)
    return int(match.group(1)) if match else None


def is_primary_task_path(path: str, task_id: str) -> bool:
    return Path(path).stem.lower() == task_id.lower()


def is_task_owned_path(
    path: str,
    task_id: str,
    primary_path: str,
    *,
    formal_task_ids: Iterable[str] | None = None,
) -> bool:
    normalized = path.replace("\\", "/")
    normalized_primary = primary_path.replace("\\", "/")
    if normalized == normalized_primary:
        return True
    candidate = PurePosixPath(normalized)
    primary = PurePosixPath(normalized_primary)
    primary_parts = [part.lower() for part in primary.parts]
    content_root = primary.parent
    for index, part in enumerate(primary_parts):
        if part == "toyapollo" and index + 1 < len(primary_parts) and primary_parts[index + 1] == "output":
            content_root = PurePosixPath(*primary.parts[: index + 2])
            break
        if re.fullmatch(r"chapter_?\d+", part):
            content_root = PurePosixPath(*primary.parts[: index + 1])
            break
    try:
        relative = candidate.relative_to(content_root)
    except ValueError:
        return False
    if any(part.lower() in {"review_contracts", "tests", "test"} for part in relative.parts[:-1]):
        return False
    stem = Path(normalized).stem.lower()
    task = task_id.lower()
    parts = [part.lower() for part in Path(normalized).parts]
    if formal_task_ids is not None:
        candidate_task = task_id_from_path(
            normalized,
            formal_task_ids=formal_task_ids,
        )
        if candidate_task and candidate_task != task_id and stem == candidate_task.lower():
            return False
    if f"{task}_support" in parts:
        return True
    return stem.startswith(f"{task}_") and not stem.startswith(f"{task}_review")


def discover_runtime_support_files(
    runtime_root: Path,
    task_id: str,
    *,
    formal_task_ids: Iterable[str] | None = None,
    manifest_required: bool = True,
) -> dict[str, bytes]:
    """Return manifest-owned support files for one canonical task."""

    root = runtime_root.resolve()
    if not (root / "manifest_by_chapter.csv").is_file():
        try:
            legacy = read_legacy_support_projection(root, task_id)
        except LegacySupportProjectionError as exc:
            raise ReconciliationError(str(exc)) from exc
        if legacy:
            return legacy
        if manifest_required:
            raise ReconciliationError(
                f"Canonical manifest is required but missing: {root / 'manifest_by_chapter.csv'}"
            )
        output_root = root / "ProbabilityTheory"
        if not output_root.is_dir():
            return {}
        primary_candidates = list(output_root.rglob(f"{task_id}.lean"))
        if len(primary_candidates) > 1:
            return {}
        primary = (
            primary_candidates[0].resolve().relative_to(root).as_posix()
            if primary_candidates
            else f"ProbabilityTheory/{task_id}.lean"
        )
        support: dict[str, bytes] = {}
        for path in output_root.rglob("*.lean"):
            logical_path = path.resolve().relative_to(root).as_posix()
            if logical_path == primary:
                continue
            if is_task_owned_path(
                logical_path,
                task_id,
                primary,
                formal_task_ids=formal_task_ids,
            ):
                support[logical_path] = path.read_bytes()
        return support
    resolver = canonical_resolver(root)
    canonical_task = canonicalize_block_id(task_id)
    if formal_task_ids is None:
        formal_task_ids = discover_formal_plan_task_ids(root / "plans")
    formal_ids = {
        canonicalize_block_id(item)
        for item in formal_task_ids
        if canonicalize_block_id(item)
    }

    def support_owner(basename: str) -> str:
        lowered = basename.lower()
        candidates = [
            item for item in formal_ids if lowered.startswith(f"{item}_")
        ]
        if not candidates:
            return ""
        return max(candidates, key=len)

    support: dict[str, bytes] = {}
    for entry in resolver.entries:
        if entry.classification != "task_owned_support_module":
            continue
        if support_owner(entry.basename) != canonical_task:
            continue
        path = (root / entry.relative_path).resolve()
        if not path.is_file():
            raise ReconciliationError(f"Manifest-owned support file is missing: {path}")
        support[entry.relative_path] = path.read_bytes()
    return support


def _git(repo: Path, *args: str, timeout: int = 30) -> bytes:
    result = run_command(["git", "-C", str(repo), *args], timeout=timeout)
    if result.returncode != 0:
        raise ReconciliationError(
            f"git {' '.join(args)} failed in {repo}: {result.error_text.strip()}"
        )
    return result.stdout


def git_ref_exists(repo: Path, ref: str) -> bool:
    result = run_command(["git", "-C", str(repo), "rev-parse", "--verify", "--quiet", ref])
    return result.returncode == 0


def git_current_branch(repo: Path) -> str:
    return _git(repo, "branch", "--show-current").decode("utf-8", errors="replace").strip()


def git_ref_paths(repo: Path, ref: str) -> list[str]:
    raw = _git(repo, "ls-tree", "-r", "--name-only", ref)
    return [line.strip() for line in raw.decode("utf-8", errors="replace").splitlines() if line.strip()]


def git_file_at_ref(repo: Path, ref: str, path: str) -> bytes:
    return _git(repo, "show", f"{ref}:{path}")


def git_files_at_ref(repo: Path, ref: str, paths: Iterable[str]) -> dict[str, bytes]:
    """Read many pinned files with one Git archive process."""

    requested = {str(path).replace("\\", "/") for path in paths}
    if not requested:
        return {}
    roots = sorted({path.split("/", 1)[0] for path in requested})
    raw = _git(repo, "archive", "--format=tar", ref, "--", *roots, timeout=120)
    found: dict[str, bytes] = {}
    with tarfile.open(fileobj=io.BytesIO(raw), mode="r:") as archive:
        for member in archive.getmembers():
            if not member.isfile() or member.name not in requested:
                continue
            handle = archive.extractfile(member)
            if handle is not None:
                found[member.name] = handle.read()
    missing = sorted(requested - set(found))
    if missing:
        raise ReconciliationError(f"Git archive at {ref} omitted requested files: {missing}")
    return found


def discover_git_subjects(
    repo: Path,
    *,
    ref: str,
    source_repo: str,
    layout: str,
    chapters: Iterable[int] | None = None,
    task_ids: Iterable[str] | None = None,
    formal_task_ids: Iterable[str] | None = None,
) -> dict[str, SubjectBundle]:
    if not (repo / ".git").exists():
        return {}
    requested_chapters = set(chapters or [])
    requested_tasks = {canonicalize_block_id(task_id) for task_id in (task_ids or []) if canonicalize_block_id(task_id)}
    commit = _git(repo, "rev-parse", ref).decode("ascii", errors="replace").strip()
    paths = [path for path in git_ref_paths(repo, ref) if path.lower().endswith(".lean")]
    primary_by_task: dict[str, str] = {}
    for path in paths:
        task_id = task_id_from_path(path, formal_task_ids=formal_task_ids)
        if not task_id or not is_primary_task_path(path, task_id):
            continue
        chapter = chapter_for_task(task_id)
        if requested_chapters and chapter not in requested_chapters:
            continue
        if requested_tasks and task_id not in requested_tasks:
            continue
        primary_by_task.setdefault(task_id, path)
    subjects: dict[str, SubjectBundle] = {}
    for task_id, primary in sorted(primary_by_task.items()):
        owned_paths = [
            path
            for path in paths
            if is_task_owned_path(
                path,
                task_id,
                primary,
                formal_task_ids=formal_task_ids,
            )
        ]
        files = {path: git_file_at_ref(repo, ref, path) for path in owned_paths}
        subjects[task_id] = SubjectBundle.from_files(
            task_id=task_id,
            files=files,
            primary_path=primary,
            source_repo=source_repo,
            source_commit=commit,
            layout=layout,
            subject_kind="git_bundle",
        )
    return subjects


def discover_catalog_git_subjects(
    repo: Path,
    *,
    ref: str,
    catalog: Any,
    source_repo: str,
    layout: str,
    chapters: Iterable[int] | None = None,
    task_ids: Iterable[str] | None = None,
    identity_schema: str | None = None,
) -> dict[str, SubjectBundle]:
    """Materialize exact bundles from explicit catalog ownership edges."""

    if not (repo / ".git").exists():
        return {}
    requested_chapters = set(chapters or [])
    requested_tasks = {
        canonicalize_block_id(task_id)
        for task_id in (task_ids or [])
        if canonicalize_block_id(task_id)
    }
    commit = _git(repo, "rev-parse", ref).decode("ascii", errors="replace").strip()
    available = set(git_ref_paths(repo, ref))
    selected_tasks = [
        task
        for task in catalog.tasks
        if (not requested_chapters or task.chapter in requested_chapters)
        and (not requested_tasks or task.task_id in requested_tasks)
    ]
    requested_paths = {
        path for task in selected_tasks for path in catalog.owned_paths(task.task_id)
    }
    file_payloads = git_files_at_ref(repo, ref, requested_paths)
    subjects: dict[str, SubjectBundle] = {}
    for task in selected_tasks:
        owned_paths = list(catalog.owned_paths(task.task_id))
        if not owned_paths or task.primary_path not in owned_paths:
            raise ReconciliationError(
                f"Catalog task {task.task_id} lacks its declared primary path in owned membership."
            )
        missing = sorted(set(owned_paths) - available)
        if missing:
            raise ReconciliationError(
                f"Catalog task {task.task_id} has files absent from {ref}: {missing}"
            )
        files = {path: file_payloads[path] for path in owned_paths}
        subjects[task.task_id] = SubjectBundle.from_files(
            task_id=task.task_id,
            files=files,
            primary_path=task.primary_path,
            source_repo=source_repo,
            source_commit=commit,
            layout=layout,
            subject_kind="catalog_git_bundle",
            identity_schema=identity_schema,
        )
    return subjects


def discover_worktree_subjects(
    repo: Path,
    *,
    source_repo: str,
    layout: str,
    chapters: Iterable[int] | None = None,
    task_ids: Iterable[str] | None = None,
    formal_task_ids: Iterable[str] | None = None,
) -> dict[str, SubjectBundle]:
    if not (repo / ".git").exists():
        return {}
    requested_chapters = set(chapters or [])
    requested_tasks = {canonicalize_block_id(task_id) for task_id in (task_ids or []) if canonicalize_block_id(task_id)}
    commit = _git(repo, "rev-parse", "HEAD").decode("ascii", errors="replace").strip()
    paths: list[str] = []
    scan_root = repo
    if not scan_root.is_dir():
        return {}
    for directory, names, files in os.walk(scan_root):
        names[:] = [
            name
            for name in names
            if name not in {".lake", ".git", "_review-worktrees", "__pycache__", "node_modules"}
        ]
        for filename in files:
            if filename.lower().endswith(".lean"):
                paths.append((Path(directory) / filename).relative_to(repo).as_posix())
    primary_by_task: dict[str, str] = {}
    for path in paths:
        task_id = task_id_from_path(path, formal_task_ids=formal_task_ids)
        if not task_id or not is_primary_task_path(path, task_id):
            continue
        chapter = chapter_for_task(task_id)
        if requested_chapters and chapter not in requested_chapters:
            continue
        if requested_tasks and task_id not in requested_tasks:
            continue
        primary_by_task.setdefault(task_id, path)
    subjects: dict[str, SubjectBundle] = {}
    for task_id, primary in sorted(primary_by_task.items()):
        owned_paths = [
            path
            for path in paths
            if is_task_owned_path(
                path,
                task_id,
                primary,
                formal_task_ids=formal_task_ids,
            )
        ]
        files = {path: (repo / path).read_bytes() for path in owned_paths}
        subjects[task_id] = SubjectBundle.from_files(
            task_id=task_id,
            files=files,
            primary_path=primary,
            source_repo=source_repo,
            source_commit=f"{commit}+worktree",
            layout=layout,
            subject_kind="worktree_bundle",
        )
    return subjects


def discover_catalog_worktree_subjects(
    repo: Path,
    *,
    catalog: Any,
    source_repo: str,
    layout: str,
    chapters: Iterable[int] | None = None,
    task_ids: Iterable[str] | None = None,
) -> dict[str, SubjectBundle]:
    """Materialize a worktree view without repeated filename heuristics."""

    if not (repo / ".git").exists():
        return {}
    profile = profile_for_catalog(catalog)
    requested_chapters = set(chapters or []) if profile == "mat" else set()
    requested_tasks = {
        canonicalize_block_id(task_id, profile)
        for task_id in (task_ids or [])
        if canonicalize_block_id(task_id, profile)
    }
    commit = _git(repo, "rev-parse", "HEAD").decode("ascii", errors="replace").strip()
    paths: list[str] = []
    if layout == "toy":
        scan_root = repo / "ToyApollo/Output"
    elif layout == "unified":
        scan_root = repo / "ProbabilityTheory"
    else:
        scan_root = repo
    if not scan_root.is_dir():
        return {}
    for directory, names, files in os.walk(scan_root):
        names[:] = [
            name
            for name in names
            if name not in {".lake", ".git", "_review-worktrees", "__pycache__", "node_modules"}
        ]
        for filename in files:
            if filename.lower().endswith(".lean"):
                paths.append((Path(directory) / filename).relative_to(repo).as_posix())
    exact_paths = set(paths)
    if getattr(catalog, "task_module_paths", None):
        subjects: dict[str, SubjectBundle] = {}
        for task in catalog.tasks:
            if requested_chapters and task.chapter not in requested_chapters:
                continue
            if requested_tasks and task.task_id not in requested_tasks:
                continue
            owned_paths = list(catalog.owned_paths(task.task_id))
            if not owned_paths or task.primary_path not in owned_paths:
                raise ReconciliationError(
                    f"Catalog task {task.task_id} lacks its declared primary path in owned membership."
                )
            missing = sorted(set(owned_paths) - exact_paths)
            if missing:
                raise ReconciliationError(
                    f"Catalog task {task.task_id} has files absent from worktree {repo}: {missing}"
                )
            files = {path: (repo / path).read_bytes() for path in owned_paths}
            subjects[task.task_id] = SubjectBundle.from_files(
                task_id=task.task_id,
                files=files,
                primary_path=task.primary_path,
                source_repo=source_repo,
                source_commit=f"{commit}+worktree",
                layout=layout,
                subject_kind="catalog_worktree_bundle",
            )
        return subjects

    by_basename: dict[str, list[str]] = {}
    for path in paths:
        by_basename.setdefault(Path(path).stem.lower(), []).append(path)
    module_by_owner: dict[str, list[Any]] = {}
    for module in catalog.modules:
        if module.owner_task_id and module.module_role in {"primary", "owned_support"}:
            module_by_owner.setdefault(module.owner_task_id, []).append(module)

    subjects: dict[str, SubjectBundle] = {}
    for task in catalog.tasks:
        if requested_chapters and task.chapter not in requested_chapters:
            continue
        if requested_tasks and task.task_id not in requested_tasks:
            continue
        logical_files: dict[str, bytes] = {}
        primary_path = ""
        for module in module_by_owner.get(task.task_id, []):
            if layout in {"mat", "unified"} and module.path in exact_paths:
                matches = [module.path]
            else:
                matches = by_basename.get(module.basename.lower(), [])
            if len(matches) > 1:
                raise ReconciliationError(
                    f"Catalog module {module.basename} is ambiguous in {repo}: {matches}"
                )
            if not matches:
                if module.module_role == "primary":
                    raise ReconciliationError(
                        f"Catalog primary {module.basename} is missing from worktree {repo}."
                    )
                continue
            logical_path = matches[0]
            logical_files[logical_path] = (repo / logical_path).read_bytes()
            if module.module_role == "primary":
                primary_path = logical_path
        if not primary_path:
            raise ReconciliationError(f"Catalog task {task.task_id} has no worktree primary in {repo}.")
        subjects[task.task_id] = SubjectBundle.from_files(
            task_id=task.task_id,
            files=logical_files,
            primary_path=primary_path,
            source_repo=source_repo,
            source_commit=f"{commit}+worktree",
            layout=layout,
            subject_kind="catalog_worktree_bundle",
        )
    return subjects


def store_subject_heads(
    store: WorkspaceStateStore,
    subjects: dict[str, SubjectBundle],
    *,
    role: str,
    freshness: str = "fresh",
    detail: dict[str, Any] | None = None,
) -> int:
    count = 0
    observed_at = utc_now()
    for task_id, subject in subjects.items():
        store.upsert_subject(subject)
        store.set_task_head(
            task_id=task_id,
            role=role,
            subject_id=subject.subject_id,
            observed_at=observed_at,
            freshness=freshness,
            detail=detail,
        )
        count += 1
    return count


def refresh_local_repositories(
    store: WorkspaceStateStore,
    *,
    workspace_root: Path,
    runtime_root: Path,
    chapters: Iterable[int] = (1, 2, 3, 4),
    task_ids: Iterable[str] | None = None,
    formal_task_ids: Iterable[str] | None = None,
    catalog: Any | None = None,
    fetch: bool = False,
) -> dict[str, Any]:
    if (
        catalog is not None
        and getattr(catalog, "schema_version", "")
        == "formalization-engine.task-catalog.v2"
    ):
        result: dict[str, Any] = {
            "unified_main": 0,
            "unified_candidate": 0,
            "legacy_mat_main": 0,
            "errors": [],
        }
        requested = [
            canonicalize_block_id(task_id)
            for task_id in (task_ids or [])
            if canonicalize_block_id(task_id)
        ]
        for role in ("unified_main", "unified_candidate", "mat_main"):
            if requested:
                for task_id in requested:
                    store.mark_task_head_freshness(
                        task_id=task_id, role=role, freshness="stale"
                    )
            else:
                store.mark_role_freshness(role=role, freshness="stale")
        if not (runtime_root / ".git").exists():
            result["errors"].append(
                f"Unified runtime repository is missing: {runtime_root}"
            )
            return result
        try:
            subjects = discover_catalog_git_subjects(
                runtime_root,
                ref=catalog.repository_commit,
                catalog=catalog,
                source_repo="ProbabilityTheoryFormalization",
                layout="unified",
                chapters=chapters,
                task_ids=task_ids,
            )
            result["unified_main"] = store_subject_heads(
                store,
                subjects,
                role="unified_main",
                detail={
                    "repo": str(runtime_root),
                    "ref": catalog.repository_commit,
                    "catalog_id": catalog.catalog_id,
                },
            )
        except ReconciliationError as exc:
            result["errors"].append(str(exc))
        mat_repo = workspace_root / "MAT3280-formalization-output"
        if (mat_repo / ".git").exists():
            try:
                subjects = discover_catalog_git_subjects(
                    mat_repo,
                    ref=catalog.corpus_origin_commit,
                    catalog=catalog,
                    source_repo="mat",
                    layout="mat",
                    chapters=chapters,
                    task_ids=task_ids,
                    identity_schema="toy-apollo.subject.v1",
                )
                result["legacy_mat_main"] = store_subject_heads(
                    store,
                    subjects,
                    role="mat_main",
                    detail={
                        "repo": str(mat_repo),
                        "ref": catalog.corpus_origin_commit,
                        "legacy_origin_for_catalog": catalog.catalog_id,
                    },
                )
            except ReconciliationError as exc:
                result["errors"].append(str(exc))
        else:
            result["errors"].append(
                f"Legacy MAT corpus-origin repository is missing: {mat_repo}"
            )
        try:
            subjects = discover_catalog_worktree_subjects(
                runtime_root,
                catalog=catalog,
                source_repo="ProbabilityTheoryFormalization",
                layout="unified",
                chapters=chapters,
                task_ids=task_ids,
            )
            result["unified_candidate"] = store_subject_heads(
                store,
                subjects,
                role="unified_candidate",
                freshness="local",
                detail={
                    "repo": str(runtime_root),
                    "working_tree": True,
                    "catalog_id": catalog.catalog_id,
                },
            )
        except ReconciliationError as exc:
            result["errors"].append(str(exc))
        return result

    profile = profile_for_catalog(catalog) if catalog is not None else "mat"
    if catalog is not None and profile != "mat":
        current_role = f"{profile}_current"
        result: dict[str, Any] = {current_role: 0, "errors": []}
        requested = [
            canonicalize_block_id(task_id, profile)
            for task_id in (task_ids or [])
            if canonicalize_block_id(task_id, profile)
        ]
        if requested:
            for task_id in requested:
                store.mark_task_head_freshness(
                    task_id=task_id,
                    role=current_role,
                    freshness="stale",
                )
        else:
            store.mark_role_freshness(role=current_role, freshness="stale")
        if not (runtime_root / ".git").exists():
            result["errors"].append(
                f"{profile} runtime repository is missing: {runtime_root}"
            )
            return result
        try:
            subjects = discover_catalog_worktree_subjects(
                runtime_root,
                catalog=catalog,
                source_repo=profile,
                layout=profile,
                chapters=chapters,
                task_ids=task_ids,
            )
            result[current_role] = store_subject_heads(
                store,
                subjects,
                role=current_role,
                detail={
                    "repo": str(runtime_root),
                    "working_tree": True,
                    "profile": profile,
                },
            )
        except ReconciliationError as exc:
            result["errors"].append(str(exc))
        return result

    result: dict[str, Any] = {"mat_main": 0, "mat_candidate": 0, "toy_current": 0, "errors": []}
    requested = [canonicalize_block_id(task_id) for task_id in (task_ids or []) if canonicalize_block_id(task_id)]
    for role in ("mat_main", "mat_candidate", "toy_current"):
        if requested:
            for task_id in requested:
                store.mark_task_head_freshness(task_id=task_id, role=role, freshness="stale")
        else:
            store.mark_role_freshness(role=role, freshness="stale")
    mat_repo = workspace_root / "MAT3280-formalization-output"
    if (mat_repo / ".git").exists():
        if fetch:
            fetched = run_command(["git", "-C", str(mat_repo), "fetch", "--prune", "origin"], timeout=60)
            if fetched.returncode != 0:
                result["errors"].append(f"MAT fetch failed: {fetched.error_text.strip()}")
        main_ref = (
            str(catalog.mat_commit)
            if catalog is not None
            else ("origin/main" if git_ref_exists(mat_repo, "origin/main") else "main")
        )
        try:
            if catalog is not None:
                subjects = discover_catalog_git_subjects(
                    mat_repo,
                    ref=main_ref,
                    catalog=catalog,
                    source_repo="mat",
                    layout="mat",
                    chapters=chapters,
                    task_ids=task_ids,
                )
            else:
                subjects = discover_git_subjects(
                    mat_repo,
                    ref=main_ref,
                    source_repo="mat",
                    layout="mat",
                    chapters=chapters,
                    task_ids=task_ids,
                    formal_task_ids=formal_task_ids,
                )
            result["mat_main"] = store_subject_heads(
                store,
                subjects,
                role="mat_main",
                detail={"repo": str(mat_repo), "ref": main_ref},
            )
        except ReconciliationError as exc:
            result["errors"].append(str(exc))
        try:
            branch = git_current_branch(mat_repo)
            if catalog is not None:
                subjects = discover_catalog_worktree_subjects(
                    mat_repo,
                    catalog=catalog,
                    source_repo="mat",
                    layout="mat",
                    chapters=chapters,
                    task_ids=task_ids,
                )
            else:
                subjects = discover_worktree_subjects(
                    mat_repo,
                    source_repo="mat",
                    layout="mat",
                    chapters=chapters,
                    task_ids=task_ids,
                    formal_task_ids=formal_task_ids,
                )
            result["mat_candidate"] = store_subject_heads(
                store,
                subjects,
                role="mat_candidate",
                detail={"repo": str(mat_repo), "branch": branch, "working_tree": True},
            )
        except ReconciliationError as exc:
            result["errors"].append(str(exc))
    if (runtime_root / ".git").exists():
        try:
            if catalog is not None:
                subjects = discover_catalog_worktree_subjects(
                    runtime_root,
                    catalog=catalog,
                    source_repo="formalization_engine",
                    layout="toy",
                    chapters=chapters,
                    task_ids=task_ids,
                )
            else:
                subjects = discover_worktree_subjects(
                    runtime_root,
                    source_repo="formalization_engine",
                    layout="toy",
                    chapters=chapters,
                    task_ids=task_ids,
                    formal_task_ids=formal_task_ids,
                )
            result["toy_current"] = store_subject_heads(
                store,
                subjects,
                role="toy_current",
                detail={"repo": str(runtime_root), "working_tree": True},
            )
        except ReconciliationError as exc:
            result["errors"].append(str(exc))
    return result


def _gh_json(endpoint: str, *, query: dict[str, str] | None = None, timeout: int = 60) -> Any:
    argv = ["gh", "api", "--method", "GET", endpoint]
    for key, value in (query or {}).items():
        argv.extend(["-f", f"{key}={value}"])
    result = run_command(argv, timeout=timeout)
    if result.returncode != 0:
        raise ReconciliationError(f"GitHub refresh failed for {endpoint}: {result.error_text.strip()}")
    try:
        return json.loads(result.stdout.decode("utf-8"))
    except json.JSONDecodeError as exc:
        raise ReconciliationError(f"GitHub returned invalid JSON for {endpoint}: {exc}") from exc


def discover_github_subjects(
    *,
    repo: str,
    ref: str,
    source_repo: str,
    layout: str,
    task_ids: Iterable[str] | None = None,
    chapters: Iterable[int] | None = None,
    formal_task_ids: Iterable[str] | None = None,
) -> tuple[str, dict[str, SubjectBundle]]:
    requested_tasks = {canonicalize_block_id(task_id) for task_id in (task_ids or []) if canonicalize_block_id(task_id)}
    requested_chapters = set(chapters or [])
    commit_payload = _gh_json(f"repos/{repo}/commits/{ref}")
    commit_sha = str(commit_payload.get("sha", ""))
    tree_payload = _gh_json(f"repos/{repo}/git/trees/{commit_sha}", query={"recursive": "1"})
    entries = [
        entry
        for entry in tree_payload.get("tree", [])
        if entry.get("type") == "blob" and str(entry.get("path", "")).lower().endswith(".lean")
    ]
    primary_by_task: dict[str, str] = {}
    by_path = {str(entry["path"]): entry for entry in entries}
    for path in by_path:
        task_id = task_id_from_path(path, formal_task_ids=formal_task_ids)
        if not task_id or not is_primary_task_path(path, task_id):
            continue
        chapter = chapter_for_task(task_id)
        if requested_tasks and task_id not in requested_tasks:
            continue
        if requested_chapters and chapter not in requested_chapters:
            continue
        primary_by_task.setdefault(task_id, path)
    subjects: dict[str, SubjectBundle] = {}
    for task_id, primary in sorted(primary_by_task.items()):
        manifests: list[dict[str, Any]] = []
        for path, entry in by_path.items():
            if not is_task_owned_path(
                path,
                task_id,
                primary,
                formal_task_ids=formal_task_ids,
            ):
                continue
            blob_sha = str(entry.get("sha", ""))
            content_hash = ""
            size = int(entry.get("size", 0) or 0)
            # Fetch the primary content so exact local/remote equality can be
            # established. Support blobs retain their Git identity; fetching
            # every large support family would be unnecessarily expensive.
            if path == primary and requested_tasks:
                blob = _gh_json(f"repos/{repo}/git/blobs/{blob_sha}")
                encoded = str(blob.get("content", "") or "").replace("\n", "")
                raw = base64.b64decode(encoded) if encoded else b""
                from .state_store import sha256_bytes

                content_hash = sha256_bytes(raw)
                size = len(raw)
            manifests.append(
                {
                    "path": path,
                    "content_sha256": content_hash,
                    "git_blob_sha": blob_sha,
                    "size": size,
                }
            )
        subjects[task_id] = SubjectBundle.from_manifest(
            task_id=task_id,
            files=manifests,
            primary_path=primary,
            source_repo=source_repo,
            source_commit=commit_sha,
            layout=layout,
            subject_kind="github_bundle",
        )
    return commit_sha, subjects


def refresh_kenneth_github(
    store: WorkspaceStateStore,
    *,
    task_ids: Iterable[str] | None = None,
    chapters: Iterable[int] = (1, 2, 3, 4),
    formal_task_ids: Iterable[str] | None = None,
) -> dict[str, Any]:
    requested = list(task_ids or [])
    result: dict[str, Any] = {"repo": KENNETH_REPO, "subjects": 0, "pull_requests": 0, "errors": []}
    if requested:
        for task_id in requested:
            store.mark_task_head_freshness(task_id=task_id, role="kenneth_main", freshness="stale")
    else:
        store.mark_role_freshness(role="kenneth_main", freshness="stale")
    try:
        commit_sha, subjects = discover_github_subjects(
            repo=KENNETH_REPO,
            ref="main",
            source_repo="kenneth",
            layout="kenneth",
            task_ids=requested or None,
            chapters=chapters,
            formal_task_ids=formal_task_ids,
        )
        result["commit_sha"] = commit_sha
        result["subjects"] = store_subject_heads(
            store,
            subjects,
            role="kenneth_main",
            freshness="fresh",
            detail={"repo": KENNETH_REPO, "ref": "main"},
        )
    except ReconciliationError as exc:
        result["errors"].append(str(exc))
        if requested:
            for task_id in requested:
                store.mark_task_head_freshness(task_id=task_id, role="kenneth_main", freshness="unavailable")
        else:
            store.mark_role_freshness(role="kenneth_main", freshness="unavailable")
        store.mark_integrations_freshness(target_repo="kenneth", freshness="unavailable")
        return result

    # For a task-specific refresh, bind PR observations by the files actually
    # changed. This catches browser-created PRs and squashed merges without
    # relying on an agent remembering to update local state.
    try:
        pulls = _gh_json(
            f"repos/{KENNETH_REPO}/pulls",
            query={"state": "all" if requested else "open", "per_page": "100"},
        )
        requested_set = {canonicalize_block_id(task_id) for task_id in requested}
        for pull in pulls:
                number = int(pull.get("number", 0) or 0)
                if not number:
                    continue
                files = _gh_json(f"repos/{KENNETH_REPO}/pulls/{number}/files", query={"per_page": "100"})
                affected = {
                    task_id_from_path(
                        str(item.get("filename", "")),
                        formal_task_ids=formal_task_ids,
                    )
                    for item in files
                    if task_id_from_path(
                        str(item.get("filename", "")),
                        formal_task_ids=formal_task_ids,
                    )
                }
                selected = requested_set & affected if requested_set else affected
                head_repo = str((pull.get("head", {}).get("repo") or {}).get("full_name", "") or "")
                head_sha = str(pull.get("head", {}).get("sha", "") or "")
                for task_id in sorted(selected):
                    merged = bool(pull.get("merged_at"))
                    state = "merged" if merged else str(pull.get("state", "unknown"))
                    head_subject_id = ""
                    if head_repo and head_sha:
                        try:
                            _commit, head_subjects = discover_github_subjects(
                                repo=head_repo,
                                ref=head_sha,
                                source_repo="kenneth_pr",
                                layout="kenneth",
                                task_ids=[task_id],
                                formal_task_ids=formal_task_ids,
                            )
                            head_subject = head_subjects.get(task_id)
                            if head_subject is not None:
                                store.upsert_subject(head_subject)
                                head_subject_id = head_subject.subject_id
                        except ReconciliationError as exc:
                            result["errors"].append(f"PR #{number} head for {task_id}: {exc}")
                    store.record_integration(
                        task_id=task_id,
                        target_repo="kenneth",
                        integration_kind="pull_request",
                        state=state,
                        branch=str(pull.get("head", {}).get("ref", "")),
                        pr_number=number,
                        head_sha=head_sha,
                        merge_sha=str(pull.get("merge_commit_sha", "") or ""),
                        head_subject_id=head_subject_id,
                        observed_at=utc_now(),
                        remote_freshness="fresh",
                        detail={"title": pull.get("title", ""), "url": pull.get("html_url", "")},
                    )
                    result["pull_requests"] += 1
    except ReconciliationError as exc:
        result["errors"].append(str(exc))
        store.mark_integrations_freshness(target_repo="kenneth", freshness="unavailable")
    return result


def refresh_workspace_state(
    store: WorkspaceStateStore,
    *,
    workspace_root: Path,
    runtime_root: Path,
    task_ids: Iterable[str] | None = None,
    chapters: Iterable[int] = (1, 2, 3, 4),
    refresh_remote: bool = False,
    catalog: Any | None = None,
) -> dict[str, Any]:
    store.initialize()
    formal_task_ids = (
        set(catalog.task_ids())
        if catalog is not None
        else discover_formal_plan_task_ids(runtime_root / "plans", chapters=chapters)
    )
    result = {
        "local": refresh_local_repositories(
            store,
            workspace_root=workspace_root,
            runtime_root=runtime_root,
            chapters=chapters,
            task_ids=task_ids,
            formal_task_ids=formal_task_ids,
            catalog=catalog,
            fetch=refresh_remote,
        ),
        "remote": None,
    }
    if refresh_remote:
        result["remote"] = refresh_kenneth_github(
            store,
            task_ids=task_ids,
            chapters=chapters,
            formal_task_ids=formal_task_ids,
        )
    result["dependency_pins"] = store.revalidate_dependency_pins()
    return result
