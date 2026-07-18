from __future__ import annotations

import base64
import json
import os
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Iterable

from src.block_id_naming import (
    canonicalize_block_id,
    extract_chapter,
    is_canonical_base_id,
)

from .phase1_plan_audit import normalize_phase1_task_type

from .state_store import SubjectBundle, WorkspaceStateStore, utc_now


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
            if not is_canonical_base_id(task_id) or not task_id.startswith(expected_prefix):
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
) -> dict[str, bytes]:
    """Return every current task-owned support file, excluding the public primary file."""

    root = runtime_root.resolve()
    output_root = root / "ToyApollo" / "Output"
    primary = f"ToyApollo/Output/{task_id}.lean"
    if not output_root.is_dir():
        return {}
    if formal_task_ids is None:
        formal_task_ids = discover_formal_plan_task_ids(runtime_root / "plans")
    support: dict[str, bytes] = {}
    for path in output_root.rglob("*.lean"):
        if not path.is_file():
            continue
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
    for directory, names, files in os.walk(repo):
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
    fetch: bool = False,
) -> dict[str, Any]:
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
        main_ref = "origin/main" if git_ref_exists(mat_repo, "origin/main") else "main"
        try:
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
            subjects = discover_worktree_subjects(
                runtime_root,
                source_repo="toy_apollo",
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
) -> dict[str, Any]:
    store.initialize()
    formal_task_ids = discover_formal_plan_task_ids(
        runtime_root / "plans",
        chapters=chapters,
    )
    result = {
        "local": refresh_local_repositories(
            store,
            workspace_root=workspace_root,
            runtime_root=runtime_root,
            chapters=chapters,
            task_ids=task_ids,
            formal_task_ids=formal_task_ids,
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
