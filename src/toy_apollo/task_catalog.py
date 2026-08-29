from __future__ import annotations

import csv
import hashlib
import io
import json
import re
import subprocess
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

from src.block_id_naming import canonicalize_block_id, extract_chapter, is_canonical_block_id

from .phase1_plan_audit import normalize_phase1_task_type


CATALOG_SCHEMA_VERSION = "toy-apollo.task-catalog.v1"
POLICY_SCHEMA_VERSION = "toy-apollo.task-catalog-policy.v1"
CORDIS_POLICY_SCHEMA_VERSION = "cordis.task-catalog-policy.v1"
DEFAULT_POLICY_PATH = Path("data/task_catalog/catalog_policy_v1.json")

DEFAULT_PROFILE = "mat"
CORDIS_PROFILE = "cordis"

FORMAL_PLAN_TYPE_PREFIXES = {
    "Definition": "def_",
    "Theorem_Statement": "thm_",
    "Theorem_with_Proof": "thm_",
    "Example_Proof": "ex_",
    "Problem": "prob_",
    "Lemma": "lem_",
    "Corollary": "cor_",
}
LEGACY_TASK_ROLE = "ledger_task_module"
LEGACY_OWNED_ROLE = "task_owned_support_module"
LEGACY_SHARED_ROLE = "shared_support_or_bridge"


class CatalogError(RuntimeError):
    """Raised when catalog inputs cannot prove a complete, unambiguous model."""


def _sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _sha256_json(payload: Any) -> str:
    raw = json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    return _sha256_bytes(raw.encode("utf-8"))


def _canonical_task_id(value: Any, profile: str = DEFAULT_PROFILE) -> str:
    return canonicalize_block_id(str(value or ""), profile)


def _git_bytes(repo: Path, *args: str) -> bytes:
    try:
        completed = subprocess.run(
            ["git", *args],
            cwd=str(repo),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=60,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise CatalogError(f"Unable to read pinned Git data from {repo}: {exc}") from exc
    if completed.returncode != 0:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        raise CatalogError(f"Git command failed in {repo}: git {' '.join(args)}: {detail}")
    return completed.stdout


def _git_text(repo: Path, *args: str) -> str:
    return _git_bytes(repo, *args).decode("utf-8")


@dataclass(frozen=True)
class CatalogFamily:
    family_id: str
    book_label: str
    family_kind: str
    count_policy: str
    members: tuple[str, ...]

    def as_dict(self) -> dict[str, Any]:
        return {
            "family_id": self.family_id,
            "book_label": self.book_label,
            "family_kind": self.family_kind,
            "count_policy": self.count_policy,
            "members": list(self.members),
        }


@dataclass(frozen=True)
class CatalogTask:
    task_id: str
    family_id: str
    chapter: int
    task_kind: str
    source_plan: str
    source_plan_path: str
    source_hash: str
    primary_path: str
    legacy_manifest_role: str
    lifecycle_state: str

    def as_dict(self) -> dict[str, Any]:
        return {
            "task_id": self.task_id,
            "family_id": self.family_id,
            "chapter": self.chapter,
            "task_kind": self.task_kind,
            "source_plan": self.source_plan,
            "source_plan_path": self.source_plan_path,
            "source_hash": self.source_hash,
            "primary_path": self.primary_path,
            "legacy_manifest_role": self.legacy_manifest_role,
            "lifecycle_state": self.lifecycle_state,
        }


@dataclass(frozen=True)
class CatalogModule:
    path: str
    basename: str
    module_name: str
    module_role: str
    owner_task_id: str
    legacy_manifest_role: str
    chapter: int | None

    def as_dict(self) -> dict[str, Any]:
        return {
            "path": self.path,
            "basename": self.basename,
            "module_name": self.module_name,
            "module_role": self.module_role,
            "owner_task_id": self.owner_task_id,
            "legacy_manifest_role": self.legacy_manifest_role,
            "chapter": self.chapter,
        }


@dataclass(frozen=True)
class TaskCatalog:
    catalog_id: str
    catalog_name: str
    toy_commit: str
    mat_commit: str
    manifest_sha256: str
    plan_set_sha256: str
    policy_sha256: str
    tasks: tuple[CatalogTask, ...]
    families: tuple[CatalogFamily, ...]
    modules: tuple[CatalogModule, ...]
    cohorts: Mapping[str, tuple[str, ...]]
    restored_task_ids: tuple[str, ...]
    role_migrations: tuple[str, ...]
    # Per-profile multi-homing map (task_id -> primary module paths). Empty for
    # the MAT profile, whose ownership stays one-to-one via CatalogModule.owner_task_id.
    task_module_paths: Mapping[str, tuple[str, ...]] = field(default_factory=dict)

    @property
    def schema_version(self) -> str:
        return CATALOG_SCHEMA_VERSION

    def counts(self) -> dict[str, int]:
        return {
            "tasks": len(self.tasks),
            "families": len(self.families),
            "modules": len(self.modules),
            "primary_modules": sum(item.module_role == "primary" for item in self.modules),
            "owned_support_modules": sum(item.module_role == "owned_support" for item in self.modules),
            "shared_modules": sum(item.module_role == "shared" for item in self.modules),
            "legacy_review_roots": sum(len(items) for items in self.cohorts.values()),
            "role_migrations": len(self.role_migrations),
            "family_overrides": sum(item.family_kind != "singleton" for item in self.families),
            "family_override_members": sum(
                len(item.members) for item in self.families if item.family_kind != "singleton"
            ),
        }

    def task_ids(self, *, cohort_id: str | None = None) -> tuple[str, ...]:
        if cohort_id is None:
            return tuple(item.task_id for item in self.tasks)
        try:
            return tuple(self.cohorts[cohort_id])
        except KeyError as exc:
            raise CatalogError(f"Unknown catalog cohort: {cohort_id}") from exc

    def family_for_task(self, task_id: str) -> CatalogFamily:
        canonical = _canonical_task_id(task_id)
        task = next((item for item in self.tasks if item.task_id == canonical), None)
        if task is None:
            raise CatalogError(f"Unknown task id: {task_id}")
        return next(item for item in self.families if item.family_id == task.family_id)
    def owned_paths(self, task_id: str, *, include_primary: bool = True) -> tuple[str, ...]:
        canonical = _canonical_task_id(task_id)
        explicit = self.task_module_paths.get(canonical)
        if explicit is not None:
            return tuple(explicit) if include_primary else ()
        allowed = {"primary", "owned_support"} if include_primary else {"owned_support"}
        return tuple(
            item.path
            for item in self.modules
            if item.owner_task_id == canonical and item.module_role in allowed
        )

    def task_for_path(self, path: str) -> str | None:
        normalized = path.replace("\\", "/").lower()
        item = next((module for module in self.modules if module.path.lower() == normalized), None)
        return item.owner_task_id or None if item is not None else None

    def stable_payload(self) -> dict[str, Any]:
        payload: dict[str, Any] = {
            "schema_version": self.schema_version,
            "catalog_name": self.catalog_name,
            "toy_commit": self.toy_commit,
            "mat_commit": self.mat_commit,
            "manifest_sha256": self.manifest_sha256,
            "plan_set_sha256": self.plan_set_sha256,
            "policy_sha256": self.policy_sha256,
            "counts": self.counts(),
            "tasks": [item.as_dict() for item in self.tasks],
            "families": [item.as_dict() for item in self.families],
            "modules": [item.as_dict() for item in self.modules],
            "cohorts": {key: list(value) for key, value in sorted(self.cohorts.items())},
            "restored_task_ids": list(self.restored_task_ids),
            "role_migrations": list(self.role_migrations),
        }
        if self.task_module_paths:
            payload["task_module_paths"] = {
                key: list(value) for key, value in sorted(self.task_module_paths.items())
            }
        return payload

    def as_dict(self) -> dict[str, Any]:
        return {"catalog_id": self.catalog_id, **self.stable_payload()}


def validate_catalog_compatible_mat_commit(
    catalog: TaskCatalog,
    *,
    mat_root: Path,
    commit: str,
    manifest_path: str = "manifest_by_chapter.csv",
) -> None:
    """Validate a historical MAT commit against active catalog ownership.

    A receipt pinned to an ancestor commit may be replayed with the active
    catalog only when the catalog manifest itself is byte-identical at both
    commits.  This validates ownership only; callers must still compare every
    task bundle and dependent build before projecting authority to the active
    subject.
    """

    commit = str(commit or "")
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise CatalogError("Historical MAT commit is not a full lowercase SHA-1.")
    mat_root = Path(mat_root).resolve()
    if commit == catalog.mat_commit:
        return
    completed = subprocess.run(
        ["git", "merge-base", "--is-ancestor", commit, catalog.mat_commit],
        cwd=mat_root,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        raise CatalogError(
            "Historical MAT commit is not an ancestor of the active catalog commit."
        )
    manifest_bytes = _git_bytes(mat_root, "show", f"{commit}:{manifest_path}")
    if hashlib.sha256(manifest_bytes).hexdigest() != catalog.manifest_sha256:
        raise CatalogError(
            "Historical MAT commit uses a different catalog ownership manifest."
        )


@dataclass(frozen=True)
class _PlanTask:
    task_id: str
    task_kind: str
    source_plan: str
    source_plan_path: str
    source_hash: str


def _plan_tasks(plan_documents: Mapping[str, bytes], profile: str = DEFAULT_PROFILE) -> tuple[tuple[_PlanTask, ...], str]:
    tasks: dict[str, _PlanTask] = {}
    plan_hashes: list[dict[str, str]] = []
    for path, raw_bytes in sorted(plan_documents.items()):
        plan_hashes.append({"path": path, "sha256": _sha256_bytes(raw_bytes)})
        try:
            payload = json.loads(raw_bytes.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise CatalogError(f"Plan is not valid UTF-8 JSON: {path}: {exc}") from exc
        if not isinstance(payload, list):
            raise CatalogError(f"Plan root must be a list: {path}")
        for raw in payload:
            if not isinstance(raw, Mapping):
                continue
            normalized_type, _note = normalize_phase1_task_type(raw.get("type", ""), profile)
            task_kind = str(normalized_type or "")
            expected_prefix = FORMAL_PLAN_TYPE_PREFIXES.get(task_kind)
            if expected_prefix is None:
                continue
            task_id = _canonical_task_id(raw.get("block_id", ""), profile)
            if not is_canonical_block_id(task_id, profile) or not task_id.startswith(expected_prefix):
                raise CatalogError(f"Formal plan entry has invalid task id {task_id!r}: {path}")
            if task_id in tasks:
                raise CatalogError(
                    f"Formal task {task_id} occurs in both {tasks[task_id].source_plan_path} and {path}"
                )
            source_payload = {
                "block_id": task_id,
                "type": task_kind,
                "title": raw.get("title", ""),
                "content": raw.get("content", ""),
                "dependencies": raw.get("dependencies", []),
                "source_plan": raw.get("source_plan", "") or Path(path).stem.removesuffix("_plan"),
            }
            tasks[task_id] = _PlanTask(
                task_id=task_id,
                task_kind=task_kind,
                source_plan=str(source_payload["source_plan"]),
                source_plan_path=path,
                source_hash=_sha256_json(source_payload),
            )
    if not tasks:
        raise CatalogError("No formal tasks were found in the pinned Phase 1 plans.")
    return tuple(tasks[key] for key in sorted(tasks)), _sha256_json(plan_hashes)


def _manifest_rows(manifest_bytes: bytes) -> tuple[list[dict[str, str]], str]:
    try:
        text = manifest_bytes.decode("utf-8-sig")
    except UnicodeDecodeError as exc:
        raise CatalogError(f"MAT manifest is not UTF-8: {exc}") from exc
    rows = [dict(row) for row in csv.DictReader(io.StringIO(text))]
    required = {"chapter", "file_path", "basename", "module_name", "classification"}
    if not rows or not required.issubset(rows[0]):
        raise CatalogError(f"MAT manifest lacks required columns: {sorted(required)}")
    paths = [str(row.get("file_path", "")).replace("\\", "/") for row in rows]
    names = [str(row.get("module_name", "")) for row in rows]
    basenames = [str(row.get("basename", "")).lower() for row in rows]
    for label, values in (("path", paths), ("module name", names), ("basename", basenames)):
        if len(values) != len(set(values)):
            raise CatalogError(f"MAT manifest contains duplicate {label} values.")
        if any(not value for value in values):
            raise CatalogError(f"MAT manifest contains an empty {label}.")
    return rows, _sha256_bytes(manifest_bytes)


def _families(
    plan_tasks: Sequence[_PlanTask],
    raw_overrides: Iterable[Mapping[str, Any]],
) -> tuple[tuple[CatalogFamily, ...], dict[str, str]]:
    task_ids = {item.task_id for item in plan_tasks}
    member_to_family: dict[str, str] = {}
    families: dict[str, CatalogFamily] = {}
    for raw in raw_overrides:
        family_id = _canonical_task_id(raw.get("family_id", ""))
        members = tuple(_canonical_task_id(item) for item in raw.get("members", []))
        if not family_id or len(members) < 2 or len(set(members)) != len(members):
            raise CatalogError(f"Invalid family override: {raw!r}")
        missing = sorted(set(members) - task_ids)
        if missing:
            raise CatalogError(f"Family {family_id} contains unknown tasks: {missing}")
        overlap = sorted(set(members) & set(member_to_family))
        if overlap:
            raise CatalogError(f"Tasks occur in multiple family overrides: {overlap}")
        family = CatalogFamily(
            family_id=family_id,
            book_label=str(raw.get("book_label", "") or family_id),
            family_kind=str(raw.get("family_kind", "") or "book_label_group"),
            count_policy=str(raw.get("count_policy", "") or "count_once"),
            members=members,
        )
        families[family_id] = family
        member_to_family.update({member: family_id for member in members})
    for task_id in sorted(task_ids - set(member_to_family)):
        families[task_id] = CatalogFamily(
            family_id=task_id,
            book_label=task_id,
            family_kind="singleton",
            count_policy="count_once",
            members=(task_id,),
        )
        member_to_family[task_id] = task_id
    return tuple(families[key] for key in sorted(families)), member_to_family


def _owned_support_owner(stem: str, task_ids: set[str]) -> str:
    # Do not run a module basename through canonicalize_block_id here.  That
    # helper deliberately projects derived names such as ``thm_6_7_helper``
    # back to ``thm_6_7``; catalog construction must first distinguish a real
    # primary basename from a support basename.
    canonical_stem = str(stem).strip().lower()
    candidates = [task_id for task_id in task_ids if canonical_stem.startswith(f"{task_id}_")]
    if not candidates:
        raise CatalogError(f"Owned-support module {stem!r} has no formal task owner.")
    longest = max(len(item) for item in candidates)
    winners = sorted(item for item in candidates if len(item) == longest)
    if len(winners) != 1:
        raise CatalogError(f"Owned-support module {stem!r} has ambiguous owners: {winners}")
    return winners[0]


def build_catalog(
    *,
    catalog_name: str,
    toy_commit: str,
    mat_commit: str,
    plan_documents: Mapping[str, bytes],
    manifest_bytes: bytes,
    family_overrides: Iterable[Mapping[str, Any]],
    restored_task_ids: Iterable[str],
    legacy_cohort_id: str,
    expected_counts: Mapping[str, int] | None = None,
    policy_sha256: str = "",
    mat_tree_paths: Iterable[str] | None = None,
) -> TaskCatalog:
    plan_tasks, plan_set_sha256 = _plan_tasks(plan_documents)
    rows, manifest_sha256 = _manifest_rows(manifest_bytes)
    formal_ids = {item.task_id for item in plan_tasks}
    restored = tuple(sorted({_canonical_task_id(item) for item in restored_task_ids}))
    if not set(restored).issubset(formal_ids):
        raise CatalogError("Restored-task evidence contains ids absent from the formal plans.")

    by_task: dict[str, dict[str, str]] = {}
    for row in rows:
        task_id = str(row.get("basename", "")).strip().lower()
        if task_id not in formal_ids:
            continue
        if task_id in by_task:
            raise CatalogError(f"Formal task {task_id} maps to multiple MAT modules.")
        by_task[task_id] = row
    missing_primary = sorted(formal_ids - set(by_task))
    if missing_primary:
        raise CatalogError(f"Formal tasks lack MAT primary modules: {missing_primary}")

    families, member_to_family = _families(plan_tasks, family_overrides)
    modules: list[CatalogModule] = []
    legacy_roots: list[str] = []
    role_migrations: list[str] = []
    for row in rows:
        path = str(row.get("file_path", "")).replace("\\", "/")
        basename = str(row.get("basename", ""))
        task_id = basename.strip().lower()
        legacy_role = str(row.get("classification", ""))
        raw_chapter = str(row.get("chapter", "") or "")
        chapter = int(raw_chapter) if raw_chapter.isdigit() else None
        if task_id in formal_ids:
            role = "primary"
            owner = task_id
            if legacy_role == LEGACY_TASK_ROLE:
                legacy_roots.append(task_id)
            elif legacy_role == LEGACY_OWNED_ROLE:
                role_migrations.append(task_id)
            else:
                raise CatalogError(
                    f"Formal task module {path} has unsupported legacy role {legacy_role!r}."
                )
        elif legacy_role == LEGACY_OWNED_ROLE:
            role = "owned_support"
            owner = _owned_support_owner(basename, formal_ids)
        elif legacy_role == LEGACY_SHARED_ROLE:
            role = "shared"
            owner = ""
        else:
            raise CatalogError(f"Unclassified MAT module {path}: legacy role {legacy_role!r}")
        modules.append(
            CatalogModule(
                path=path,
                basename=basename,
                module_name=str(row.get("module_name", "")),
                module_role=role,
                owner_task_id=owner,
                legacy_manifest_role=legacy_role,
                chapter=chapter,
            )
        )

    role_migrations_tuple = tuple(sorted(role_migrations))
    if role_migrations_tuple != restored:
        missing = sorted(set(restored) - set(role_migrations_tuple))
        extra = sorted(set(role_migrations_tuple) - set(restored))
        raise CatalogError(
            "Legacy support-to-primary migrations do not equal the archive-restored task set: "
            f"missing={missing}, extra={extra}"
        )

    if mat_tree_paths is not None:
        manifest_paths = {item.path for item in modules}
        tree_paths = {str(item).replace("\\", "/") for item in mat_tree_paths if str(item).endswith(".lean")}
        if manifest_paths != tree_paths:
            raise CatalogError(
                "Pinned MAT manifest and Lean tree differ: "
                f"manifest_only={sorted(manifest_paths - tree_paths)}, "
                f"tree_only={sorted(tree_paths - manifest_paths)}"
            )

    task_rows: list[CatalogTask] = []
    for raw in plan_tasks:
        primary = by_task[raw.task_id]
        legacy_role = str(primary.get("classification", ""))
        task_rows.append(
            CatalogTask(
                task_id=raw.task_id,
                family_id=member_to_family[raw.task_id],
                chapter=int(extract_chapter(raw.task_id) or 0),
                task_kind=raw.task_kind,
                source_plan=raw.source_plan,
                source_plan_path=raw.source_plan_path,
                source_hash=raw.source_hash,
                primary_path=str(primary.get("file_path", "")).replace("\\", "/"),
                legacy_manifest_role=legacy_role,
                lifecycle_state=(
                    "restored_then_stale_manifest_role"
                    if raw.task_id in set(role_migrations_tuple)
                    else "formal_task"
                ),
            )
        )

    stable = {
        "schema_version": CATALOG_SCHEMA_VERSION,
        "catalog_name": catalog_name,
        "toy_commit": toy_commit,
        "mat_commit": mat_commit,
        "manifest_sha256": manifest_sha256,
        "plan_set_sha256": plan_set_sha256,
        "policy_sha256": policy_sha256,
        "tasks": [item.as_dict() for item in sorted(task_rows, key=lambda item: item.task_id)],
        "families": [item.as_dict() for item in families],
        "modules": [item.as_dict() for item in sorted(modules, key=lambda item: item.path.lower())],
        "cohorts": {legacy_cohort_id: sorted(legacy_roots)},
        "restored_task_ids": list(restored),
        "role_migrations": list(role_migrations_tuple),
    }
    catalog = TaskCatalog(
        catalog_id=_sha256_json(stable),
        catalog_name=catalog_name,
        toy_commit=toy_commit,
        mat_commit=mat_commit,
        manifest_sha256=manifest_sha256,
        plan_set_sha256=plan_set_sha256,
        policy_sha256=policy_sha256,
        tasks=tuple(sorted(task_rows, key=lambda item: item.task_id)),
        families=families,
        modules=tuple(sorted(modules, key=lambda item: item.path.lower())),
        cohorts={legacy_cohort_id: tuple(sorted(legacy_roots))},
        restored_task_ids=restored,
        role_migrations=role_migrations_tuple,
    )
    if expected_counts is not None:
        actual = catalog.counts()
        mismatches = {
            key: {"expected": int(value), "actual": actual.get(key)}
            for key, value in expected_counts.items()
            if actual.get(key) != int(value)
        }
        if mismatches:
            raise CatalogError(f"Catalog count invariants failed: {mismatches}")
    return catalog


def build_cordis_catalog(
    *,
    catalog_name: str,
    cordis_commit: str,
    plan_documents: Mapping[str, bytes],
    module_documents: Mapping[str, bytes],
    task_module_map: Mapping[str, str],
    family_overrides: Iterable[Mapping[str, Any]] = (),
    expected_counts: Mapping[str, int] | None = None,
    policy_sha256: str = "",
) -> TaskCatalog:
    """Cordis-profile catalog constructor.

    Semantic differences from the MAT ``build_catalog`` (kept deliberate):
    paper-continuous task ids (`def_1`, `thm_4`, ...), several tasks may share
    one primary module (subject bundle = the whole module file), and the
    evidence pins are the paper PDF/extracted-text hashes plus the Cordis
    commit instead of the MAT manifest. Count invariants stay fail-closed.
    """

    plan_tasks, plan_set_sha256 = _plan_tasks(plan_documents, CORDIS_PROFILE)
    formal_ids = {item.task_id for item in plan_tasks}

    module_paths = sorted(str(path).replace("\\", "/") for path in module_documents)
    known_modules = set(module_paths)
    task_module_paths: dict[str, tuple[str, ...]] = {}
    for task_id in sorted(formal_ids):
        mapped = str(task_module_map.get(task_id, "")).replace("\\", "/")
        if not mapped:
            raise CatalogError(f"Cordis task {task_id} has no primary module mapping.")
        if mapped not in known_modules:
            raise CatalogError(
                f"Cordis task {task_id} maps to unknown module {mapped!r}."
            )
        task_module_paths[task_id] = (mapped,)
    unmapped = sorted(set(task_module_map) - formal_ids)
    if unmapped:
        raise CatalogError(f"Cordis module map references unknown tasks: {unmapped}")
    referenced_modules = {path for paths in task_module_paths.values() for path in paths}
    unreferenced = sorted(set(module_paths) - referenced_modules)
    if unreferenced:
        raise CatalogError(f"Cordis modules are not referenced by any task: {unreferenced}")

    families, member_to_family = _families(plan_tasks, family_overrides)
    modules = tuple(
        CatalogModule(
            path=path,
            basename=Path(path).stem,
            module_name=path[: -len(".lean")].replace("/", "."),
            module_role="primary",
            owner_task_id="",
            legacy_manifest_role="cordis_module",
            chapter=None,
        )
        for path in module_paths
    )
    module_hash_payload = [
        {"path": path, "sha256": _sha256_bytes(module_documents[path])} for path in module_paths
    ]

    task_rows = tuple(
        CatalogTask(
            task_id=raw.task_id,
            family_id=member_to_family[raw.task_id],
            chapter=0,
            task_kind=raw.task_kind,
            source_plan=raw.source_plan,
            source_plan_path=raw.source_plan_path,
            source_hash=raw.source_hash,
            primary_path=task_module_paths[raw.task_id][0],
            legacy_manifest_role="cordis_module",
            lifecycle_state="formal_task",
        )
        for raw in plan_tasks
    )
    stable: dict[str, Any] = {
        "schema_version": CATALOG_SCHEMA_VERSION,
        "catalog_name": catalog_name,
        "toy_commit": cordis_commit,
        "mat_commit": "",
        "manifest_sha256": _sha256_json(module_hash_payload),
        "plan_set_sha256": plan_set_sha256,
        "policy_sha256": policy_sha256,
        "tasks": [item.as_dict() for item in sorted(task_rows, key=lambda item: item.task_id)],
        "families": [item.as_dict() for item in families],
        "modules": [item.as_dict() for item in modules],
        "cohorts": {"cordis_paper_review_roots": []},
        "restored_task_ids": [],
        "role_migrations": [],
        "task_module_paths": {key: list(value) for key, value in sorted(task_module_paths.items())},
    }
    catalog = TaskCatalog(
        catalog_id=_sha256_json(stable),
        catalog_name=catalog_name,
        toy_commit=cordis_commit,
        mat_commit="",
        manifest_sha256=str(stable["manifest_sha256"]),
        plan_set_sha256=plan_set_sha256,
        policy_sha256=policy_sha256,
        tasks=tuple(sorted(task_rows, key=lambda item: item.task_id)),
        families=families,
        modules=modules,
        cohorts={"cordis_paper_review_roots": ()},
        restored_task_ids=(),
        role_migrations=(),
        task_module_paths=task_module_paths,
    )
    if expected_counts is not None:
        actual = catalog.counts()
        mismatches = {
            key: {"expected": int(value), "actual": actual.get(key)}
            for key, value in expected_counts.items()
            if actual.get(key) != int(value)
        }
        if mismatches:
            raise CatalogError(f"Catalog count invariants failed: {mismatches}")
    return catalog


def _load_cordis_catalog(
    *,
    workspace_root: Path,
    runtime_root: Path,
    policy_path: Path,
    policy: Mapping[str, Any],
    policy_bytes: bytes,
) -> TaskCatalog:
    cordis_source = policy.get("cordis_source")
    paper_source = policy.get("paper_source")
    task_module_map = policy.get("task_module_map")
    if not all(isinstance(item, Mapping) for item in (cordis_source, paper_source)) or not isinstance(
        task_module_map, Mapping
    ):
        raise CatalogError(f"Cordis catalog policy is missing a required mapping: {policy_path}")

    cordis_commit = str(cordis_source.get("commit", ""))
    if not re.fullmatch(r"[0-9a-f]{40}", cordis_commit):
        raise CatalogError("Cordis catalog policy does not pin a full commit SHA-1.")
    plans_prefix = str(cordis_source.get("plans_prefix", "plans")).strip("/")
    modules_prefix = str(cordis_source.get("modules_prefix", "Cordis/Foundations")).strip("/")

    pdf_path = workspace_root / str(paper_source.get("pdf_workspace_relative_path", "paper.pdf"))
    text_path = workspace_root / str(
        paper_source.get("extracted_text_workspace_relative_path", "")
    )
    source_pins = {
        "paper_pdf_path": str(pdf_path),
        "paper_pdf_sha256": str(paper_source.get("pdf_sha256", "")),
        "extracted_text_path": str(text_path),
        "extracted_text_sha256": str(paper_source.get("extracted_text_sha256", "")),
        "cordis_commit": cordis_commit,
    }
    try:
        pdf_hash = _sha256_bytes(pdf_path.read_bytes())
        text_hash = _sha256_bytes(text_path.read_bytes())
    except OSError as exc:
        raise CatalogError(f"Unable to read pinned Cordis paper sources: {exc}") from exc
    if pdf_hash != source_pins["paper_pdf_sha256"]:
        raise CatalogError(
            f"Pinned Cordis paper.pdf hash mismatch: expected {source_pins['paper_pdf_sha256']}, got {pdf_hash}"
        )
    if text_hash != source_pins["extracted_text_sha256"]:
        raise CatalogError(
            f"Pinned Cordis extracted-text hash mismatch: expected {source_pins['extracted_text_sha256']}, got {text_hash}"
        )

    plan_paths = [
        line.strip()
        for line in _git_text(
            runtime_root, "ls-tree", "-r", "--name-only", cordis_commit, "--", plans_prefix
        ).splitlines()
        if line.strip().endswith("_plan.json")
    ]
    plan_documents = {
        path: _git_bytes(runtime_root, "show", f"{cordis_commit}:{path}") for path in sorted(plan_paths)
    }
    module_paths = [
        line.strip().replace("\\", "/")
        for line in _git_text(
            runtime_root, "ls-tree", "-r", "--name-only", cordis_commit, "--", modules_prefix
        ).splitlines()
        if line.strip().endswith(".lean")
    ]
    module_documents = {
        path: _git_bytes(runtime_root, "show", f"{cordis_commit}:{path}") for path in module_paths
    }

    overrides = policy.get("family_overrides")
    expected_counts = policy.get("expected_counts")
    if not isinstance(overrides, list) or not isinstance(expected_counts, Mapping):
        raise CatalogError("Cordis catalog policy lacks family overrides or count invariants.")
    return build_cordis_catalog(
        catalog_name=str(policy.get("catalog_name", "") or "cordis"),
        cordis_commit=cordis_commit,
        plan_documents=plan_documents,
        module_documents=module_documents,
        task_module_map={str(key): str(value) for key, value in task_module_map.items()},
        family_overrides=[item for item in overrides if isinstance(item, Mapping)],
        expected_counts={str(key): int(value) for key, value in expected_counts.items()},
        policy_sha256=_sha256_bytes(policy_bytes),
    )


def load_catalog(
    *,
    workspace_root: Path,
    runtime_root: Path,
    mat_root: Path | None = None,
    policy_path: Path | None = None,
) -> TaskCatalog:
    workspace_root = workspace_root.resolve()
    runtime_root = runtime_root.resolve()
    mat_root = (mat_root or workspace_root / "MAT3280-formalization-output").resolve()
    policy_path = (policy_path or runtime_root / DEFAULT_POLICY_PATH).resolve()
    try:
        policy_bytes = policy_path.read_bytes()
        policy = json.loads(policy_bytes.decode("utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise CatalogError(f"Unable to load catalog policy {policy_path}: {exc}") from exc
    if not isinstance(policy, Mapping):
        raise CatalogError(f"Unsupported catalog policy: {policy_path}")
    schema_version = str(policy.get("schema_version", ""))
    source_kind = str(policy.get("source_kind", "") or "mat_manifest")
    if schema_version == CORDIS_POLICY_SCHEMA_VERSION or source_kind == "cordis_modules":
        if schema_version != CORDIS_POLICY_SCHEMA_VERSION or source_kind != "cordis_modules":
            raise CatalogError(
                f"Inconsistent Cordis catalog policy schema/source_kind: {policy_path}"
            )
        return _load_cordis_catalog(
            workspace_root=workspace_root,
            runtime_root=runtime_root,
            policy_path=policy_path,
            policy=policy,
            policy_bytes=policy_bytes,
        )
    if schema_version != POLICY_SCHEMA_VERSION or source_kind != "mat_manifest":
        raise CatalogError(f"Unsupported catalog policy: {policy_path}")

    toy_source = policy.get("toy_source")
    mat_source = policy.get("mat_source")
    restored_source = policy.get("restored_task_evidence")
    cohort = policy.get("legacy_review_root_cohort")
    if not all(isinstance(item, Mapping) for item in (toy_source, mat_source, restored_source, cohort)):
        raise CatalogError("Catalog policy is missing a required source mapping.")
    toy_commit = str(toy_source.get("commit", ""))
    mat_commit = str(mat_source.get("commit", ""))
    plans_prefix = str(toy_source.get("plans_prefix", "plans")).strip("/")
    manifest_path = str(mat_source.get("manifest_path", "manifest_by_chapter.csv"))
    plan_paths = [
        line.strip()
        for line in _git_text(runtime_root, "ls-tree", "-r", "--name-only", toy_commit, "--", plans_prefix).splitlines()
        if line.strip().endswith("_plan.json")
    ]
    plan_documents = {
        path: _git_bytes(runtime_root, "show", f"{toy_commit}:{path}") for path in sorted(plan_paths)
    }
    manifest_bytes = _git_bytes(mat_root, "show", f"{mat_commit}:{manifest_path}")
    manifest_hash = _sha256_bytes(manifest_bytes)
    expected_manifest_hash = str(mat_source.get("manifest_sha256", ""))
    if manifest_hash != expected_manifest_hash:
        raise CatalogError(
            f"Pinned MAT manifest hash mismatch: expected {expected_manifest_hash}, got {manifest_hash}"
        )
    tree_paths = [
        line.strip()
        for line in _git_text(mat_root, "ls-tree", "-r", "--name-only", mat_commit).splitlines()
        if line.strip().endswith(".lean")
    ]

    evidence_path = workspace_root / str(restored_source.get("workspace_relative_path", ""))
    try:
        restored_bytes = evidence_path.read_bytes()
        restored_payload = json.loads(restored_bytes.decode("utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise CatalogError(f"Unable to load restored-task evidence {evidence_path}: {exc}") from exc
    expected_restored_hash = str(restored_source.get("sha256", ""))
    if _sha256_bytes(restored_bytes) != expected_restored_hash:
        raise CatalogError(f"Restored-task evidence hash mismatch: {evidence_path}")
    restored_ids = restored_payload.get("restored_task_ids") if isinstance(restored_payload, Mapping) else None
    if not isinstance(restored_ids, list):
        raise CatalogError("Restored-task evidence lacks restored_task_ids.")

    overrides = policy.get("family_overrides")
    expected_counts = policy.get("expected_counts")
    if not isinstance(overrides, list) or not isinstance(expected_counts, Mapping):
        raise CatalogError("Catalog policy lacks family overrides or count invariants.")
    return build_catalog(
        catalog_name=str(policy.get("catalog_name", "") or "toyapollo"),
        toy_commit=toy_commit,
        mat_commit=mat_commit,
        plan_documents=plan_documents,
        manifest_bytes=manifest_bytes,
        family_overrides=[item for item in overrides if isinstance(item, Mapping)],
        restored_task_ids=[str(item) for item in restored_ids],
        legacy_cohort_id=str(cohort.get("cohort_id", "") or "legacy_mat_review_roots"),
        expected_counts={str(key): int(value) for key, value in expected_counts.items()},
        policy_sha256=_sha256_bytes(policy_bytes),
        mat_tree_paths=tree_paths,
    )


def validate_catalog(catalog: TaskCatalog) -> dict[str, Any]:
    identity_payload = {
        "schema_version": catalog.schema_version,
        "catalog_name": catalog.catalog_name,
        "toy_commit": catalog.toy_commit,
        "mat_commit": catalog.mat_commit,
        "manifest_sha256": catalog.manifest_sha256,
        "plan_set_sha256": catalog.plan_set_sha256,
        "policy_sha256": catalog.policy_sha256,
        "tasks": [item.as_dict() for item in catalog.tasks],
        "families": [item.as_dict() for item in catalog.families],
        "modules": [item.as_dict() for item in catalog.modules],
        "cohorts": {key: list(value) for key, value in sorted(catalog.cohorts.items())},
        "restored_task_ids": list(catalog.restored_task_ids),
        "role_migrations": list(catalog.role_migrations),
    }
    if catalog.task_module_paths:
        identity_payload["task_module_paths"] = {
            key: list(value) for key, value in sorted(catalog.task_module_paths.items())
        }
    identity_sha256 = _sha256_json(identity_payload)
    tasks = {item.task_id for item in catalog.tasks}
    family_members = [member for family in catalog.families for member in family.members]
    primary_owners = [item.owner_task_id for item in catalog.modules if item.module_role == "primary"]
    owned_support = [item for item in catalog.modules if item.module_role == "owned_support"]
    errors: list[str] = []
    if catalog.catalog_id != identity_sha256:
        errors.append("catalog_id does not match the immutable catalog payload")
    if set(family_members) != tasks or len(family_members) != len(set(family_members)):
        errors.append("family membership is not a one-to-one partition of tasks")
    if catalog.task_module_paths:
        # Cordis multi-homing: every task maps to at least one existing primary
        # module; modules may be shared across tasks by design.
        module_index = {item.path: item for item in catalog.modules}
        for task_id, mapped in sorted(catalog.task_module_paths.items()):
            if not mapped:
                errors.append(f"task {task_id} has an empty primary module mapping")
                continue
            for path in mapped:
                module = module_index.get(path)
                if module is None:
                    errors.append(f"task {task_id} maps to unknown module {path}")
                elif module.module_role != "primary":
                    errors.append(f"task {task_id} maps to non-primary module {path}")
        if set(catalog.task_module_paths) != tasks:
            errors.append("task module mapping does not cover the task set exactly")
    else:
        if set(primary_owners) != tasks or len(primary_owners) != len(set(primary_owners)):
            errors.append("primary module ownership is not one-to-one with tasks")
    if any(not item.owner_task_id or item.owner_task_id not in tasks for item in owned_support):
        errors.append("owned-support module has no valid task owner")
    if any(item.owner_task_id for item in catalog.modules if item.module_role == "shared"):
        errors.append("shared module unexpectedly has a single owner")
    return {
        "valid": not errors,
        "catalog_id": catalog.catalog_id,
        "counts": catalog.counts(),
        "errors": errors,
        "identity_payload_sha256": identity_sha256,
        "stable_payload_sha256": _sha256_json(catalog.stable_payload()),
    }


def task_ids(catalog: TaskCatalog, *, cohort_id: str | None = None) -> tuple[str, ...]:
    return catalog.task_ids(cohort_id=cohort_id)


def family_for_task(catalog: TaskCatalog, task_id: str) -> CatalogFamily:
    return catalog.family_for_task(task_id)


def owned_paths(catalog: TaskCatalog, task_id: str, *, include_primary: bool = True) -> tuple[str, ...]:
    return catalog.owned_paths(task_id, include_primary=include_primary)


def task_for_path(catalog: TaskCatalog, path: str) -> str | None:
    return catalog.task_for_path(path)
