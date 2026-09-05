"""Emit immutable current-MAT exact-build receipts in bounded batches.

This module deliberately has no ledger dependency.  It inventories the pinned
catalog and MAT tree once, runs one combined ``lake build`` per bounded batch,
and writes one canonical ``mat.catalog.exact-build.v1`` receipt per task.
"""

from __future__ import annotations

import json
import re
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

from formalization_engine.block_id_naming import canonicalize_block_id, is_canonical_block_id

from .state_reconcile import discover_catalog_git_subjects
from .state_store import SubjectBundle, filesystem_path
from .state_transformation_receipt import (
    FORBIDDEN_PATTERNS,
    _command_text,
    _forbidden_findings,
    _json_bytes,
    _run,
    _sha256_bytes,
    _utc_now,
    _write_new,
)
from .task_catalog import load_catalog


EXACT_BUILD_SCHEMA = "mat.catalog.exact-build.v1"
_HEX40 = re.compile(r"^[0-9a-f]{40}$")


class ExactBuildBatchError(RuntimeError):
    """Raised when exact-build evidence cannot be emitted fail-closed."""


@dataclass(frozen=True)
class ExactBuildSelection:
    task_ids: tuple[str, ...]
    expected_commits: tuple[str, ...] = ()
    expected_task_modules: tuple[tuple[str, tuple[str, ...]], ...] = ()


def _task_file_entries(path: Path) -> list[str]:
    try:
        raw = path.expanduser().read_text(encoding="utf-8")
    except OSError as exc:
        raise ExactBuildBatchError(f"Unable to read task list {path}: {exc}") from exc
    stripped = raw.strip()
    if stripped.startswith("["):
        try:
            payload = json.loads(stripped)
        except json.JSONDecodeError as exc:
            raise ExactBuildBatchError(f"Task list JSON is invalid: {path}: {exc}") from exc
        if not isinstance(payload, list):
            raise ExactBuildBatchError(f"Task list JSON must be an array: {path}")
        return [str(item) for item in payload]
    return [
        item.strip()
        for line in raw.splitlines()
        if not line.lstrip().startswith("#")
        for item in line.split(",")
        if item.strip()
    ]


def _manifest_modules(
    entry: Mapping[str, Any], *, key: str, path: Path, index: int
) -> tuple[str, ...]:
    raw = entry.get(key)
    if not isinstance(raw, list) or not raw or any(
        not isinstance(module, str) or not module.strip() for module in raw
    ):
        raise ExactBuildBatchError(
            f"Action manifest entry {index} has invalid {key}: {path}"
        )
    modules = tuple(sorted(set(raw)))
    if len(modules) != len(raw):
        raise ExactBuildBatchError(
            f"Action manifest entry {index} has duplicate modules: {path}"
        )
    return modules


def _manifest_task_entries(
    entries: Any, *, modules_key: str, path: Path
) -> tuple[list[str], dict[str, tuple[str, ...]], dict[str, str]]:
    if not isinstance(entries, list) or not entries:
        raise ExactBuildBatchError(f"Action manifest task entries are missing: {path}")
    tasks: list[str] = []
    modules: dict[str, tuple[str, ...]] = {}
    primaries: dict[str, str] = {}
    for index, entry in enumerate(entries):
        if not isinstance(entry, Mapping):
            raise ExactBuildBatchError(
                f"Action manifest task entry {index} is malformed: {path}"
            )
        task_id = canonicalize_block_id(str(entry.get("task_id", "") or ""))
        if not task_id or not is_canonical_block_id(task_id) or task_id in modules:
            raise ExactBuildBatchError(
                f"Action manifest task entry {index} has invalid/duplicate task_id: {path}"
            )
        owned = _manifest_modules(entry, key=modules_key, path=path, index=index)
        primary = str(entry.get("primary_build_module", "") or "").strip()
        if primary and primary not in owned:
            raise ExactBuildBatchError(
                f"Action manifest primary module is not owned by {task_id}: {path}"
            )
        tasks.append(task_id)
        modules[task_id] = owned
        if primary:
            primaries[task_id] = primary
    return tasks, modules, primaries


def _declared_count(payload: Mapping[str, Any], key: str, actual: int, path: Path) -> None:
    counts = payload.get("counts")
    raw = counts.get(key) if isinstance(counts, Mapping) else None
    if raw is None:
        raise ExactBuildBatchError(f"Action manifest lacks counts.{key}: {path}")
    try:
        count = int(raw)
    except (TypeError, ValueError) as exc:
        raise ExactBuildBatchError(
            f"Action manifest count counts.{key} is invalid: {path}"
        ) from exc
    if count != actual:
        raise ExactBuildBatchError(
            f"Action manifest counts.{key}={count} does not match {actual}: {path}"
        )


def _action_manifest_entries(
    path: Path,
) -> tuple[list[str], str, dict[str, tuple[str, ...]]]:
    try:
        payload = json.loads(path.expanduser().read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ExactBuildBatchError(f"Unable to read action manifest {path}: {exc}") from exc
    if not isinstance(payload, Mapping):
        raise ExactBuildBatchError(f"Action manifest must be a JSON object: {path}")
    schema = str(payload.get("schema", "") or "")
    if schema == "toy-apollo.resolved-invalidation-action-manifest.v1":
        tasks, modules, primaries = _manifest_task_entries(
            payload.get("unique_exact_builds"),
            modules_key="owned_modules",
            path=path,
        )
        _declared_count(payload, "unique_exact_build_tasks", len(tasks), path)
        if set(primaries) != set(tasks):
            raise ExactBuildBatchError(
                f"Action manifest lacks primary modules for some tasks: {path}"
            )
        _declared_count(
            payload,
            "unique_owned_modules",
            sum(len(values) for values in modules.values()),
            path,
        )
        _declared_count(payload, "unique_primary_build_modules", len(primaries), path)
        commit = str(payload.get("mat_commit", "") or "").strip()
    elif schema == "toy-apollo.ch3-4-boundary-delta-exact-build-action-manifest.v1":
        tasks, modules, primaries = _manifest_task_entries(
            payload.get("unique_exact_build_tasks"),
            modules_key="owned_modules",
            path=path,
        )
        _declared_count(payload, "unique_exact_build_tasks", len(tasks), path)
        if set(primaries) != set(tasks):
            raise ExactBuildBatchError(
                f"Action manifest lacks primary modules for some tasks: {path}"
            )
        actions = payload.get("unique_task_module_actions")
        if not isinstance(actions, list):
            raise ExactBuildBatchError(
                f"Action manifest lacks unique_task_module_actions: {path}"
            )
        action_modules: dict[str, list[str]] = {task_id: [] for task_id in tasks}
        for index, action in enumerate(actions):
            if not isinstance(action, Mapping):
                raise ExactBuildBatchError(
                    f"Action manifest module action {index} is malformed: {path}"
                )
            task_id = canonicalize_block_id(str(action.get("task_id", "") or ""))
            module = str(action.get("module", "") or "").strip()
            if task_id not in action_modules or not module:
                raise ExactBuildBatchError(
                    f"Action manifest module action {index} is invalid: {path}"
                )
            expected_primary = module == primaries.get(task_id)
            if action.get("is_primary") is not expected_primary:
                raise ExactBuildBatchError(
                    f"Action manifest module action primary flag is invalid: {path}"
                )
            action_modules[task_id].append(module)
        normalized_actions = {
            task_id: tuple(sorted(values)) for task_id, values in action_modules.items()
        }
        if normalized_actions != modules:
            raise ExactBuildBatchError(
                f"Action manifest task/module actions disagree with owned modules: {path}"
            )
        _declared_count(payload, "unique_owned_modules", len(actions), path)
        commit = str(payload.get("mat_commit", "") or "").strip()
    elif schema == "ch9-14.boundary-delta-exact-build-action-manifest.v1":
        tasks, modules, _primaries = _manifest_task_entries(
            payload.get("unique_combined_build_tasks"),
            modules_key="modules",
            path=path,
        )
        _declared_count(payload, "unique_combined_build_tasks", len(tasks), path)
        scope = payload.get("scope")
        commit = str(
            scope.get("target_commit", "") if isinstance(scope, Mapping) else ""
        ).strip()
    else:
        raise ExactBuildBatchError(f"Unsupported action manifest schema {schema!r}: {path}")
    if not _HEX40.fullmatch(commit):
        raise ExactBuildBatchError(
            f"Action manifest lacks its required 40-hex MAT commit: {path}"
        )
    return tasks, commit, modules


def collect_exact_build_selection(
    *,
    tasks: Sequence[str] = (),
    task_files: Sequence[Path] = (),
    action_manifests: Sequence[Path] = (),
) -> ExactBuildSelection:
    """Load task ids from explicit flags, task files, and action manifests."""

    raw_tasks = list(tasks)
    commits: list[str] = []
    expected_modules: dict[str, tuple[str, ...]] = {}
    for path in task_files:
        raw_tasks.extend(_task_file_entries(path))
    for path in action_manifests:
        manifest_tasks, commit, manifest_modules = _action_manifest_entries(path)
        raw_tasks.extend(manifest_tasks)
        commits.append(commit)
        for task_id, modules in manifest_modules.items():
            previous = expected_modules.get(task_id)
            if previous is not None and previous != modules:
                raise ExactBuildBatchError(
                    f"Action manifests disagree on owned modules for {task_id}"
                )
            expected_modules[task_id] = modules
    canonical: list[str] = []
    seen: set[str] = set()
    for raw in raw_tasks:
        task_id = canonicalize_block_id(str(raw))
        if not task_id or not is_canonical_block_id(task_id):
            raise ExactBuildBatchError(f"Invalid task id: {raw!r}")
        if task_id not in seen:
            canonical.append(task_id)
            seen.add(task_id)
    if not canonical:
        raise ExactBuildBatchError(
            "At least one --task, --task-file, or --action-manifest is required"
        )
    return ExactBuildSelection(
        task_ids=tuple(canonical),
        expected_commits=tuple(sorted(set(commits))),
        expected_task_modules=tuple(sorted(expected_modules.items())),
    )


def catalog_owned_build_modules(
    catalog: Any, task_ids: Iterable[str]
) -> tuple[dict[str, str], dict[str, tuple[str, ...]]]:
    wanted = set(task_ids)
    primaries: dict[str, list[str]] = {task_id: [] for task_id in wanted}
    owned: dict[str, list[str]] = {task_id: [] for task_id in wanted}
    for module in catalog.modules:
        if module.owner_task_id not in wanted:
            continue
        if module.module_role in {"primary", "owned_support"}:
            owned[module.owner_task_id].append(module.module_name)
        if module.module_role == "primary":
            primaries[module.owner_task_id].append(module.module_name)
    bad = {
        task_id: modules for task_id, modules in primaries.items() if len(modules) != 1
    }
    if bad:
        raise ExactBuildBatchError(
            "Catalog must provide exactly one primary module per task: " + repr(bad)
        )
    return (
        {task_id: modules[0] for task_id, modules in primaries.items()},
        {task_id: tuple(sorted(modules)) for task_id, modules in owned.items()},
    )


def _subject_identity(subject: SubjectBundle) -> dict[str, Any]:
    return {
        "task_id": subject.task_id,
        "commit": subject.source_commit,
        "subject_id": subject.subject_id,
        "bundle_hash": subject.bundle_hash,
        "primary_hash": subject.primary_hash,
        "primary_path": subject.primary_path,
        "subject_files": subject.manifest(),
    }


def _findings_are_empty(value: Any) -> bool:
    return value == [] or value == {}


def validate_current_exact_build_receipt(
    path: Path,
    *,
    subject: SubjectBundle,
    primary_module: str,
    task_modules: Sequence[str],
    commit: str,
    checkout: Path,
) -> dict[str, Any]:
    """Strictly validate an existing receipt against a freshly inventoried subject."""

    try:
        payload = json.loads(filesystem_path(path).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ExactBuildBatchError(
            f"{subject.task_id}: existing receipt is unreadable: {exc}"
        ) from exc
    identity = _subject_identity(subject)
    focused = payload.get("focused_build") if isinstance(payload, Mapping) else None
    cwd_text = str(focused.get("cwd", "")) if isinstance(focused, Mapping) else ""
    if (
        not isinstance(payload, Mapping)
        or payload.get("schema") != EXACT_BUILD_SCHEMA
        or any(payload.get(key) != value for key, value in identity.items())
        or not str(payload.get("campaign_id", "") or "").strip()
        or not str(payload.get("created_at", "") or "").strip()
        or payload.get("success") is not True
        or payload.get("exit_code") != 0
    ):
        raise ExactBuildBatchError(
            f"{subject.task_id}: existing receipt identity or success state mismatches current MAT"
        )
    if payload.get("commit") != commit:
        raise ExactBuildBatchError(f"{subject.task_id}: existing receipt commit mismatch")
    command = focused.get("command") if isinstance(focused, Mapping) else None
    membership = (
        focused.get("task_modules_in_combined_command")
        if isinstance(focused, Mapping)
        else None
    )
    if (
        not isinstance(focused, Mapping)
        or focused.get("exit_code") != 0
        or focused.get("task_module") != primary_module
        or focused.get("task_module_in_combined_command") is not True
        or focused.get("task_modules") != list(task_modules)
        or membership != {module: True for module in task_modules}
        or not isinstance(command, list)
        or command[:2] != ["lake", "build"]
        or any(module not in command[2:] for module in task_modules)
        or not isinstance(focused.get("batch_index"), int)
        or focused.get("batch_index", 0) <= 0
        or not isinstance(focused.get("batch_size"), int)
        or focused.get("batch_size", 0) <= 0
        or not isinstance(focused.get("duration_seconds"), (int, float))
        or not isinstance(focused.get("stdout"), str)
        or not isinstance(focused.get("stderr"), str)
        or not Path(cwd_text).is_absolute()
        or Path(cwd_text).resolve() != checkout.resolve()
    ):
        raise ExactBuildBatchError(f"{subject.task_id}: existing combined build binding mismatch")
    forbidden = payload.get("forbidden_token_scan")
    if (
        not isinstance(forbidden, Mapping)
        or forbidden.get("exit_code") != 0
        or forbidden.get("findings") != {}
        or forbidden.get("tokens") != sorted(FORBIDDEN_PATTERNS)
    ):
        raise ExactBuildBatchError(f"{subject.task_id}: existing forbidden scan is not clean")
    tree = payload.get("lean_tree_equivalence")
    if (
        not isinstance(tree, Mapping)
        or tree.get("build_commit") != commit
        or tree.get("target_commit") != commit
        or tree.get("changed_lean_files") != []
        or tree.get("build_checkout_clean") is not True
    ):
        raise ExactBuildBatchError(f"{subject.task_id}: existing clean-tree binding mismatch")
    return dict(payload)


def _existing_receipt(
    directory: Path,
    *,
    subject: SubjectBundle,
    primary_module: str,
    task_modules: Sequence[str],
    commit: str,
    checkout: Path,
) -> dict[str, Any] | None:
    receipt = directory / "exact_mat_build_receipt_v1.json"
    if not directory.exists():
        return None
    if not directory.is_dir() or not receipt.is_file():
        raise ExactBuildBatchError(
            f"{subject.task_id}: immutable evidence is partial; refusing overwrite"
        )
    unexpected = sorted(path.name for path in directory.iterdir() if path != receipt)
    if unexpected:
        raise ExactBuildBatchError(
            f"{subject.task_id}: exact-build directory contains unexpected files: {unexpected}"
        )
    payload = validate_current_exact_build_receipt(
        receipt,
        subject=subject,
        primary_module=primary_module,
        task_modules=task_modules,
        commit=commit,
        checkout=checkout,
    )
    return {
        "task_id": subject.task_id,
        "status": "skipped_existing",
        "receipt": str(receipt),
        "receipt_sha256": _sha256_bytes(filesystem_path(receipt).read_bytes()),
        "subject_id": payload["subject_id"],
    }


def _revalidate_exact_tree(mat_repo: Path, checkout: Path, commit: str) -> None:
    if _command_text(mat_repo, "git", "rev-parse", "origin/main") != commit:
        raise ExactBuildBatchError("MAT origin/main changed during exact-build emission")
    if _command_text(checkout, "git", "rev-parse", "HEAD") != commit:
        raise ExactBuildBatchError("Build checkout HEAD changed during exact-build emission")
    if _command_text(checkout, "git", "status", "--porcelain", "--untracked-files=all"):
        raise ExactBuildBatchError("Build checkout became dirty during exact-build emission")


def _chunks(items: Sequence[Any], size: int) -> Iterable[Sequence[Any]]:
    for index in range(0, len(items), size):
        yield items[index : index + size]


def emit_current_exact_builds_batch(
    *,
    workspace_root: Path,
    runtime_root: Path,
    task_ids: Sequence[str],
    checkout: Path,
    output_root: Path,
    batch_size: int = 12,
    timeout: int = 1800,
    campaign_id: str = "current_exact_build_batch",
    skip_existing: bool = True,
    expected_commits: Sequence[str] = (),
    expected_task_modules: Mapping[str, Sequence[str]] | None = None,
) -> dict[str, Any]:
    """Build current MAT tasks in bounded combined batches and emit receipts."""

    if batch_size <= 0:
        raise ExactBuildBatchError("batch_size must be positive")
    if timeout <= 0:
        raise ExactBuildBatchError("timeout must be positive")
    if not campaign_id.strip():
        raise ExactBuildBatchError("campaign_id must be non-empty")
    canonical = list(
        collect_exact_build_selection(tasks=task_ids).task_ids
    )
    workspace = workspace_root.expanduser().resolve()
    runtime = runtime_root.expanduser().resolve()
    build_checkout = checkout.expanduser().resolve()
    output = output_root.expanduser().resolve()
    mat_repo = workspace / "MAT3280-formalization-output"
    if output == build_checkout or output.is_relative_to(build_checkout):
        raise ExactBuildBatchError("output_root must be outside the clean build checkout")
    if output == mat_repo or output.is_relative_to(mat_repo):
        raise ExactBuildBatchError("output_root must be outside the MAT source repository")
    if not (mat_repo / ".git").exists():
        raise ExactBuildBatchError(f"MAT repository is missing: {mat_repo}")
    if not (build_checkout / ".git").exists():
        raise ExactBuildBatchError(f"Build checkout is missing: {build_checkout}")

    catalog = load_catalog(workspace_root=workspace, runtime_root=runtime)
    missing = sorted(set(canonical) - set(catalog.task_ids()))
    if missing:
        raise ExactBuildBatchError(f"Tasks are absent from the active catalog: {missing}")
    expected = sorted(set(str(value) for value in expected_commits if str(value)))
    if any(value != catalog.mat_commit for value in expected):
        raise ExactBuildBatchError(
            "Action manifest commit does not match catalog MAT pin "
            f"{catalog.mat_commit}: {expected}"
        )
    origin_main = _command_text(mat_repo, "git", "rev-parse", "origin/main")
    head = _command_text(build_checkout, "git", "rev-parse", "HEAD")
    dirty = _command_text(
        build_checkout, "git", "status", "--porcelain", "--untracked-files=all"
    )
    if origin_main != catalog.mat_commit or head != catalog.mat_commit:
        raise ExactBuildBatchError(
            "MAT origin/main and clean build checkout must equal the catalog pin: "
            f"origin/main={origin_main} HEAD={head} catalog={catalog.mat_commit}"
        )
    if dirty:
        raise ExactBuildBatchError("Build checkout is not clean")

    subjects = discover_catalog_git_subjects(
        mat_repo,
        ref=catalog.mat_commit,
        catalog=catalog,
        source_repo="mat",
        layout="mat",
        task_ids=canonical,
    )
    absent = sorted(set(canonical) - set(subjects))
    if absent:
        raise ExactBuildBatchError(f"Catalog-pinned MAT subjects are missing: {absent}")
    wrong_commits = sorted(
        task_id
        for task_id in canonical
        if subjects[task_id].source_commit != catalog.mat_commit
    )
    if wrong_commits:
        raise ExactBuildBatchError(
            f"Catalog subject inventory is not pinned to {catalog.mat_commit}: {wrong_commits}"
        )
    primary_modules, owned_modules = catalog_owned_build_modules(catalog, canonical)
    wrong_primary_modules = {
        task_id: {
            "catalog": primary_modules[task_id],
            "subject": subjects[task_id].primary_path.removesuffix(".lean").replace("/", "."),
        }
        for task_id in canonical
        if primary_modules[task_id]
        != subjects[task_id].primary_path.removesuffix(".lean").replace("/", ".")
    }
    if wrong_primary_modules:
        raise ExactBuildBatchError(
            "Catalog primary modules do not match subject primary paths: "
            + repr(wrong_primary_modules)
        )
    wrong_owned_paths = {
        task_id: {
            "catalog": sorted(catalog.owned_paths(task_id)),
            "subject": sorted(item.path for item in subjects[task_id].files),
        }
        for task_id in canonical
        if sorted(catalog.owned_paths(task_id))
        != sorted(item.path for item in subjects[task_id].files)
    }
    if wrong_owned_paths:
        raise ExactBuildBatchError(
            "Catalog owned modules do not match complete subject files: "
            + repr(wrong_owned_paths)
        )
    declared_modules = {
        canonicalize_block_id(task_id): tuple(sorted(modules))
        for task_id, modules in (expected_task_modules or {}).items()
    }
    mismatched_declared_modules = {
        task_id: {
            "manifest": declared_modules[task_id],
            "catalog": owned_modules.get(task_id),
        }
        for task_id in declared_modules
        if task_id not in owned_modules or declared_modules[task_id] != owned_modules[task_id]
    }
    if mismatched_declared_modules:
        raise ExactBuildBatchError(
            "Action manifest owned modules do not match the catalog: "
            + repr(mismatched_declared_modules)
        )

    pending: list[tuple[str, SubjectBundle, str, tuple[str, ...], Path]] = []
    skipped: list[dict[str, Any]] = []
    for task_id in canonical:
        subject = subjects[task_id]
        directory = output / task_id
        existing = _existing_receipt(
            directory,
            subject=subject,
            primary_module=primary_modules[task_id],
            task_modules=owned_modules[task_id],
            commit=catalog.mat_commit,
            checkout=build_checkout,
        )
        if existing is not None:
            if not skip_existing:
                raise ExactBuildBatchError(
                    f"{task_id}: immutable exact-build receipt already exists"
                )
            skipped.append(existing)
        else:
            pending.append(
                (
                    task_id,
                    subject,
                    primary_modules[task_id],
                    owned_modules[task_id],
                    directory,
                )
            )

    emitted: list[dict[str, Any]] = []
    build_commands: list[list[str]] = []
    for batch_index, batch in enumerate(_chunks(pending, batch_size), start=1):
        combined_modules = sorted(
            {module for item in batch for module in item[3]}
        )
        command = ["lake", "build", *combined_modules]
        build_commands.append(command)
        started = time.perf_counter()
        completed = _run(build_checkout, *command, timeout=timeout)
        duration = round(time.perf_counter() - started, 3)
        if completed.returncode != 0:
            raise ExactBuildBatchError(
                f"Combined exact build batch {batch_index} failed with exit code "
                f"{completed.returncode}: {completed.stderr.decode('utf-8', errors='replace')}"
            )
        created_at = _utc_now()
        prepared: list[tuple[Path, bytes, str, str]] = []
        for task_id, subject, primary_module, task_modules, directory in batch:
            subject_payload = {
                "source_commit": subject.source_commit,
                "files": subject.manifest(),
            }
            findings = _forbidden_findings(mat_repo, subject_payload)
            if findings:
                raise ExactBuildBatchError(
                    f"{task_id}: forbidden-token scan found {len(findings)} match(es)"
                )
            receipt = {
                "schema": EXACT_BUILD_SCHEMA,
                "campaign_id": campaign_id,
                **_subject_identity(subject),
                "success": True,
                "exit_code": 0,
                "focused_build": {
                    "command": command,
                    "task_module": primary_module,
                    "task_module_in_combined_command": primary_module in command[2:],
                    "task_modules": list(task_modules),
                    "task_modules_in_combined_command": {
                        module: module in command[2:] for module in task_modules
                    },
                    "batch_index": batch_index,
                    "batch_size": len(batch),
                    "cwd": str(build_checkout),
                    "exit_code": completed.returncode,
                    "duration_seconds": duration,
                    "stdout": completed.stdout.decode("utf-8", errors="replace"),
                    "stderr": completed.stderr.decode("utf-8", errors="replace"),
                },
                "forbidden_token_scan": {
                    "exit_code": 0,
                    "findings": {},
                    "tokens": sorted(FORBIDDEN_PATTERNS),
                },
                "lean_tree_equivalence": {
                    "build_commit": catalog.mat_commit,
                    "target_commit": catalog.mat_commit,
                    "changed_lean_files": [],
                    "build_checkout_clean": True,
                },
                "created_at": created_at,
            }
            receipt_path = directory / "exact_mat_build_receipt_v1.json"
            prepared.append((receipt_path, _json_bytes(receipt), task_id, subject.subject_id))
        _revalidate_exact_tree(mat_repo, build_checkout, catalog.mat_commit)
        raced = [str(path) for path, _payload, _task, _subject in prepared if path.exists()]
        if raced:
            raise ExactBuildBatchError(
                "Immutable exact-build evidence appeared during validation: " + ", ".join(raced)
            )
        for path, payload, task_id, subject_id in prepared:
            _write_new(path, payload)
            emitted.append(
                {
                    "task_id": task_id,
                    "status": "emitted",
                    "receipt": str(path),
                    "receipt_sha256": _sha256_bytes(payload),
                    "subject_id": subject_id,
                }
            )

    tasks = sorted([*skipped, *emitted], key=lambda item: str(item["task_id"]))
    return {
        "status": "all_existing" if not pending else "emitted",
        "catalog_mat_commit": catalog.mat_commit,
        "requested": len(canonical),
        "emitted": len(emitted),
        "skipped_existing": len(skipped),
        "batch_size": batch_size,
        "build_batches": len(build_commands),
        "build_commands": build_commands,
        "tasks": tasks,
    }
