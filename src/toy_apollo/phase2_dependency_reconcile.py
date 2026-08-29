from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from src.block_id_naming import canonicalize_block_id, canonicalize_task_dict

from .core import LedgerDependencyConflictError, LedgerManager
from .phase2_pack_shared.io import sha256_json


RECONCILIATION_SCHEMA_VERSION = "phase2.dependency_reconciliation.v1"


class DependencyReconciliationError(RuntimeError):
    pass


@dataclass(frozen=True)
class Phase1DependencyAuthority:
    task: dict[str, Any]
    dependencies: tuple[str, ...]
    source_plan: str
    source_file: Path
    source_file_sha256: str
    source_task_sha256: str


def _strict_dependency_list(raw: Any, *, field: str, task_id: str) -> list[str]:
    if not isinstance(raw, list):
        raise DependencyReconciliationError(f"{field} for {task_id} must be a JSON/list dependency array.")
    normalized: list[str] = []
    seen: set[str] = set()
    for raw_dependency in raw:
        if not isinstance(raw_dependency, str):
            raise DependencyReconciliationError(f"{field} for {task_id} contains a non-string dependency.")
        dependency = canonicalize_block_id(raw_dependency)
        if not dependency:
            raise DependencyReconciliationError(
                f"{field} for {task_id} contains an empty or invalid dependency: {raw_dependency!r}."
            )
        if dependency == task_id:
            raise DependencyReconciliationError(f"{field} for {task_id} contains a self dependency.")
        if dependency in seen:
            raise DependencyReconciliationError(f"{field} for {task_id} contains duplicate {dependency!r}.")
        seen.add(dependency)
        normalized.append(dependency)
    return normalized


def load_phase1_dependency_authority(task_id: str, plans_dir: Path) -> Phase1DependencyAuthority:
    """Load one unique task entry without applying or re-registering its source unit."""

    canonical_task_id = canonicalize_block_id(task_id)
    if not canonical_task_id:
        raise DependencyReconciliationError("Dependency reconciliation task id is empty or invalid.")
    matches: list[tuple[Path, dict[str, Any]]] = []
    for plan_file in sorted(Path(plans_dir).glob("*_plan.json")):
        try:
            payload = json.loads(plan_file.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise DependencyReconciliationError(
                f"Cannot establish unique Phase 1 authority because {plan_file} is unreadable: {exc}."
            ) from exc
        if not isinstance(payload, list):
            raise DependencyReconciliationError(
                f"Cannot establish unique Phase 1 authority because {plan_file} is not a task array."
            )
        for raw_task in payload:
            if not isinstance(raw_task, dict):
                continue
            if canonicalize_block_id(str(raw_task.get("block_id", "") or "")) == canonical_task_id:
                matches.append((plan_file.resolve(), raw_task))

    if not matches:
        raise DependencyReconciliationError(
            f"Task {canonical_task_id} was not found in tracked Phase 1 plans under {plans_dir}."
        )
    if len(matches) != 1:
        files = ", ".join(str(path) for path, _task in matches)
        raise DependencyReconciliationError(
            f"Task {canonical_task_id} has duplicate Phase 1 plan authority: {files}."
        )

    source_file, raw_task = matches[0]
    normalized_task = canonicalize_task_dict(raw_task)
    normalized_task["source_plan"] = str(
        normalized_task.get("source_plan") or source_file.stem.removesuffix("_plan")
    )
    dependencies = _strict_dependency_list(
        raw_task.get("dependencies"),
        field="Phase 1 dependencies",
        task_id=canonical_task_id,
    )
    return Phase1DependencyAuthority(
        task=normalized_task,
        dependencies=tuple(dependencies),
        source_plan=str(normalized_task["source_plan"]),
        source_file=source_file,
        source_file_sha256=hashlib.sha256(source_file.read_bytes()).hexdigest(),
        source_task_sha256=sha256_json(raw_task),
    )


def _display_source_path(path: Path, runtime_root: Path) -> str:
    try:
        return path.resolve().relative_to(Path(runtime_root).resolve()).as_posix()
    except ValueError:
        return str(path.resolve())


def _assert_dependency_only_scope(
    *,
    task_id: str,
    record: dict[str, Any],
    authority: Phase1DependencyAuthority,
) -> None:
    snapshot = record.get("candidate_snapshot", {})
    if not isinstance(snapshot, dict):
        raise DependencyReconciliationError(f"Task {task_id} has no candidate snapshot to reconcile.")
    snapshot_task_id = canonicalize_block_id(str(snapshot.get("block_id", "") or ""))
    if snapshot_task_id != task_id:
        raise DependencyReconciliationError(
            f"Task {task_id} candidate snapshot identity is {snapshot_task_id!r}; dependency-only repair is unsafe."
        )
    current_source_plan = str(
        snapshot.get("source_plan") or record.get("source_plan") or ""
    ).strip()
    if current_source_plan != authority.source_plan:
        raise DependencyReconciliationError(
            f"Task {task_id} source_plan drifted ({current_source_plan!r} != {authority.source_plan!r}); "
            "dependency-only repair is unsafe."
        )
    current_content = str(snapshot.get("content", "") or "")
    authoritative_content = str(authority.task.get("content", "") or "")
    if current_content != authoritative_content:
        raise DependencyReconciliationError(
            f"Task {task_id} content also drifted from Phase 1; use the normal Phase 1 registration path."
        )


def reconcile_phase2_task_dependencies(
    task_id: str,
    ledger: LedgerManager,
    settings: Any,
    *,
    expected_old_dependencies: list[str],
) -> dict[str, Any]:
    """Reconcile exactly one registered task to its unique Phase 1 dependency list."""

    canonical_task_id = canonicalize_block_id(task_id)
    expected = _strict_dependency_list(
        expected_old_dependencies,
        field="Expected old dependencies",
        task_id=canonical_task_id,
    )
    authority = load_phase1_dependency_authority(canonical_task_id, Path(settings.plans_dir))
    records = getattr(ledger, "ledger", {}).get("tasks", {})
    record = records.get(canonical_task_id) if isinstance(records, dict) else None
    if not isinstance(record, dict):
        raise DependencyReconciliationError(
            f"Task {canonical_task_id} is not registered; dependency reconciliation cannot create or register it."
        )
    _assert_dependency_only_scope(
        task_id=canonical_task_id,
        record=record,
        authority=authority,
    )

    source_file = _display_source_path(authority.source_file, Path(settings.runtime_root))
    identity_basis = {
        "task_id": canonical_task_id,
        "expected_old_dependencies": expected,
        "phase1_dependencies": list(authority.dependencies),
        "source_file": source_file,
        "source_file_sha256": authority.source_file_sha256,
        "source_task_sha256": authority.source_task_sha256,
    }
    audit_event = {
        "schema_version": RECONCILIATION_SCHEMA_VERSION,
        "reconciliation_id": sha256_json(identity_basis),
        "recorded_at": datetime.now(UTC).isoformat().replace("+00:00", "Z"),
        "scope": "single_task",
        "authority": "tracked_phase1_plan_task",
        "reason": "repair_cross_task_dependency_field_contamination",
        "source_plan": authority.source_plan,
        "source_file": source_file,
        "source_file_sha256": authority.source_file_sha256,
        "source_task_sha256": authority.source_task_sha256,
        "expected_old_dependencies": expected,
        "phase1_dependencies": list(authority.dependencies),
        "invalidated_bindings": [
            "runtime_completion_status",
            "build_ready_candidate",
            "phase2_task_status",
            "current_semantic_review_request",
            "semantic_review_apply_receipt",
            "active_review_repair_or_auto_loop",
        ],
    }
    try:
        return ledger.reconcile_candidate_dependencies(
            canonical_task_id,
            expected_dependencies=expected,
            replacement_dependencies=list(authority.dependencies),
            audit_event=audit_event,
        )
    except LedgerDependencyConflictError as exc:
        raise DependencyReconciliationError(str(exc)) from exc
