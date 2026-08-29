from __future__ import annotations

import json
import os
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Mapping

from src.block_id_naming import canonicalize_block_id, canonicalize_id_list, canonicalize_task_dict

from .phase2_dependency_reconcile import (
    DependencyReconciliationError,
    load_phase1_dependency_authority,
)
from .phase2_pack_generation import resolve_phase2_task
from .state_reconcile import (
    CommandResult,
    ReconciliationError,
    chapter_for_task,
    discover_runtime_support_files,
    run_command,
)
from .state_store import (
    StateConcurrencyError,
    SubjectBundle,
    WorkspaceStateStore,
    sha256_bytes,
    sha256_file,
    sha256_json,
    utc_now,
)


FROZEN_OWNER_SCOPE = "chapters_1_4_frozen_dependency"
FROZEN_AUTHORITY_SCOPE = "frozen_owner_dependency_chapters_1_4"
FROZEN_OWNER_HASH_ENV = "TOY_APOLLO_FROZEN_OWNER_TOKEN_SHA256"
FROZEN_DECISION_SCHEMA = "toy-apollo.frozen-owner-decision.v1"
FROZEN_BUILD_SCHEMA = "toy-apollo.frozen-mechanical-build.v1"
FROZEN_RECEIPT_SCHEMA = "toy-apollo.frozen-owner-dependency-receipt.v2"
FROZEN_REVOCATION_SCHEMA = "toy-apollo.frozen-owner-dependency-revocation.v1"
FROZEN_HEAD_ROLE = "frozen_dependency"
HEX_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


class FrozenDependencyAuthorityError(RuntimeError):
    pass


@dataclass(frozen=True)
class FrozenDependencyBasis:
    task_id: str
    task_contract: dict[str, Any]
    operational_task: dict[str, Any]
    subject: SubjectBundle
    dependencies: tuple[str, ...]
    dependency_subjects: tuple[dict[str, Any], ...]

    def as_dict(self) -> dict[str, Any]:
        return {
            "task_id": self.task_id,
            "task_contract": self.task_contract,
            "subject": _subject_payload(self.subject),
            "dependencies": list(self.dependencies),
            "dependencies_sha256": sha256_json(list(self.dependencies)),
            "dependency_subjects": list(self.dependency_subjects),
            "dependency_subjects_sha256": sha256_json(list(self.dependency_subjects)),
        }


def _subject_payload(subject: SubjectBundle) -> dict[str, Any]:
    return {
        "subject_id": subject.subject_id,
        "primary_path": subject.primary_path,
        "primary_hash": subject.primary_hash,
        "bundle_hash": subject.bundle_hash,
        "files": subject.manifest(),
    }


def _logical_path(path: Path, runtime_root: Path) -> str:
    try:
        return path.resolve().relative_to(runtime_root.resolve()).as_posix()
    except ValueError:
        return str(path.resolve())


def _strict_dependencies(task_id: str, raw: Any) -> tuple[str, ...]:
    if not isinstance(raw, list):
        raise FrozenDependencyAuthorityError(
            f"Task {task_id} exact-current dependencies are missing or not a list."
        )
    normalized = canonicalize_id_list(raw)
    if len(normalized) != len(raw) or task_id in normalized:
        raise FrozenDependencyAuthorityError(
            f"Task {task_id} exact-current dependencies contain invalid or duplicate ids."
        )
    return tuple(normalized)


def _operational_contract(task_id: str, task: Mapping[str, Any]) -> dict[str, Any]:
    snapshot = task.get("candidate_snapshot")
    source = snapshot if isinstance(snapshot, Mapping) else task
    normalized = canonicalize_task_dict(dict(source))
    block_id = canonicalize_block_id(
        str(normalized.get("block_id") or task.get("block_id") or task_id)
    )
    dependencies = _strict_dependencies(
        task_id,
        normalized.get("dependencies", task.get("dependencies")),
    )
    contract = {
        "block_id": block_id,
        "type": str(normalized.get("type") or task.get("type") or ""),
        "content": str(normalized.get("content") or task.get("content") or ""),
        "source_plan": str(
            normalized.get("source_plan") or task.get("source_plan") or ""
        ),
        "dependencies": list(dependencies),
    }
    if block_id != task_id or not contract["content"] or not contract["source_plan"]:
        raise FrozenDependencyAuthorityError(
            f"Task {task_id} exact-current operational contract is incomplete or mismatched."
        )
    return contract


def _official_subject(task_id: str, settings) -> SubjectBundle:
    runtime_root = Path(settings.runtime_root).resolve()
    primary_path = Path(settings.toyapollo_output_dir) / f"{task_id}.lean"
    if not primary_path.is_file():
        raise FrozenDependencyAuthorityError(
            f"Canonical Toy output is missing for {task_id}: {primary_path}."
        )
    primary_logical = _logical_path(primary_path, runtime_root)
    expected_primary = f"{getattr(settings, "output_subdir", "ToyApollo/Output")}/{task_id}.lean"
    if primary_logical != expected_primary:
        raise FrozenDependencyAuthorityError(
            f"Canonical Toy output path for {task_id} is not {expected_primary}: {primary_logical}."
        )
    files: dict[str, bytes] = {primary_logical: primary_path.read_bytes()}
    try:
        files.update(discover_runtime_support_files(runtime_root, task_id))
    except Exception as exc:
        raise FrozenDependencyAuthorityError(
            f"Cannot establish exact current support bundle for {task_id}: {exc}"
        ) from exc
    return SubjectBundle.from_files(
        task_id=task_id,
        files=files,
        primary_path=primary_logical,
        source_repo="toy_apollo",
        layout="toy_frozen_dependency",
        subject_kind="frozen_dependency_subject",
    )


def compute_frozen_dependency_basis(task_id: str, ledger, settings) -> FrozenDependencyBasis:
    canonical_task_id = canonicalize_block_id(task_id)
    if chapter_for_task(canonical_task_id) not in {1, 2, 3, 4}:
        raise FrozenDependencyAuthorityError(
            f"Frozen owner dependency authority is limited to Chapter 1-4 block_ids; got {task_id!r}."
        )
    try:
        plan = load_phase1_dependency_authority(
            canonical_task_id,
            Path(settings.plans_dir),
        )
        resolved = resolve_phase2_task(canonical_task_id, ledger, settings)
    except (DependencyReconciliationError, FileNotFoundError, KeyError, ValueError) as exc:
        raise FrozenDependencyAuthorityError(str(exc)) from exc
    if not isinstance(resolved, dict):
        raise FrozenDependencyAuthorityError(
            f"Task {canonical_task_id} exact-current resolver did not return a task."
        )
    operational_task = _operational_contract(canonical_task_id, resolved)
    if operational_task["source_plan"] != plan.source_plan:
        raise FrozenDependencyAuthorityError(
            f"Task {canonical_task_id} exact-current source_plan drifted from tracked Phase 1."
        )
    dependencies = tuple(operational_task["dependencies"])
    runtime_root = Path(settings.runtime_root).resolve()
    source_path = runtime_root / "inputs" / f"{plan.source_plan}.tex"
    if not source_path.is_file():
        raise FrozenDependencyAuthorityError(
            f"Current source TeX contract is missing for {canonical_task_id}: {source_path}."
        )
    subject = _official_subject(canonical_task_id, settings)
    dependency_subjects = tuple(
        {
            "task_id": dependency_id,
            **_subject_payload(_official_subject(dependency_id, settings)),
        }
        for dependency_id in dependencies
    )
    task_contract = {
        "resolver": "resolve_phase2_task",
        "resolved_task_sha256": sha256_json(operational_task),
        "source_plan": plan.source_plan,
        "plan_file": _logical_path(plan.source_file, runtime_root),
        "plan_file_sha256": plan.source_file_sha256,
        "plan_task_sha256": plan.source_task_sha256,
        "source_file": _logical_path(source_path, runtime_root),
        "source_file_sha256": sha256_file(source_path),
    }
    return FrozenDependencyBasis(
        task_id=canonical_task_id,
        task_contract=task_contract,
        operational_task=operational_task,
        subject=subject,
        dependencies=dependencies,
        dependency_subjects=dependency_subjects,
    )


def _receipt_bytes(payload: Mapping[str, Any]) -> bytes:
    return (
        json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode("utf-8")


def _write_content_addressed(root: Path, payload: Mapping[str, Any]) -> tuple[Path, str]:
    raw = _receipt_bytes(payload)
    digest = sha256_bytes(raw)
    root.mkdir(parents=True, exist_ok=True)
    path = root / f"{digest}.json"
    try:
        with path.open("xb") as handle:
            handle.write(raw)
            handle.flush()
            os.fsync(handle.fileno())
    except FileExistsError:
        if path.read_bytes() != raw:
            raise FrozenDependencyAuthorityError(
                f"Content-addressed artifact collision: {path}."
            )
    return path.resolve(), digest


def _configured_owner_hash(settings) -> str:
    configured = str(
        getattr(settings, "frozen_owner_token_sha256", "")
        or os.environ.get(FROZEN_OWNER_HASH_ENV, "")
        or ""
    ).strip().lower()
    if not HEX_SHA256_RE.fullmatch(configured):
        raise FrozenDependencyAuthorityError(
            f"Configured owner token SHA-256 is missing or invalid; set {FROZEN_OWNER_HASH_ENV}."
        )
    return configured


def _load_owner_decision(
    *,
    task_id: str,
    action: str,
    owner_scope: str,
    owner_token: str,
    owner_reason: str,
    decision_path: str | Path,
    settings,
) -> dict[str, Any]:
    if owner_scope != FROZEN_OWNER_SCOPE:
        raise FrozenDependencyAuthorityError(
            f"Owner scope must be exactly {FROZEN_OWNER_SCOPE!r}."
        )
    token = str(owner_token or "").strip()
    if len(token) < 8:
        raise FrozenDependencyAuthorityError("Presented owner decision token is not explicit.")
    token_hash = sha256_bytes(token.encode("utf-8"))
    configured_hash = _configured_owner_hash(settings)
    if token_hash != configured_hash:
        raise FrozenDependencyAuthorityError(
            "Presented owner decision token does not match the configured owner identity."
        )
    reason = str(owner_reason or "").strip()
    if len(reason) < 8:
        raise FrozenDependencyAuthorityError("Owner reason must be explicit.")
    path = Path(decision_path).expanduser().resolve()
    if not path.is_file():
        raise FrozenDependencyAuthorityError(f"Owner decision file is missing: {path}.")
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise FrozenDependencyAuthorityError(f"Owner decision file is invalid: {exc}") from exc
    expected = {
        "schema_version": FROZEN_DECISION_SCHEMA,
        "action": action,
        "task_id": task_id,
        "owner_scope": owner_scope,
        "owner_token_sha256": configured_hash,
        "reason": reason,
    }
    if not isinstance(payload, dict) or any(payload.get(k) != v for k, v in expected.items()):
        raise FrozenDependencyAuthorityError(
            "Owner decision file does not match task/action/scope/identity/reason."
        )
    return {
        "file": str(path),
        "sha256": sha256_file(path),
        "scope": owner_scope,
        "token_sha256": configured_hash,
        "reason": reason,
        "payload": payload,
    }


def _bound_decision_is_current(decision: Any) -> bool:
    if not isinstance(decision, dict):
        return False
    try:
        path = Path(str(decision.get("file", "") or "")).expanduser().resolve()
        if not path.is_file() or sha256_file(path) != decision.get("sha256"):
            return False
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    return payload == decision.get("payload")


def _state_store(settings) -> WorkspaceStateStore:
    state_path = getattr(settings, "state_db_file", None)
    if state_path is None:
        raise FrozenDependencyAuthorityError("Workspace state_db_file is not configured.")
    store = WorkspaceStateStore(Path(state_path))
    if not store.exists:
        raise FrozenDependencyAuthorityError(
            f"Workspace state database is missing: {store.path}."
        )
    store.assert_integrity()
    return store


def build_frozen_dependency_evidence(
    task_id: str,
    ledger,
    settings,
    *,
    command_runner: Callable[..., CommandResult] = run_command,
    timeout: int = 600,
) -> dict[str, Any]:
    basis = compute_frozen_dependency_basis(task_id, ledger, settings)
    module = f"{getattr(settings, "lean_module_root", "ToyApollo.Output")}.{basis.task_id}"
    command = ["lake", "build", module]
    try:
        result = command_runner(
            command,
            cwd=Path(settings.runtime_root),
            timeout=timeout,
        )
    except ReconciliationError as exc:
        raise FrozenDependencyAuthorityError(str(exc)) from exc
    refreshed = compute_frozen_dependency_basis(task_id, ledger, settings)
    if refreshed.as_dict() != basis.as_dict():
        raise FrozenDependencyAuthorityError(
            "Frozen dependency basis drifted while the mechanical build ran."
        )
    if result.returncode != 0:
        raise FrozenDependencyAuthorityError(
            f"lake build {module} failed with exit code {result.returncode}."
        )
    basis_hash = sha256_json(basis.as_dict())
    run_id = sha256_json(
        {
            "operation": "frozen_dependency_build_check",
            "task_id": basis.task_id,
            "basis_sha256": basis_hash,
            "module": module,
        }
    )
    payload = {
        "schema_version": FROZEN_BUILD_SCHEMA,
        "task_id": basis.task_id,
        "module": module,
        "command": command,
        "exit_code": 0,
        "primary_path": basis.subject.primary_path,
        "primary_sha256": basis.subject.primary_hash,
        "subject_bundle_sha256": basis.subject.bundle_hash,
        "basis_sha256": basis_hash,
        "stdout_sha256": sha256_bytes(result.stdout),
        "stderr_sha256": sha256_bytes(result.stderr),
        "run_id": run_id,
    }
    path, evidence_hash = _write_content_addressed(
        Path(settings.artifact_root) / "frozen_dependency_builds" / basis.task_id,
        payload,
    )
    store = _state_store(settings)
    existing = store.run_record(run_id)
    if existing is None:
        store.upsert_subject(basis.subject)
        store.record_run(
            task_id=basis.task_id,
            operation="frozen_dependency_build_check",
            status="completed",
            subject_id=basis.subject.subject_id,
            artifact_path=path,
            detail={
                "evidence_sha256": evidence_hash,
                "basis_sha256": basis_hash,
                "subject_bundle_sha256": basis.subject.bundle_hash,
                "module": module,
            },
            run_id=run_id,
            completed_at=utc_now(),
        )
    return {
        "task_id": basis.task_id,
        "evidence_file": str(path),
        "evidence_sha256": evidence_hash,
        "run_id": run_id,
        "primary_hash": basis.subject.primary_hash,
        "bundle_hash": basis.subject.bundle_hash,
        "dependencies": list(basis.dependencies),
    }


def _controlled_build_evidence(
    path: str | Path,
    *,
    basis: FrozenDependencyBasis,
    settings,
) -> dict[str, Any]:
    evidence_path = Path(path).expanduser().resolve()
    controlled_root = (
        Path(settings.artifact_root) / "frozen_dependency_builds" / basis.task_id
    ).resolve()
    try:
        evidence_path.relative_to(controlled_root)
    except ValueError as exc:
        raise FrozenDependencyAuthorityError(
            "Build evidence is outside the harness-owned artifact root."
        ) from exc
    if not evidence_path.is_file():
        raise FrozenDependencyAuthorityError(f"Build evidence is missing: {evidence_path}.")
    evidence_hash = sha256_file(evidence_path)
    if evidence_path.name != f"{evidence_hash}.json":
        raise FrozenDependencyAuthorityError(
            "Build evidence filename does not match its content hash."
        )
    try:
        payload = json.loads(evidence_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise FrozenDependencyAuthorityError(f"Build evidence is invalid: {exc}") from exc
    expected = {
        "schema_version": FROZEN_BUILD_SCHEMA,
        "task_id": basis.task_id,
        "module": f"{getattr(settings, "lean_module_root", "ToyApollo.Output")}.{basis.task_id}",
        "command": ["lake", "build", f"{getattr(settings, "lean_module_root", "ToyApollo.Output")}.{basis.task_id}"],
        "exit_code": 0,
        "primary_path": basis.subject.primary_path,
        "primary_sha256": basis.subject.primary_hash,
        "subject_bundle_sha256": basis.subject.bundle_hash,
        "basis_sha256": sha256_json(basis.as_dict()),
    }
    if not isinstance(payload, dict) or any(payload.get(k) != v for k, v in expected.items()):
        raise FrozenDependencyAuthorityError(
            "Build evidence does not match the exact current task/module/subject/basis."
        )
    run_id = str(payload.get("run_id", "") or "")
    run = _state_store(settings).run_record(run_id)
    if run is None:
        raise FrozenDependencyAuthorityError("Build evidence has no matching normalized state run.")
    try:
        detail = json.loads(str(run.get("detail_json", "") or "{}"))
    except json.JSONDecodeError as exc:
        raise FrozenDependencyAuthorityError("Build state run detail is invalid.") from exc
    if (
        run.get("task_id") != basis.task_id
        or run.get("operation") != "frozen_dependency_build_check"
        or run.get("status") != "completed"
        or run.get("subject_id") != basis.subject.subject_id
        or Path(str(run.get("artifact_path", ""))).resolve() != evidence_path
        or detail.get("evidence_sha256") != evidence_hash
        or detail.get("subject_bundle_sha256") != basis.subject.bundle_hash
    ):
        raise FrozenDependencyAuthorityError(
            "Build evidence does not match its normalized successful state run."
        )
    return {
        "path": str(evidence_path),
        "sha256": evidence_hash,
        "run_id": run_id,
        "payload": payload,
    }


def _current_record(ledger, task_id: str) -> dict[str, Any] | None:
    records = getattr(ledger, "ledger", {}).get("tasks", {})
    record = records.get(task_id) if isinstance(records, dict) else None
    return record if isinstance(record, dict) else None


def _register_or_validate_record(
    ledger,
    basis: FrozenDependencyBasis,
) -> dict[str, Any]:
    tasks = ledger.ledger.setdefault("tasks", {})
    record = tasks.get(basis.task_id)
    if record is None:
        snapshot = dict(basis.operational_task)
        record = {
            **snapshot,
            "status": "TODO",
            "candidate_snapshot": snapshot,
        }
        tasks[basis.task_id] = record
    if not isinstance(record, dict):
        raise FrozenDependencyAuthorityError(
            f"Operational record for {basis.task_id} is invalid."
        )
    if _operational_contract(basis.task_id, record) != basis.operational_task:
        raise FrozenDependencyAuthorityError(
            f"Operational record for {basis.task_id} changed since basis calculation."
        )
    return record


def _authority_detail(
    basis: FrozenDependencyBasis,
    *,
    receipt_path: Path,
    receipt_hash: str,
    decision: Mapping[str, Any],
    build: Mapping[str, Any],
) -> dict[str, Any]:
    return {
        "authority_scope": FROZEN_AUTHORITY_SCOPE,
        "receipt_file": str(receipt_path),
        "receipt_sha256": receipt_hash,
        "owner_decision_file": decision["file"],
        "owner_decision_sha256": decision["sha256"],
        "owner_token_sha256": decision["token_sha256"],
        "task_contract_sha256": sha256_json(basis.task_contract),
        "dependencies_sha256": sha256_json(list(basis.dependencies)),
        "dependency_subjects_sha256": sha256_json(list(basis.dependency_subjects)),
        "build_evidence_sha256": build["sha256"],
        "build_run_id": build["run_id"],
    }


def _record_grant_state(
    store: WorkspaceStateStore,
    *,
    basis: FrozenDependencyBasis,
    receipt_path: Path,
    receipt_hash: str,
    decision: Mapping[str, Any],
    build: Mapping[str, Any],
) -> None:
    detail = _authority_detail(
        basis,
        receipt_path=receipt_path,
        receipt_hash=receipt_hash,
        decision=decision,
        build=build,
    )
    store.upsert_subject(basis.subject)
    store.record_review(
        task_id=basis.task_id,
        subject_id=basis.subject.subject_id,
        verdict="owner_frozen_dependency",
        proof_class="",
        completion_class="",
        phase2_status="",
        evidence_path=receipt_path,
        evidence_hash=receipt_hash,
        reviewer_independence=json.dumps(
            {
                "kind": "owner_decision",
                "owner_token_sha256": decision["token_sha256"],
                "decision_sha256": decision["sha256"],
            },
            sort_keys=True,
        ),
        authority_scope=FROZEN_AUTHORITY_SCOPE,
        authority_eligible=True,
    )
    store.set_task_head(
        task_id=basis.task_id,
        role=FROZEN_HEAD_ROLE,
        subject_id=basis.subject.subject_id,
        detail=detail,
    )
    store.record_run(
        task_id=basis.task_id,
        operation="frozen_dependency_accept",
        status="completed",
        subject_id=basis.subject.subject_id,
        artifact_path=receipt_path,
        detail=detail,
        run_id=sha256_json(
            {
                "operation": "frozen_dependency_accept",
                "task_id": basis.task_id,
                "receipt_sha256": receipt_hash,
            }
        ),
        completed_at=utc_now(),
    )


def accept_frozen_dependency_authority(
    task_id: str,
    ledger,
    settings,
    *,
    owner_scope: str,
    owner_decision_token: str,
    owner_reason: str,
    owner_decision_path: str | Path,
    expected_primary_hash: str,
    expected_subject_hash: str,
    expected_dependencies: list[str],
    expected_frozen_tip: str,
    build_evidence_path: str | Path,
) -> dict[str, Any]:
    basis = compute_frozen_dependency_basis(task_id, ledger, settings)
    decision = _load_owner_decision(
        task_id=basis.task_id,
        action="grant",
        owner_scope=owner_scope,
        owner_token=owner_decision_token,
        owner_reason=owner_reason,
        decision_path=owner_decision_path,
        settings=settings,
    )
    if tuple(canonicalize_id_list(expected_dependencies)) != basis.dependencies:
        raise FrozenDependencyAuthorityError("Expected dependency CAS does not match current basis.")
    if expected_primary_hash != basis.subject.primary_hash:
        raise FrozenDependencyAuthorityError("Expected primary hash does not match current basis.")
    if expected_subject_hash != basis.subject.bundle_hash:
        raise FrozenDependencyAuthorityError("Expected subject hash does not match current basis.")
    build = _controlled_build_evidence(build_evidence_path, basis=basis, settings=settings)
    receipt = {
        "schema_version": FROZEN_RECEIPT_SCHEMA,
        "authority_scope": FROZEN_AUTHORITY_SCOPE,
        "owner_scope": owner_scope,
        "owner_decision": decision,
        "basis": basis.as_dict(),
        "mechanical_build_evidence": build,
        "semantic_status_claim": "none",
        "dependency_projection": {
            "runtime_status": "COMPLETED",
            "dependency_consumable_status": "pass",
            "evidence_type": "frozen_owner_dependency",
        },
    }
    receipt_path, receipt_hash = _write_content_addressed(
        Path(settings.artifact_root)
        / "frozen_dependency_receipts"
        / basis.task_id
        / "grants",
        receipt,
    )
    current = _current_record(ledger, basis.task_id)
    if (
        current is not None
        and current.get("frozen_dependency_active") is True
        and current.get("frozen_dependency_receipt_sha256") == receipt_hash
        and frozen_dependency_projection(
            basis.task_id, current, ledger, settings
        ).get("phase2_status")
        == "pass"
    ):
        return _grant_result(basis, receipt_path, receipt_hash, build)
    refreshed = compute_frozen_dependency_basis(task_id, ledger, settings)
    if refreshed.as_dict() != basis.as_dict() or not _bound_decision_is_current(decision):
        raise FrozenDependencyAuthorityError("Frozen basis drifted during acceptance.")

    def mutate_ledger() -> dict[str, Any]:
        record = _register_or_validate_record(ledger, basis)
        current_tip = str(record.get("frozen_dependency_receipt_sha256", "") or "")
        if current_tip != str(expected_frozen_tip or ""):
            raise FrozenDependencyAuthorityError(
                f"Frozen tip CAS mismatch: expected {expected_frozen_tip!r}, current {current_tip!r}."
            )
        record.update(
            {
                "frozen_dependency_active": True,
                "frozen_dependency_receipt_file": str(receipt_path),
                "frozen_dependency_receipt_sha256": receipt_hash,
                "frozen_dependency_revocation_file": "",
                "frozen_dependency_revocation_sha256": "",
                "frozen_dependency_subject_id": basis.subject.subject_id,
                "frozen_dependency_primary_hash": basis.subject.primary_hash,
                "frozen_dependency_bundle_hash": basis.subject.bundle_hash,
                "frozen_dependency_dependencies": list(basis.dependencies),
                "frozen_dependency_evidence_type": "frozen_owner_dependency",
            }
        )
        return record

    def mutate_normalized(store: WorkspaceStateStore, _result: Any) -> None:
        _record_grant_state(
            store,
            basis=basis,
            receipt_path=receipt_path,
            receipt_hash=receipt_hash,
            decision=decision,
            build=build,
        )

    runner = getattr(ledger, "mutate_with_normalized_state", None)
    if not callable(runner):
        raise FrozenDependencyAuthorityError(
            "Operational ledger lacks atomic campaign+normalized state mutation."
        )
    try:
        runner(mutate_ledger, mutate_normalized)
    except StateConcurrencyError as exc:
        raise FrozenDependencyAuthorityError(str(exc)) from exc
    return _grant_result(basis, receipt_path, receipt_hash, build)


def _grant_result(
    basis: FrozenDependencyBasis,
    receipt_path: Path,
    receipt_hash: str,
    build: Mapping[str, Any],
) -> dict[str, Any]:
    return {
        "task_id": basis.task_id,
        "receipt_file": str(receipt_path),
        "receipt_sha256": receipt_hash,
        "subject_id": basis.subject.subject_id,
        "primary_hash": basis.subject.primary_hash,
        "bundle_hash": basis.subject.bundle_hash,
        "dependencies": list(basis.dependencies),
        "build_evidence_sha256": build["sha256"],
    }


def revoke_frozen_dependency_authority(
    task_id: str,
    ledger,
    settings,
    *,
    expected_current_receipt: str,
    owner_scope: str,
    owner_decision_token: str,
    owner_reason: str,
    owner_decision_path: str | Path,
) -> dict[str, Any]:
    canonical_task_id = canonicalize_block_id(task_id)
    decision = _load_owner_decision(
        task_id=canonical_task_id,
        action="revoke",
        owner_scope=owner_scope,
        owner_token=owner_decision_token,
        owner_reason=owner_reason,
        decision_path=owner_decision_path,
        settings=settings,
    )
    payload = {
        "schema_version": FROZEN_REVOCATION_SCHEMA,
        "authority_scope": FROZEN_AUTHORITY_SCOPE,
        "task_id": canonical_task_id,
        "revoked_receipt_sha256": expected_current_receipt,
        "owner_decision": decision,
    }
    path, receipt_hash = _write_content_addressed(
        Path(settings.artifact_root)
        / "frozen_dependency_receipts"
        / canonical_task_id
        / "revocations",
        payload,
    )
    current = _current_record(ledger, canonical_task_id)
    if (
        current is not None
        and current.get("frozen_dependency_active") is False
        and current.get("frozen_dependency_receipt_sha256") == expected_current_receipt
        and current.get("frozen_dependency_revocation_sha256") == receipt_hash
    ):
        return {
            "task_id": canonical_task_id,
            "revocation_file": str(path),
            "revocation_sha256": receipt_hash,
        }
    if not _bound_decision_is_current(decision):
        raise FrozenDependencyAuthorityError("Owner revoke decision drifted during apply.")

    def mutate_ledger() -> dict[str, Any]:
        record = _current_record(ledger, canonical_task_id)
        if record is None:
            raise FrozenDependencyAuthorityError("No frozen authority exists to revoke.")
        if (
            record.get("frozen_dependency_active") is not True
            or record.get("frozen_dependency_receipt_sha256")
            != expected_current_receipt
        ):
            raise FrozenDependencyAuthorityError("Frozen revoke CAS mismatch.")
        record.update(
            {
                "frozen_dependency_active": False,
                "frozen_dependency_revocation_file": str(path),
                "frozen_dependency_revocation_sha256": receipt_hash,
            }
        )
        return record

    def mutate_normalized(store: WorkspaceStateStore, _result: Any) -> None:
        store.mark_task_head_freshness(
            task_id=canonical_task_id,
            role=FROZEN_HEAD_ROLE,
            freshness="revoked",
        )
        store.record_run(
            task_id=canonical_task_id,
            operation="frozen_dependency_revoke",
            status="completed",
            artifact_path=path,
            detail={
                "revocation_sha256": receipt_hash,
                "revoked_receipt_sha256": expected_current_receipt,
                "owner_decision_sha256": decision["sha256"],
            },
            run_id=sha256_json(
                {
                    "operation": "frozen_dependency_revoke",
                    "task_id": canonical_task_id,
                    "revocation_sha256": receipt_hash,
                }
            ),
            completed_at=utc_now(),
        )

    runner = getattr(ledger, "mutate_with_normalized_state", None)
    if not callable(runner):
        raise FrozenDependencyAuthorityError(
            "Operational ledger lacks atomic campaign+normalized state mutation."
        )
    try:
        runner(mutate_ledger, mutate_normalized)
    except StateConcurrencyError as exc:
        raise FrozenDependencyAuthorityError(str(exc)) from exc
    return {
        "task_id": canonical_task_id,
        "revocation_file": str(path),
        "revocation_sha256": receipt_hash,
    }


def frozen_dependency_projection(
    task_id: str,
    record: Mapping[str, Any],
    ledger,
    settings,
) -> dict[str, Any]:
    if record.get("frozen_dependency_active") is not True:
        return {}
    if record.get("frozen_dependency_revocation_sha256"):
        return {}
    receipt_raw = str(record.get("frozen_dependency_receipt_file", "") or "")
    receipt_hash = str(record.get("frozen_dependency_receipt_sha256", "") or "")
    if not receipt_raw or not receipt_hash:
        return {}
    try:
        path = Path(receipt_raw).expanduser().resolve()
        controlled = (
            Path(settings.artifact_root)
            / "frozen_dependency_receipts"
            / canonicalize_block_id(task_id)
            / "grants"
        ).resolve()
        path.relative_to(controlled)
        if (
            not path.is_file()
            or sha256_file(path) != receipt_hash
            or path.name != f"{receipt_hash}.json"
        ):
            return {}
        receipt = json.loads(path.read_text(encoding="utf-8"))
        if (
            not isinstance(receipt, dict)
            or receipt.get("schema_version") != FROZEN_RECEIPT_SCHEMA
            or receipt.get("authority_scope") != FROZEN_AUTHORITY_SCOPE
            or receipt.get("owner_scope") != FROZEN_OWNER_SCOPE
        ):
            return {}
        if not _bound_decision_is_current(receipt.get("owner_decision")):
            return {}
        basis = compute_frozen_dependency_basis(task_id, ledger, settings)
        if receipt.get("basis") != basis.as_dict():
            return {}
        build = receipt.get("mechanical_build_evidence")
        if not isinstance(build, dict):
            return {}
        if _controlled_build_evidence(build.get("path", ""), basis=basis, settings=settings) != build:
            return {}
        report = _state_store(settings).task_report(basis.task_id)
        head = report.get("heads", {}).get(FROZEN_HEAD_ROLE, {})
        detail = json.loads(str(head.get("detail_json", "") or "{}"))
        if (
            head.get("subject_id") != basis.subject.subject_id
            or head.get("bundle_hash") != basis.subject.bundle_hash
            or head.get("freshness") not in {"fresh", "local"}
            or detail.get("receipt_sha256") != receipt_hash
            or detail.get("authority_scope") != FROZEN_AUTHORITY_SCOPE
        ):
            return {}
    except (
        FrozenDependencyAuthorityError,
        OSError,
        ValueError,
        json.JSONDecodeError,
    ):
        return {}
    return {
        "status": "COMPLETED",
        "phase2_status": "pass",
        "phase2_status_reason": (
            "owner-frozen Chapter 1-4 dependency authority; "
            "dependency scheduling only, not semantic review"
        ),
        "phase2_status_evidence_type": "frozen_owner_dependency",
        "frozen_dependency_receipt_file": str(path),
        "frozen_dependency_receipt_sha256": receipt_hash,
    }
