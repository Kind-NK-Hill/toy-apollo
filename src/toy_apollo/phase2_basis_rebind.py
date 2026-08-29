from __future__ import annotations

import hashlib
import json
import os
import re
from collections.abc import Callable
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from src.block_id_naming import canonicalize_block_id, canonicalize_id_list

from .core import LedgerBasisRebindConflictError, LedgerManager, TaskStatus
from .phase2_dependency_reconcile import (
    DependencyReconciliationError,
    load_phase1_dependency_authority,
)
from .phase2_pack_generation import resolve_phase2_task
from .phase2_pack_shared.artifacts import select_latest_existing_task_file
from .phase2_pack_shared.io import path_exists, read_file_safely, read_json_safely, sha256_json, sha256_text
from .phase2_review_decision import evaluate_semantic_review_result
from .phase2_review_request import (
    _basis_change_is_retirement_only,
    _normalize_retired_proof_obligation_basis,
    build_semantic_review_basis,
)


REBINDS_SCHEMA_VERSION = "phase2.applied_review_basis_rebind.v2"
_SHA256_RE = re.compile(r"[0-9a-f]{64}")


class AppliedReviewBasisRebindError(RuntimeError):
    pass


def _strict_hash(value: str, *, field: str) -> str:
    value = str(value or "").strip().lower()
    if not _SHA256_RE.fullmatch(value):
        raise AppliedReviewBasisRebindError(f"{field} must be one lowercase SHA-256 digest.")
    return value


def _strict_dependencies(raw: list[str], *, task_id: str) -> list[str]:
    if not isinstance(raw, list):
        raise AppliedReviewBasisRebindError("Expected dependencies must be a list.")
    normalized = canonicalize_id_list(raw)
    if len(normalized) != len(raw) or task_id in normalized:
        raise AppliedReviewBasisRebindError("Expected dependencies contain an invalid, duplicate, or self id.")
    return normalized


def _resolve_bound_path(raw: Any, *, pack_dir: Path) -> Path:
    value = str(raw or "").strip()
    if not value:
        raise AppliedReviewBasisRebindError("Applied review provenance contains an empty file path.")
    path = Path(value).expanduser()
    if not path.is_absolute():
        path = pack_dir / path
    path = path.resolve()
    try:
        path.relative_to(pack_dir.resolve())
    except ValueError as exc:
        raise AppliedReviewBasisRebindError(
            f"Applied review provenance escapes its task pack: {path}."
        ) from exc
    if not path_exists(path):
        raise AppliedReviewBasisRebindError(f"Applied review provenance file is missing: {path}.")
    return path


def _consumer_map(raw: Any, *, field: str) -> dict[tuple[str, str], dict[str, Any]]:
    if not isinstance(raw, list):
        raise AppliedReviewBasisRebindError(f"{field} must be an array.")
    mapped: dict[tuple[str, str], dict[str, Any]] = {}
    for item in raw:
        if not isinstance(item, dict):
            raise AppliedReviewBasisRebindError(f"{field} contains a non-object entry.")
        key = (
            canonicalize_block_id(str(item.get("block_id", "") or "")),
            str(item.get("relation", "") or ""),
        )
        if not key[0] or not key[1] or key in mapped:
            raise AppliedReviewBasisRebindError(f"{field} contains an invalid or duplicate consumer identity.")
        mapped[key] = item
    return mapped


def validate_downstream_additions_and_accepted_output_advancements(
    old_basis: dict[str, Any],
    new_basis: dict[str, Any],
    *,
    pending_to_completed_ids: set[str] | None = None,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Return additive consumers and exact accepted-output evidence advancements."""

    if not isinstance(old_basis, dict) or not isinstance(new_basis, dict):
        raise AppliedReviewBasisRebindError("Old and new semantic review bases must be objects.")
    allowed_root = {"direct_downstream_consumers", "downstream_evidence"}
    old_other = {key: value for key, value in old_basis.items() if key not in allowed_root}
    new_other = {key: value for key, value in new_basis.items() if key not in allowed_root}
    if old_other != new_other:
        raise AppliedReviewBasisRebindError("Basis rebind refused: a non-downstream semantic field changed.")

    old_direct = _consumer_map(
        old_basis.get("direct_downstream_consumers"),
        field="old direct_downstream_consumers",
    )
    new_direct = _consumer_map(
        new_basis.get("direct_downstream_consumers"),
        field="new direct_downstream_consumers",
    )
    if not set(old_direct) <= set(new_direct):
        raise AppliedReviewBasisRebindError(
            "Basis rebind refused: downstream consumers were removed."
        )
    for key, old_item in old_direct.items():
        if new_direct[key] != old_item:
            raise AppliedReviewBasisRebindError(
                f"Basis rebind refused: existing downstream consumer {key!r} changed."
            )

    old_downstream = old_basis.get("downstream_evidence")
    new_downstream = new_basis.get("downstream_evidence")
    if not isinstance(old_downstream, dict) or not isinstance(new_downstream, dict):
        raise AppliedReviewBasisRebindError("Basis rebind refused: downstream_evidence must be an object.")
    old_evidence = _consumer_map(
        old_downstream.get("direct_downstream_consumers"),
        field="old downstream evidence",
    )
    new_evidence = _consumer_map(
        new_downstream.get("direct_downstream_consumers"),
        field="new downstream evidence",
    )
    if set(old_evidence) != set(old_direct) or set(new_evidence) != set(new_direct):
        raise AppliedReviewBasisRebindError(
            "Basis rebind refused: downstream consumer and evidence identities disagree."
        )
    old_downstream_other = {
        key: value for key, value in old_downstream.items() if key != "direct_downstream_consumers"
    }
    new_downstream_other = {
        key: value for key, value in new_downstream.items() if key != "direct_downstream_consumers"
    }
    expected_old_scan = bool(old_evidence)
    expected_new_scan = bool(new_evidence)
    if old_downstream_other != {"downstream_import_scan_required_before_quarantine": expected_old_scan}:
        raise AppliedReviewBasisRebindError("Basis rebind refused: old downstream summary is not canonical.")
    if new_downstream_other != {"downstream_import_scan_required_before_quarantine": expected_new_scan}:
        raise AppliedReviewBasisRebindError("Basis rebind refused: new downstream summary is not canonical.")

    advancements: list[dict[str, Any]] = []
    pending_ids = {
        canonicalize_block_id(item) for item in (pending_to_completed_ids or set())
    }
    if "" in pending_ids:
        raise AppliedReviewBasisRebindError("Pending-to-completed ids contain an invalid task id.")
    allowed_advancement_fields = {"official_output_hash", "official_output_imports"}
    for key in sorted(set(old_evidence) & set(new_evidence)):
        old_item = old_evidence[key]
        new_item = new_evidence[key]
        if new_item == old_item:
            continue
        direct = new_direct[key]
        for field, value in direct.items():
            if old_item.get(field) != value or new_item.get(field) != value:
                raise AppliedReviewBasisRebindError(
                    f"Basis rebind refused: existing consumer {key!r} evidence changed identity field {field}."
                )
        is_pending_completion = key[0] in pending_ids
        allowed_fields = (
            allowed_advancement_fields
            | {"official_output_file", "official_output_exists"}
            if is_pending_completion
            else allowed_advancement_fields
        )
        old_fixed = {
            field: value
            for field, value in old_item.items()
            if field not in allowed_fields
        }
        new_fixed = {
            field: value
            for field, value in new_item.items()
            if field not in allowed_fields
        }
        if old_fixed != new_fixed:
            raise AppliedReviewBasisRebindError(
                f"Basis rebind refused: existing consumer {key!r} changed non-output evidence."
            )
        old_output_hash_raw = str(old_item.get("official_output_hash", "") or "")
        if is_pending_completion and not old_output_hash_raw:
            if (
                bool(old_item.get("official_output_exists"))
                or str(old_item.get("official_output_file", "") or "")
                or list(old_item.get("official_output_imports", []) or [])
            ):
                raise AppliedReviewBasisRebindError(
                    f"Basis rebind refused: pending consumer {key!r} has non-empty pre-completion evidence."
                )
            old_output_hash = ""
        else:
            old_output_hash = _strict_hash(
                old_output_hash_raw,
                field=f"Old accepted output hash for {key[0]}",
            )
        new_output_hash = _strict_hash(
            str(new_item.get("official_output_hash", "") or ""),
            field=f"New accepted output hash for {key[0]}",
        )
        if old_output_hash == new_output_hash:
            raise AppliedReviewBasisRebindError(
                f"Basis rebind refused: existing consumer {key!r} did not advance its accepted output."
            )
        advancements.append(
            {
                "consumer": direct,
                "old_evidence": old_item,
                "new_evidence": new_item,
                "old_evidence_hash": sha256_json(old_item),
                "new_evidence_hash": sha256_json(new_item),
                "old_official_output_hash": old_output_hash,
                "new_official_output_hash": new_output_hash,
                "transition_kind": (
                    "pending_to_completed_accepted_output"
                    if is_pending_completion
                    else "existing_consumer_accepted_output_advancement"
                ),
            }
        )

    additions: list[dict[str, Any]] = []
    for key in sorted(set(new_direct) - set(old_direct)):
        direct = new_direct[key]
        evidence = new_evidence[key]
        for field, value in direct.items():
            if evidence.get(field) != value:
                raise AppliedReviewBasisRebindError(
                    f"Basis rebind refused: added consumer {key!r} evidence changed field {field}."
                )
        additions.append({"consumer": direct, "evidence": evidence})
    if not additions and not advancements:
        raise AppliedReviewBasisRebindError("Basis rebind refused: downstream basis delta is a no-op.")
    return additions, advancements


def validate_downstream_only_additions(
    old_basis: dict[str, Any],
    new_basis: dict[str, Any],
) -> list[dict[str, Any]]:
    """Return added consumer evidence or refuse any non-additive basis delta."""

    additions, advancements = validate_downstream_additions_and_accepted_output_advancements(
        old_basis,
        new_basis,
    )
    if advancements:
        raise AppliedReviewBasisRebindError(
            "Basis rebind refused: existing downstream evidence changed."
        )
    return additions


def validate_rebind_basis_delta(
    old_basis: dict[str, Any],
    new_basis: dict[str, Any],
) -> tuple[list[dict[str, Any]], bool]:
    """Compose the official retirement projection with a downstream-only delta."""

    normalized_old = _normalize_retired_proof_obligation_basis(old_basis)
    normalized_new = _normalize_retired_proof_obligation_basis(new_basis)
    if not _basis_change_is_retirement_only(old_basis, normalized_old):
        raise AppliedReviewBasisRebindError(
            "Basis rebind refused: old-basis normalization exceeds the official retirement policy."
        )
    if not _basis_change_is_retirement_only(new_basis, normalized_new):
        raise AppliedReviewBasisRebindError(
            "Basis rebind refused: new-basis normalization exceeds the official retirement policy."
        )
    retirement_normalization_used = (
        normalized_old != old_basis or normalized_new != new_basis
    )
    additions = validate_downstream_only_additions(normalized_old, normalized_new)
    return additions, retirement_normalization_used


def validate_rebind_basis_delta_with_accepted_output_advancements(
    old_basis: dict[str, Any],
    new_basis: dict[str, Any],
    *,
    pending_to_completed_ids: set[str] | None = None,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], bool]:
    """Compose retirement normalization with additive/accepted-output downstream deltas."""

    normalized_old = _normalize_retired_proof_obligation_basis(old_basis)
    normalized_new = _normalize_retired_proof_obligation_basis(new_basis)
    if not _basis_change_is_retirement_only(old_basis, normalized_old):
        raise AppliedReviewBasisRebindError(
            "Basis rebind refused: old-basis normalization exceeds the official retirement policy."
        )
    if not _basis_change_is_retirement_only(new_basis, normalized_new):
        raise AppliedReviewBasisRebindError(
            "Basis rebind refused: new-basis normalization exceeds the official retirement policy."
        )
    retirement_normalization_used = normalized_old != old_basis or normalized_new != new_basis
    additions, advancements = validate_downstream_additions_and_accepted_output_advancements(
        normalized_old,
        normalized_new,
        pending_to_completed_ids=pending_to_completed_ids,
    )
    return additions, advancements, retirement_normalization_used


def _task_payload_from_basis(basis: dict[str, Any]) -> dict[str, Any]:
    payload = basis.get("task")
    if not isinstance(payload, dict):
        raise AppliedReviewBasisRebindError("Semantic review basis has no task payload.")
    return payload


def validate_applied_review_clean_pass(
    result: dict[str, Any],
    review_input: dict[str, Any],
) -> dict[str, Any]:
    """Apply the normal review normalizer/projector and require its clean PASS."""

    decision = evaluate_semantic_review_result(
        result,
        review_input=review_input,
        runner_metadata={"status": "applied_review_basis_rebind_validation"},
    )
    if not decision.is_clean_pass:
        reason = str(decision.result.get("summary", "") or "").strip()
        raise AppliedReviewBasisRebindError(
            "Applied semantic review is no longer a valid, applicable PASS"
            + (f": {reason}" if reason else ".")
        )
    return decision.result


def _validate_added_consumer(
    *,
    task_id: str,
    addition: dict[str, Any],
    ledger: LedgerManager,
    settings: Any,
) -> dict[str, Any]:
    consumer = addition["consumer"]
    evidence = addition["evidence"]
    consumer_id = canonicalize_block_id(str(consumer.get("block_id", "") or ""))
    if str(consumer.get("relation", "") or "") != "hard_dependency":
        raise AppliedReviewBasisRebindError(
            f"Added consumer {consumer_id} is not a hard dependency relation."
        )
    try:
        authority = load_phase1_dependency_authority(consumer_id, Path(settings.plans_dir))
    except DependencyReconciliationError as exc:
        raise AppliedReviewBasisRebindError(
            f"Added consumer {consumer_id} has no unique authoritative Phase 1 plan entry: {exc}"
        ) from exc
    if task_id not in authority.dependencies:
        raise AppliedReviewBasisRebindError(
            f"Added consumer {consumer_id} does not hard-depend on {task_id} in its authoritative plan."
        )

    consumer_task = resolve_phase2_task(consumer_id, ledger, settings)
    if task_id not in canonicalize_id_list(consumer_task.get("dependencies", [])):
        raise AppliedReviewBasisRebindError(
            f"Added consumer {consumer_id} does not currently hard-depend on {task_id}."
        )
    record = ledger.ledger.get("tasks", {}).get(consumer_id, {})
    if not isinstance(record, dict):
        raise AppliedReviewBasisRebindError(f"Added consumer {consumer_id} is not registered.")
    status = str(record.get("status", "") or "")
    phase2_status = str(record.get("phase2_status", "") or "").strip().lower()
    if status == TaskStatus.ORPHANED.value:
        raise AppliedReviewBasisRebindError(f"Added consumer {consumer_id} is retired/ORPHANED.")

    validation = {
        "block_id": consumer_id,
        "authoritative_plan_file": str(authority.source_file),
        "authoritative_plan_task_hash": authority.source_task_sha256,
        "ledger_status": status,
        "phase2_status": phase2_status,
        "validation_mode": "pending_authoritative_plan",
        "completion_claimed": False,
        "official_import_verified": False,
    }
    if status != TaskStatus.COMPLETED.value or phase2_status != "pass":
        return validation

    source_plan = str(consumer_task.get("source_plan", "unknown") or "unknown")
    output_path = select_latest_existing_task_file(consumer_id, source_plan, settings)
    if output_path is None or not path_exists(output_path):
        raise AppliedReviewBasisRebindError(f"Added consumer {consumer_id} has no official output.")
    output_hash = sha256_text(read_file_safely(output_path))
    if not bool(evidence.get("official_output_exists")):
        raise AppliedReviewBasisRebindError(f"Added consumer {consumer_id} evidence says its output is missing.")
    if Path(str(evidence.get("official_output_file", "") or "")).resolve() != output_path.resolve():
        raise AppliedReviewBasisRebindError(f"Added consumer {consumer_id} official path evidence changed.")
    if str(evidence.get("official_output_hash", "") or "") != output_hash:
        raise AppliedReviewBasisRebindError(f"Added consumer {consumer_id} official output hash changed.")
    if str(record.get("latest_applied_review_subject_hash", "") or "") != output_hash:
        raise AppliedReviewBasisRebindError(
            f"Added consumer {consumer_id} PASS is not bound to its current official output."
        )
    imports = [
        line.strip()
        for line in read_file_safely(output_path).splitlines()
        if line.strip().startswith("import ")
    ]
    if evidence.get("official_output_imports") != imports:
        raise AppliedReviewBasisRebindError(f"Added consumer {consumer_id} import evidence changed.")
    expected_import = f"import {getattr(settings, "lean_module_root", "ToyApollo.Output")}.{task_id}"
    if expected_import not in imports:
        raise AppliedReviewBasisRebindError(
            f"Added consumer {consumer_id} does not import {expected_import.removeprefix('import ')}."
        )
    return {
        **validation,
        "validation_mode": "completed_pass_import_verified",
        "completion_claimed": True,
        "official_import_verified": True,
    }


def _validate_completed_consumer_review_receipt(
    *,
    consumer_id: str,
    output_path: Path,
    output_hash: str,
    record: dict[str, Any],
    settings: Any,
) -> dict[str, Any]:
    """Require the current accepted consumer output to retain an exact clean-review receipt."""

    pack_dir = Path(settings.phase2_prompt_packs_dir) / consumer_id
    expected_result_file = str(record.get("latest_applied_review_result_file", "") or "")
    result_path = _resolve_bound_path(expected_result_file, pack_dir=pack_dir)
    result = read_json_safely(result_path, {})
    result_hash = sha256_json(result) if isinstance(result, dict) else ""
    if not result_hash or result_hash != str(record.get("latest_applied_review_result_hash", "") or ""):
        raise AppliedReviewBasisRebindError(
            f"Accepted consumer {consumer_id} review result is missing, invalid, or changed."
        )
    input_path = _resolve_bound_path(result.get("review_input_file"), pack_dir=pack_dir)
    review_input = read_json_safely(input_path, {})
    input_hash = sha256_json(review_input) if isinstance(review_input, dict) else ""
    expected_input_hash = str(record.get("latest_applied_review_input_hash", "") or "")
    if (
        not input_hash
        or input_hash != expected_input_hash
        or str(result.get("review_input_hash", "") or "") != expected_input_hash
    ):
        raise AppliedReviewBasisRebindError(
            f"Accepted consumer {consumer_id} review input binding changed."
        )
    normalized_pass = validate_applied_review_clean_pass(result, review_input)
    review_subject_kind = str(review_input.get("review_subject_kind", "") or "")
    if review_subject_kind not in {"official_output", "candidate"}:
        raise AppliedReviewBasisRebindError(
            f"Accepted consumer {consumer_id} review is not bound to a promotable subject."
        )
    if str(record.get("latest_applied_review_subject_kind", "") or "") != review_subject_kind:
        raise AppliedReviewBasisRebindError(
            f"Accepted consumer {consumer_id} ledger subject kind changed."
        )
    if str(review_input.get("review_subject_hash", "") or "") != output_hash:
        raise AppliedReviewBasisRebindError(
            f"Accepted consumer {consumer_id} review subject is not current."
        )
    candidate = review_input.get("candidate")
    output_text = read_file_safely(output_path)
    if not isinstance(candidate, dict) or str(candidate.get("lean", "") or "") != output_text:
        raise AppliedReviewBasisRebindError(
            f"Accepted consumer {consumer_id} reviewed implementation is not current."
        )
    if str(candidate.get("hash", "") or "") != output_hash:
        raise AppliedReviewBasisRebindError(
            f"Accepted consumer {consumer_id} reviewed candidate hash changed."
        )
    return {
        "review_input_file": str(input_path),
        "review_input_hash": input_hash,
        "review_result_file": str(result_path),
        "review_result_hash": result_hash,
        "review_subject_kind": review_subject_kind,
        "review_verdict": str(normalized_pass.get("verdict", "") or ""),
        "proof_class": str(normalized_pass.get("proof_class", "") or ""),
        "completion_class": str(normalized_pass.get("completion_class", "") or ""),
    }


def _validate_accepted_output_advancement(
    *,
    task_id: str,
    advancement: dict[str, Any],
    ledger: LedgerManager,
    settings: Any,
) -> dict[str, Any]:
    """Validate one existing hard consumer's newly accepted output and review binding."""

    addition = {
        "consumer": advancement["consumer"],
        "evidence": advancement["new_evidence"],
    }
    validation = _validate_added_consumer(
        task_id=task_id,
        addition=addition,
        ledger=ledger,
        settings=settings,
    )
    if validation.get("validation_mode") != "completed_pass_import_verified":
        consumer_id = str(advancement["consumer"].get("block_id", "") or "")
        raise AppliedReviewBasisRebindError(
            f"Existing consumer {consumer_id} accepted-output advancement is not COMPLETED/PASS."
        )
    consumer_id = str(validation["block_id"])
    record = ledger.ledger.get("tasks", {}).get(consumer_id, {})
    output_path = Path(str(advancement["new_evidence"].get("official_output_file", "") or ""))
    output_hash = str(advancement["new_evidence"].get("official_output_hash", "") or "")
    review_binding = _validate_completed_consumer_review_receipt(
        consumer_id=consumer_id,
        output_path=output_path,
        output_hash=output_hash,
        record=record,
        settings=settings,
    )
    return {
        **validation,
        "validation_mode": "existing_consumer_accepted_output_advancement",
        "old_evidence_hash": str(advancement["old_evidence_hash"]),
        "new_evidence_hash": str(advancement["new_evidence_hash"]),
        "old_official_output_hash": str(advancement["old_official_output_hash"]),
        "new_official_output_hash": str(advancement["new_official_output_hash"]),
        "transition_kind": str(
            advancement.get("transition_kind", "existing_consumer_accepted_output_advancement")
        ),
        "review_binding": review_binding,
    }


def _next_receipt_path(pack_dir: Path) -> Path:
    versions: list[int] = []
    for path in pack_dir.glob("basis_rebind_receipt_v*.json"):
        match = re.fullmatch(r"basis_rebind_receipt_v(\d+)\.json", path.name)
        if match:
            versions.append(int(match.group(1)))
    return pack_dir / f"basis_rebind_receipt_v{max(versions, default=0) + 1}.json"


def _materialize_immutable_receipt(receipt_path: Path, receipt_bytes: bytes) -> None:
    """Create and durably flush one never-overwritten receipt before ledger CAS."""

    try:
        descriptor = os.open(receipt_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        with os.fdopen(descriptor, "wb") as handle:
            written = handle.write(receipt_bytes)
            if written != len(receipt_bytes):
                raise OSError(
                    f"short receipt write ({written} of {len(receipt_bytes)} bytes)"
                )
            handle.flush()
            os.fsync(handle.fileno())
        if receipt_path.read_bytes() != receipt_bytes:
            raise OSError("receipt bytes changed during materialization")
        # POSIX needs the directory entry flushed as well as the file contents.
        # Windows' file fsync maps to FlushFileBuffers; opening a directory with
        # os.open is not portable there.
        if os.name != "nt":
            directory_descriptor = os.open(receipt_path.parent, os.O_RDONLY)
            try:
                os.fsync(directory_descriptor)
            finally:
                os.close(directory_descriptor)
    except OSError as exc:
        raise AppliedReviewBasisRebindError(
            "Immutable receipt materialization failed before ledger CAS; "
            f"no ledger mutation was attempted and any created file is preserved: {exc}."
        ) from exc


def _materialize_receipt_before_cas(
    receipt_path: Path,
    receipt_bytes: bytes,
    land_cas: Callable[[], dict[str, Any]],
) -> dict[str, Any]:
    """Make the receipt durable, then attempt the task-local ledger CAS."""

    _materialize_immutable_receipt(receipt_path, receipt_bytes)
    try:
        return land_cas()
    except LedgerBasisRebindConflictError as exc:
        raise AppliedReviewBasisRebindError(
            "Review-basis CAS refused after immutable receipt materialization; "
            f"the complete unreferenced orphan is preserved at {receipt_path}: {exc}."
        ) from exc


def _load_immutable_rebind_receipt(
    event: dict[str, Any],
    *,
    pack_dir: Path,
) -> tuple[Path, dict[str, Any]]:
    raw_path = str(event.get("receipt_file", "") or "").strip()
    if not raw_path:
        raise AppliedReviewBasisRebindError("Applied-review basis rebind history has no receipt file.")
    receipt_path = Path(raw_path).expanduser()
    if not receipt_path.is_absolute():
        receipt_path = pack_dir / receipt_path
    receipt_path = receipt_path.resolve()
    try:
        receipt_path.relative_to(pack_dir.resolve())
    except ValueError as exc:
        raise AppliedReviewBasisRebindError(
            f"Applied-review basis rebind receipt escapes its task pack: {receipt_path}."
        ) from exc
    if not path_exists(receipt_path):
        raise AppliedReviewBasisRebindError(
            f"Applied-review basis rebind receipt is missing: {receipt_path}."
        )
    expected_hash = _strict_hash(
        str(event.get("receipt_sha256", "") or ""),
        field="Applied-review basis rebind receipt hash",
    )
    actual_hash = hashlib.sha256(receipt_path.read_bytes()).hexdigest()
    if actual_hash != expected_hash:
        raise AppliedReviewBasisRebindError(
            f"Applied-review basis rebind receipt hash changed: {receipt_path}."
        )
    receipt = read_json_safely(receipt_path, {})
    if not isinstance(receipt, dict):
        raise AppliedReviewBasisRebindError(
            f"Applied-review basis rebind receipt is not a JSON object: {receipt_path}."
        )
    return receipt_path, receipt


def validate_rebind_chain_tip(
    record: dict[str, Any],
    *,
    task_id: str,
    pack_dir: Path,
    origin_basis_hash: str,
    expected_current_post_basis_hash: str,
) -> dict[str, Any] | None:
    """Validate the immutable rebind chain and return its exact current tip."""

    history = record.get("applied_review_basis_rebind_history", [])
    if not isinstance(history, list):
        raise AppliedReviewBasisRebindError("Applied-review basis rebind history is not an array.")
    if not history:
        if expected_current_post_basis_hash != origin_basis_hash:
            raise AppliedReviewBasisRebindError(
                "Applied-review post-basis differs from its origin without an immutable rebind history."
            )
        return None

    pointer = origin_basis_hash
    previous_event: dict[str, Any] | None = None
    previous_receipt: dict[str, Any] | None = None
    tip: dict[str, Any] | None = None
    for index, raw_event in enumerate(history):
        if not isinstance(raw_event, dict):
            raise AppliedReviewBasisRebindError(
                "Applied-review basis rebind history contains a non-object event."
            )
        event = raw_event
        previous_post = str(event.get("previous_post_basis_hash", "") or "")
        replacement_post = str(event.get("replacement_post_basis_hash", "") or "")
        if previous_post != pointer or not replacement_post or replacement_post == pointer:
            raise AppliedReviewBasisRebindError(
                "Applied-review basis rebind history is stale or branched."
            )
        receipt_path, receipt = _load_immutable_rebind_receipt(event, pack_dir=pack_dir)
        identity = receipt.get("identity")
        if not isinstance(identity, dict):
            raise AppliedReviewBasisRebindError("Applied-review basis rebind receipt has no identity.")
        rebind_id = str(receipt.get("rebind_id", "") or "")
        if (
            str(event.get("rebind_id", "") or "") != rebind_id
            or rebind_id != sha256_json(identity)
            or canonicalize_block_id(str(identity.get("task_id", "") or "")) != task_id
            or str(identity.get("old_basis_hash", "") or "") != pointer
            or str(identity.get("new_basis_hash", "") or "") != replacement_post
        ):
            raise AppliedReviewBasisRebindError(
                "Applied-review basis rebind history and immutable receipt identity disagree."
            )
        if index > 0:
            chain = receipt.get("chain")
            if not isinstance(chain, dict) or previous_event is None or previous_receipt is None:
                raise AppliedReviewBasisRebindError(
                    "Chained applied-review basis rebind receipt has no prior-tip binding."
                )
            expected_chain = {
                "previous_rebind_id": str(previous_receipt.get("rebind_id", "") or ""),
                "previous_receipt_file": str(previous_event.get("receipt_file", "") or ""),
                "previous_receipt_sha256": str(previous_event.get("receipt_sha256", "") or ""),
                "previous_post_basis_hash": pointer,
                "origin_basis_hash": origin_basis_hash,
            }
            if chain != expected_chain:
                raise AppliedReviewBasisRebindError(
                    "Applied-review basis rebind history has a stale or branched prior-tip binding."
                )
        pointer = replacement_post
        previous_event = event
        previous_receipt = receipt
        tip = {
            "event": event,
            "receipt": receipt,
            "receipt_path": receipt_path,
        }

    if pointer != expected_current_post_basis_hash:
        raise AppliedReviewBasisRebindError(
            "Latest immutable applied-review rebind tip differs from the current post-basis."
        )
    return tip


def rebase_review_basis_to_chain_tip(
    origin_basis: dict[str, Any],
    chain_tip: dict[str, Any] | None,
    *,
    expected_post_basis_hash: str,
) -> dict[str, Any]:
    """Reconstruct the exact semantic basis at the immutable rebind chain tip."""

    if chain_tip is None:
        if sha256_json(origin_basis) != expected_post_basis_hash:
            raise AppliedReviewBasisRebindError(
                "Origin basis does not match the unchained applied-review post-basis."
            )
        return origin_basis

    effective = json.loads(json.dumps(_normalize_retired_proof_obligation_basis(origin_basis)))
    receipt = chain_tip.get("receipt", {})
    identity = receipt.get("identity", {}) if isinstance(receipt, dict) else {}
    if not isinstance(identity, dict):
        raise AppliedReviewBasisRebindError("Prior rebind receipt has no identity.")
    post_direct = identity.get("post_direct_downstream_consumers")
    post_evidence = identity.get("post_downstream_evidence")
    if (post_direct is None) != (post_evidence is None):
        raise AppliedReviewBasisRebindError(
            "Prior rebind receipt has an incomplete post-downstream basis snapshot."
        )
    if post_direct is None:
        direct_map = _consumer_map(
            effective.get("direct_downstream_consumers"),
            field="Normalized origin downstream consumers",
        )
        evidence_map = _consumer_map(
            effective.get("downstream_evidence", {}).get("direct_downstream_consumers"),
            field="Normalized origin downstream evidence",
        )
        additions = identity.get("added_consumers", [])
        if not isinstance(additions, list) or not additions:
            raise AppliedReviewBasisRebindError("Prior rebind receipt additions are not an array.")
        for addition in additions:
            if not isinstance(addition, dict):
                raise AppliedReviewBasisRebindError(
                    "Prior rebind receipt contains an invalid consumer addition."
                )
            consumer = addition.get("consumer")
            evidence = addition.get("evidence")
            if not isinstance(consumer, dict) or not isinstance(evidence, dict):
                raise AppliedReviewBasisRebindError(
                    "Prior rebind receipt contains incomplete consumer evidence."
                )
            key = (
                canonicalize_block_id(str(consumer.get("block_id", "") or "")),
                str(consumer.get("relation", "") or ""),
            )
            if not key[0] or not key[1]:
                raise AppliedReviewBasisRebindError(
                    "Prior rebind receipt contains an invalid consumer identity."
                )
            direct_map[key] = consumer
            evidence_map[key] = evidence
        ordered_keys = sorted(direct_map)
        post_direct = [direct_map[key] for key in ordered_keys]
        post_evidence = [evidence_map[key] for key in ordered_keys]
    else:
        _consumer_map(post_direct, field="Prior-tip downstream consumers")
        _consumer_map(post_evidence, field="Prior-tip downstream evidence")

    direct_map = _consumer_map(post_direct, field="Prior-tip downstream consumers")
    evidence_map = _consumer_map(post_evidence, field="Prior-tip downstream evidence")
    if set(direct_map) != set(evidence_map):
        raise AppliedReviewBasisRebindError(
            "Prior-tip downstream consumer and evidence identities disagree."
        )
    effective["direct_downstream_consumers"] = list(post_direct)
    effective_downstream = effective.get("downstream_evidence")
    if not isinstance(effective_downstream, dict):
        raise AppliedReviewBasisRebindError("Normalized origin downstream evidence is invalid.")
    effective_downstream["direct_downstream_consumers"] = list(post_evidence)
    effective_downstream["downstream_import_scan_required_before_quarantine"] = bool(post_evidence)
    if sha256_json(effective) != expected_post_basis_hash:
        raise AppliedReviewBasisRebindError(
            "Reconstructed prior-tip semantic basis does not match the immutable post-basis hash."
        )
    return effective


def validate_pending_to_completed_enrichment(
    previous_receipt: dict[str, Any],
    additions: list[dict[str, Any]],
    consumer_validations: list[dict[str, Any]],
) -> None:
    """Require an exact same-consumer pending-to-completed second hop."""

    identity = previous_receipt.get("identity")
    if not isinstance(identity, dict):
        raise AppliedReviewBasisRebindError("Prior rebind receipt has no identity.")
    prior_additions = identity.get("added_consumers")
    prior_validations = identity.get("added_consumer_validations")
    if not isinstance(prior_additions, list) or not isinstance(prior_validations, list):
        raise AppliedReviewBasisRebindError(
            "Prior rebind receipt has no authoritative consumer validation evidence."
        )

    def addition_map(raw: list[dict[str, Any]], *, field: str) -> dict[tuple[str, str], dict[str, Any]]:
        mapped: dict[tuple[str, str], dict[str, Any]] = {}
        for item in raw:
            if not isinstance(item, dict) or not isinstance(item.get("consumer"), dict):
                raise AppliedReviewBasisRebindError(f"{field} contains an invalid consumer addition.")
            consumer = item["consumer"]
            key = (
                canonicalize_block_id(str(consumer.get("block_id", "") or "")),
                str(consumer.get("relation", "") or ""),
            )
            if not key[0] or not key[1] or key in mapped:
                raise AppliedReviewBasisRebindError(f"{field} has a duplicate consumer identity.")
            mapped[key] = item
        return mapped

    prior_map = addition_map(prior_additions, field="Prior rebind additions")
    current_map = addition_map(additions, field="Current rebind additions")
    if set(prior_map) != set(current_map):
        raise AppliedReviewBasisRebindError(
            "Pending-to-completed enrichment changed the downstream consumer set."
        )
    for key in prior_map:
        if prior_map[key]["consumer"] != current_map[key]["consumer"]:
            raise AppliedReviewBasisRebindError(
                f"Pending-to-completed enrichment changed consumer identity {key!r}."
            )

    def validation_map(raw: list[dict[str, Any]], *, field: str) -> dict[str, dict[str, Any]]:
        mapped: dict[str, dict[str, Any]] = {}
        for item in raw:
            if not isinstance(item, dict):
                raise AppliedReviewBasisRebindError(f"{field} contains a non-object validation.")
            block_id = canonicalize_block_id(str(item.get("block_id", "") or ""))
            if not block_id or block_id in mapped:
                raise AppliedReviewBasisRebindError(f"{field} has an invalid consumer id.")
            mapped[block_id] = item
        return mapped

    prior_validation_map = validation_map(prior_validations, field="Prior rebind validations")
    current_validation_map = validation_map(
        consumer_validations,
        field="Current rebind validations",
    )
    expected_ids = {key[0] for key in prior_map}
    if set(prior_validation_map) != expected_ids or set(current_validation_map) != expected_ids:
        raise AppliedReviewBasisRebindError(
            "Pending-to-completed enrichment consumer validations do not match the consumer set."
        )
    for block_id in sorted(expected_ids):
        prior = prior_validation_map[block_id]
        current = current_validation_map[block_id]
        if (
            prior.get("validation_mode") != "pending_authoritative_plan"
            or prior.get("completion_claimed") is not False
            or prior.get("official_import_verified") is not False
        ):
            raise AppliedReviewBasisRebindError(
                f"Prior consumer {block_id} was not an exact pending-plan validation."
            )
        if (
            current.get("validation_mode") != "completed_pass_import_verified"
            or current.get("completion_claimed") is not True
            or current.get("official_import_verified") is not True
        ):
            raise AppliedReviewBasisRebindError(
                f"Consumer {block_id} did not enrich monotonically to completed PASS/import evidence."
            )


def validate_pending_to_completed_advancements(
    previous_receipt: dict[str, Any],
    advancements: list[dict[str, Any]],
    advancement_validations: list[dict[str, Any]],
) -> None:
    """Require exact pending consumers at the prior tip to become reviewed accepted outputs."""

    identity = previous_receipt.get("identity")
    if not isinstance(identity, dict):
        raise AppliedReviewBasisRebindError("Prior rebind receipt has no identity.")
    prior_additions = identity.get("added_consumers")
    prior_validations = identity.get("added_consumer_validations")
    if not isinstance(prior_additions, list) or not isinstance(prior_validations, list):
        raise AppliedReviewBasisRebindError(
            "Prior rebind receipt has no authoritative consumer validation evidence."
        )
    pending_ids = {
        canonicalize_block_id(str(item.get("block_id", "") or ""))
        for item in prior_validations
        if isinstance(item, dict) and item.get("validation_mode") == "pending_authoritative_plan"
    }
    if not pending_ids or "" in pending_ids:
        raise AppliedReviewBasisRebindError("Prior rebind tip has no valid pending consumers.")
    prior_addition_map = {
        canonicalize_block_id(str(item.get("consumer", {}).get("block_id", "") or "")): item
        for item in prior_additions
        if isinstance(item, dict) and isinstance(item.get("consumer"), dict)
    }
    advancement_map = {
        canonicalize_block_id(str(item.get("consumer", {}).get("block_id", "") or "")): item
        for item in advancements
        if isinstance(item, dict) and isinstance(item.get("consumer"), dict)
    }
    validation_map = {
        canonicalize_block_id(str(item.get("block_id", "") or "")): item
        for item in advancement_validations
        if isinstance(item, dict)
    }
    if set(prior_addition_map) < pending_ids or set(advancement_map) != pending_ids:
        raise AppliedReviewBasisRebindError(
            "Pending-to-completed advancement changed the pending consumer set."
        )
    if set(validation_map) != pending_ids:
        raise AppliedReviewBasisRebindError(
            "Pending-to-completed advancement validations do not match the pending consumer set."
        )
    for block_id in sorted(pending_ids):
        prior = prior_addition_map[block_id]
        current = advancement_map[block_id]
        if prior.get("consumer") != current.get("consumer"):
            raise AppliedReviewBasisRebindError(
                f"Pending-to-completed advancement changed consumer identity {block_id}."
            )
        if prior.get("evidence") != current.get("old_evidence"):
            raise AppliedReviewBasisRebindError(
                f"Pending-to-completed advancement lost prior evidence for {block_id}."
            )
        validation = validation_map[block_id]
        if (
            validation.get("validation_mode") != "existing_consumer_accepted_output_advancement"
            or validation.get("completion_claimed") is not True
            or validation.get("official_import_verified") is not True
            or validation.get("review_binding", {}).get("review_verdict") != "pass"
        ):
            raise AppliedReviewBasisRebindError(
                f"Consumer {block_id} did not advance to a reviewed COMPLETED/PASS output."
            )


def rebase_accepted_output_advancements_to_chain_tip(
    advancements: list[dict[str, Any]],
    chain_tip: dict[str, Any] | None,
) -> list[dict[str, Any]]:
    """Bind advancement old-evidence hashes to the exact latest immutable chain tip."""

    if not advancements or chain_tip is None:
        return advancements
    identity = chain_tip.get("receipt", {}).get("identity", {})
    prior_post = identity.get("post_downstream_evidence") if isinstance(identity, dict) else None
    if prior_post is None:
        # Legacy additive-only receipts never changed origin-existing consumer evidence.
        return advancements
    prior_map = _consumer_map(prior_post, field="Prior-tip downstream evidence")
    rebound: list[dict[str, Any]] = []
    allowed_advancement_fields = {"official_output_hash", "official_output_imports"}
    for advancement in advancements:
        consumer = advancement["consumer"]
        key = (
            canonicalize_block_id(str(consumer.get("block_id", "") or "")),
            str(consumer.get("relation", "") or ""),
        )
        prior = prior_map.get(key)
        if prior is None:
            raise AppliedReviewBasisRebindError(
                f"Accepted-output advancement consumer {key!r} is absent from the prior chain tip."
            )
        current = advancement["new_evidence"]
        if prior == current:
            raise AppliedReviewBasisRebindError(
                f"Accepted-output advancement consumer {key!r} is unchanged from the prior chain tip."
            )
        for field, value in consumer.items():
            if prior.get(field) != value or current.get(field) != value:
                raise AppliedReviewBasisRebindError(
                    f"Accepted-output advancement consumer {key!r} changed identity field {field}."
                )
        prior_fixed = {
            field: value for field, value in prior.items() if field not in allowed_advancement_fields
        }
        current_fixed = {
            field: value for field, value in current.items() if field not in allowed_advancement_fields
        }
        if prior_fixed != current_fixed:
            raise AppliedReviewBasisRebindError(
                f"Accepted-output advancement consumer {key!r} changed non-output evidence."
            )
        prior_output_hash = _strict_hash(
            str(prior.get("official_output_hash", "") or ""),
            field=f"Prior-tip accepted output hash for {key[0]}",
        )
        current_output_hash = _strict_hash(
            str(current.get("official_output_hash", "") or ""),
            field=f"Current accepted output hash for {key[0]}",
        )
        if prior_output_hash == current_output_hash:
            raise AppliedReviewBasisRebindError(
                f"Accepted-output advancement consumer {key!r} did not advance its output hash."
            )
        rebound.append(
            {
                **advancement,
                "old_evidence": prior,
                "old_evidence_hash": sha256_json(prior),
                "old_official_output_hash": prior_output_hash,
                "new_evidence_hash": sha256_json(current),
                "new_official_output_hash": current_output_hash,
            }
        )
    return rebound


def rebind_phase2_applied_review_basis(
    task_id: str,
    ledger: LedgerManager,
    settings: Any,
    *,
    expected_old_basis_hash: str,
    expected_new_basis_hash: str,
    expected_subject_hash: str,
    expected_dependencies: list[str],
) -> dict[str, Any]:
    canonical_task_id = canonicalize_block_id(task_id)
    if not canonical_task_id:
        raise AppliedReviewBasisRebindError("Review-basis rebind task id is empty or invalid.")
    old_hash = _strict_hash(expected_old_basis_hash, field="Expected old basis hash")
    new_hash = _strict_hash(expected_new_basis_hash, field="Expected new basis hash")
    subject_hash = _strict_hash(expected_subject_hash, field="Expected subject hash")
    dependencies = _strict_dependencies(expected_dependencies, task_id=canonical_task_id)
    if old_hash == new_hash:
        raise AppliedReviewBasisRebindError("Expected old and new basis hashes must differ.")

    record = ledger.ledger.get("tasks", {}).get(canonical_task_id, {})
    if not isinstance(record, dict):
        raise AppliedReviewBasisRebindError(f"Task {canonical_task_id} is not registered.")
    pack_dir = Path(settings.phase2_prompt_packs_dir) / canonical_task_id
    if not path_exists(pack_dir):
        raise AppliedReviewBasisRebindError(f"Task pack is missing: {pack_dir}.")

    expected_result_file = str(record.get("latest_applied_review_result_file", "") or "")
    result_path = _resolve_bound_path(expected_result_file, pack_dir=pack_dir)
    result = read_json_safely(result_path, {})
    if not isinstance(result, dict) or sha256_json(result) != str(
        record.get("latest_applied_review_result_hash", "") or ""
    ):
        raise AppliedReviewBasisRebindError("Applied semantic review result is missing, invalid, or changed.")

    input_path = _resolve_bound_path(result.get("review_input_file"), pack_dir=pack_dir)
    review_input = read_json_safely(input_path, {})
    input_hash = sha256_json(review_input) if isinstance(review_input, dict) else ""
    expected_input_hash = str(record.get("latest_applied_review_input_hash", "") or "")
    if not input_hash or input_hash != expected_input_hash or str(
        result.get("review_input_hash", "") or ""
    ) != expected_input_hash:
        raise AppliedReviewBasisRebindError("Applied semantic review input hash binding changed.")
    normalized_pass = validate_applied_review_clean_pass(result, review_input)
    if str(review_input.get("review_subject_kind", "") or "") != "official_output":
        raise AppliedReviewBasisRebindError("Only an applied official-output review can be rebound.")
    if str(review_input.get("review_subject_hash", "") or "") != subject_hash:
        raise AppliedReviewBasisRebindError("Applied review subject hash differs from the expected subject.")
    origin_hash = _strict_hash(
        str(record.get("latest_applied_review_origin_basis_hash", "") or ""),
        field="Applied review origin basis hash",
    )
    old_basis = review_input.get("review_basis")
    if not isinstance(old_basis, dict) or sha256_json(old_basis) != origin_hash:
        raise AppliedReviewBasisRebindError("Applied review input does not contain its bound origin basis.")
    if str(review_input.get("review_basis_hash", "") or "") != origin_hash:
        raise AppliedReviewBasisRebindError("Applied review input basis binding changed.")
    if str(record.get("latest_applied_review_post_basis_hash", "") or "") != old_hash:
        raise AppliedReviewBasisRebindError("Current applied post-basis differs from the expected old basis.")
    if str(record.get("latest_applied_review_subject_hash", "") or "") != subject_hash:
        raise AppliedReviewBasisRebindError("Current applied subject differs from the expected subject.")
    chain_tip = validate_rebind_chain_tip(
        record,
        task_id=canonical_task_id,
        pack_dir=pack_dir,
        origin_basis_hash=origin_hash,
        expected_current_post_basis_hash=old_hash,
    )
    comparison_old_basis = rebase_review_basis_to_chain_tip(
        old_basis,
        chain_tip,
        expected_post_basis_hash=old_hash,
    )
    previous_pending_consumers = (
        list(chain_tip["receipt"].get("basis_delta_components", {}).get("pending_consumers", []))
        if chain_tip is not None
        else []
    )

    task = resolve_phase2_task(canonical_task_id, ledger, settings)
    official_path = select_latest_existing_task_file(
        canonical_task_id,
        str(task.get("source_plan", "unknown") or "unknown"),
        settings,
    )
    if official_path is None or not path_exists(official_path):
        raise AppliedReviewBasisRebindError("Canonical official output is missing.")
    official_text = read_file_safely(official_path)
    if sha256_text(official_text) != subject_hash:
        raise AppliedReviewBasisRebindError("Canonical official output changed from the applied review subject.")
    candidate = review_input.get("candidate")
    if not isinstance(candidate, dict) or str(candidate.get("lean", "") or "") != official_text:
        raise AppliedReviewBasisRebindError("Canonical official implementation differs from the reviewed snapshot.")
    if str(candidate.get("hash", "") or "") != subject_hash:
        raise AppliedReviewBasisRebindError("Reviewed candidate implementation hash binding changed.")

    authority = load_phase1_dependency_authority(canonical_task_id, Path(settings.plans_dir))
    if list(authority.dependencies) != dependencies:
        raise AppliedReviewBasisRebindError("Tracked Phase 1 hard dependencies differ from the expected list.")
    current_basis = build_semantic_review_basis(
        task,
        ledger,
        settings,
        review_subject_kind="official_output",
        review_subject_hash=subject_hash,
        review_subject_file=official_path,
    )
    if sha256_json(current_basis) != new_hash:
        raise AppliedReviewBasisRebindError("Current semantic review basis differs from the expected new basis.")
    old_task_payload = _task_payload_from_basis(old_basis)
    current_task_payload = _task_payload_from_basis(current_basis)
    if old_task_payload != current_task_payload:
        raise AppliedReviewBasisRebindError("Task semantic payload changed; fresh review is required.")
    if canonicalize_id_list(current_task_payload.get("dependencies", [])) != dependencies:
        raise AppliedReviewBasisRebindError("Runtime hard dependencies differ from the expected list.")

    (
        additions,
        accepted_output_advancements,
        retirement_normalization_used,
    ) = validate_rebind_basis_delta_with_accepted_output_advancements(
        comparison_old_basis,
        current_basis,
        pending_to_completed_ids=set(previous_pending_consumers),
    )
    consumer_validations: list[dict[str, Any]] = []
    for addition in additions:
        consumer_validations.append(
            _validate_added_consumer(
                task_id=canonical_task_id,
                addition=addition,
                ledger=ledger,
                settings=settings,
            )
        )
    advancement_validations: list[dict[str, Any]] = []
    for advancement in accepted_output_advancements:
        advancement_validations.append(
            _validate_accepted_output_advancement(
                task_id=canonical_task_id,
                advancement=advancement,
                ledger=ledger,
                settings=settings,
            )
        )
    pending_to_completed_enrichment = bool(previous_pending_consumers)
    if pending_to_completed_enrichment:
        validate_pending_to_completed_advancements(
            chain_tip["receipt"],
            accepted_output_advancements,
            advancement_validations,
        )

    receipt_path = _next_receipt_path(pack_dir)
    if path_exists(receipt_path):
        raise AppliedReviewBasisRebindError(f"Immutable receipt path already exists: {receipt_path}.")
    raw_implementation_hash = hashlib.sha256(official_path.read_bytes()).hexdigest()
    identity = {
        "task_id": canonical_task_id,
        "old_basis_hash": old_hash,
        "new_basis_hash": new_hash,
        "origin_basis_hash": origin_hash,
        "subject_hash": subject_hash,
        "raw_implementation_hash": raw_implementation_hash,
        "semantic_task_payload_hash": sha256_json(current_task_payload),
        "dependencies": dependencies,
        "added_consumers": additions,
        "added_consumer_validations": consumer_validations,
        "accepted_output_advancements": accepted_output_advancements,
        "accepted_output_advancement_validations": advancement_validations,
        "post_direct_downstream_consumers": list(
            current_basis.get("direct_downstream_consumers", [])
        ),
        "post_downstream_evidence": list(
            current_basis.get("downstream_evidence", {}).get("direct_downstream_consumers", [])
        ),
        "retirement_policy_normalization_only": retirement_normalization_used,
        "review_input_hash": expected_input_hash,
        "review_result_hash": str(record.get("latest_applied_review_result_hash", "") or ""),
    }
    chain = None
    if chain_tip is not None:
        previous_event = chain_tip["event"]
        previous_receipt = chain_tip["receipt"]
        chain = {
            "previous_rebind_id": str(previous_receipt.get("rebind_id", "") or ""),
            "previous_receipt_file": str(previous_event.get("receipt_file", "") or ""),
            "previous_receipt_sha256": str(previous_event.get("receipt_sha256", "") or ""),
            "previous_post_basis_hash": old_hash,
            "origin_basis_hash": origin_hash,
        }
    receipt = {
        "schema_version": REBINDS_SCHEMA_VERSION,
        "rebind_id": sha256_json(identity),
        "recorded_at": datetime.now(UTC).isoformat().replace("+00:00", "Z"),
        "scope": "single_task_applied_review",
        "reason": (
            "pending_to_completed_downstream_consumer_evidence_enrichment"
            if pending_to_completed_enrichment
            else (
                "existing_consumer_accepted_output_advancement"
                if accepted_output_advancements and not additions
                else (
                    "additive_consumers_plus_existing_consumer_accepted_output_advancement"
                    if accepted_output_advancements
                    else (
                        "retirement_policy_normalization_plus_additive_authoritative_downstream_consumer_evidence"
                        if retirement_normalization_used
                        else "additive_authoritative_downstream_consumer_evidence_only"
                    )
                )
            )
        ),
        "not_a_new_semantic_review": True,
        "pending_to_completed_enrichment": pending_to_completed_enrichment,
        "identity": identity,
        "review_provenance": {
            "review_input_file": str(input_path),
            "review_input_hash": expected_input_hash,
            "review_result_file": str(result_path),
            "review_result_hash": str(record.get("latest_applied_review_result_hash", "") or ""),
            "verdict": "pass",
            "proof_class": str(normalized_pass.get("proof_class", "") or ""),
            "completion_class": str(normalized_pass.get("completion_class", "") or ""),
        },
        "validated_invariants": {
            "official_subject_unchanged": True,
            "official_implementation_unchanged": True,
            "semantic_task_payload_unchanged": True,
            "hard_dependencies_unchanged": True,
            "basis_delta_downstream_additions_only": not accepted_output_advancements,
            "basis_delta_downstream_additions_or_accepted_output_advancements_only": True,
            "immutable_rebind_chain_tip_exact": True,
            "origin_review_input_and_result_unchanged": True,
            "pending_to_completed_enrichment": pending_to_completed_enrichment,
            "retirement_policy_normalization_only": retirement_normalization_used,
            "added_consumers_authoritative_planned_hard_dependencies_non_retired": True,
            "added_consumers_completed_pass_and_import_target": all(
                item["validation_mode"] == "completed_pass_import_verified"
                for item in consumer_validations
            ),
            "pending_consumers_do_not_claim_completion": all(
                item["completion_claimed"] is False
                for item in consumer_validations
                if item["validation_mode"] == "pending_authoritative_plan"
            ),
            "advanced_consumers_completed_pass_import_and_review_bound": all(
                item["validation_mode"] == "existing_consumer_accepted_output_advancement"
                and item["completion_claimed"] is True
                and item["official_import_verified"] is True
                and item["review_binding"]["review_verdict"] == "pass"
                for item in advancement_validations
            ),
        },
        "basis_delta_components": {
            "retirement_policy_normalization_only": retirement_normalization_used,
            "additive_downstream_consumers": [
                item["block_id"] for item in consumer_validations
            ],
            "pending_consumers": [
                item["block_id"]
                for item in consumer_validations
                if item["validation_mode"] == "pending_authoritative_plan"
            ],
            "previous_pending_consumers": previous_pending_consumers,
            "accepted_output_advancements": [
                {
                    "block_id": item["block_id"],
                    "old_evidence_hash": item["old_evidence_hash"],
                    "new_evidence_hash": item["new_evidence_hash"],
                    "old_official_output_hash": item["old_official_output_hash"],
                    "new_official_output_hash": item["new_official_output_hash"],
                }
                for item in advancement_validations
            ],
        },
        "mutation_contract": {
            "advance_only": "latest_applied_review_post_basis_hash",
            "preserve_review_input_result_and_verdict": True,
            "append_immutable_history": True,
        },
    }
    if chain is not None:
        receipt["chain"] = chain
    receipt_bytes = (json.dumps(receipt, indent=2, ensure_ascii=False) + "\n").encode("utf-8")
    receipt_hash = hashlib.sha256(receipt_bytes).hexdigest()
    event = {
        **receipt,
        "receipt_file": str(receipt_path),
        "receipt_sha256": receipt_hash,
    }
    expected_rebind_revision = int(record.get("applied_review_basis_rebind_revision", 0) or 0)
    expected_rebind_tip_id = (
        str(chain_tip["receipt"].get("rebind_id", "") or "")
        if chain_tip is not None
        else ""
    )
    expected_rebind_tip_receipt_sha256 = (
        str(chain_tip["event"].get("receipt_sha256", "") or "")
        if chain_tip is not None
        else ""
    )

    def land_rebind_cas() -> dict[str, Any]:
        return ledger.rebind_applied_review_basis(
            canonical_task_id,
            expected_subject_hash=subject_hash,
            expected_subject_kind=str(review_input.get("review_subject_kind", "") or ""),
            expected_origin_basis_hash=origin_hash,
            expected_old_basis_hash=old_hash,
            replacement_basis_hash=new_hash,
            expected_input_hash=expected_input_hash,
            expected_result_file=expected_result_file,
            expected_result_hash=str(record.get("latest_applied_review_result_hash", "") or ""),
            expected_rebind_revision=expected_rebind_revision,
            expected_rebind_tip_id=expected_rebind_tip_id,
            expected_rebind_tip_receipt_sha256=expected_rebind_tip_receipt_sha256,
            expected_dependencies=dependencies,
            expected_task_payload=current_task_payload,
            receipt_event=event,
        )

    return _materialize_receipt_before_cas(receipt_path, receipt_bytes, land_rebind_cas)
