from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from src.block_id_naming import canonicalize_block_id

from .core import LedgerManager, TaskStatus
from .phase2_pack_shared.artifacts import (
    latest_review_repair_request_path,
    latest_review_repair_summary_path,
    list_versioned_json_files,
    next_review_repair_attempt,
    review_repair_request_path,
    review_repair_summary_path,
    select_latest_existing_task_file,
)
from .phase2_pack_shared.io import (
    copy_file,
    path_exists,
    read_file_safely,
    read_json_safely,
    sha256_json,
    sha256_text,
    unlink_path,
    write_json,
    write_text,
)
from .phase2_pack_shared.review_basis_parts import dedupe_strings
from .phase2_pack_shared.runtime_state import auto_loop_attempt_payload, auto_loop_field_defaults
from .phase2_pack_views import _render_review_repair_summary, refresh_pack_runtime_view, render_semantic_review_report
from .phase2_failure_budget import phase2_failure_counters_from_history
from .phase2_proof_obligations import (
    apply_obligation_review,
    apply_obligation_review_to_file,
    extract_obligation_review_blockers,
    proof_obligation_path,
    seed_focused_child_obligations_from_review,
    summarize_proof_obligations,
)
from .phase2_obligation_tasks import reconcile_obligation_tasks_for_task
from .phase2_output_binding import resolve_phase2_output_binding
from .phase2_review_decision import evaluate_semantic_review_result, project_normalized_semantic_review_result
from .phase2_review_request import (
    _clear_current_review_metadata,
    _resolve_review_binding_path,
    _validate_review_input_freshness,
    build_semantic_review_basis,
)
from .phase2_semantic_review import (
    SEMANTIC_REVIEW_PROMPT_VERSION,
    SEMANTIC_REVIEW_RUBRIC_VERSION,
    latest_semantic_review_artifact_paths,
    next_semantic_review_artifact_paths,
    normalize_reviewer_result,
)
from .phase2_semantic_fail_triage import write_semantic_fail_triage_artifacts
from .phase2_pack_generation import (
    hard_check_diagnostic,
    parse_diagnostics,
    record_semantic_review_attempt,
    review_diagnostics,
    run_lean_module_build,
    run_official_module_build,
    run_staged_official_build,
    support_review_target_from_obligations,
    write_review_compat_summary,
    resolve_phase2_task,
)


@dataclass
class ApplyOutcome:
    success: bool
    detail: str
    disposition: str
    next_action: str = ""
    repair_ready: dict[str, Any] | None = None


def _review_version_matches(value: Any, expected: int) -> bool:
    if isinstance(value, bool):
        return False
    try:
        return int(value) == expected
    except (TypeError, ValueError):
        return False


def _resolve_codex_review_input_path(result_path: Path, raw_result: Any) -> Path | None:
    if isinstance(raw_result, dict):
        raw_input_path = str(raw_result.get("review_input_file", "") or "").strip()
        if raw_input_path:
            path = Path(raw_input_path).expanduser()
            if not path.is_absolute():
                result_relative = (result_path.parent / path).resolve()
                if path_exists(result_relative):
                    return result_relative
                cwd_relative = (Path.cwd() / path).resolve()
                if path_exists(cwd_relative):
                    return cwd_relative
                path = result_relative
            return path
    if result_path.name.startswith("semantic_review_result_v") and result_path.suffix == ".json":
        version = result_path.stem.removeprefix("semantic_review_result_v")
        if version.isdigit():
            return result_path.parent / f"semantic_review_input_v{version}.json"
    return None


def _review_repair_request_path(pack_dir: Path, attempt: int) -> Path:
    return review_repair_request_path(pack_dir, attempt)


def _latest_review_repair_request_path(pack_dir: Path) -> Path:
    return latest_review_repair_request_path(pack_dir)


def _review_repair_summary_path(pack_dir: Path, attempt: int) -> Path:
    return review_repair_summary_path(pack_dir, attempt)


def _latest_review_repair_summary_path(pack_dir: Path) -> Path:
    return latest_review_repair_summary_path(pack_dir)


def _next_review_repair_attempt(pack_dir: Path) -> int:
    return next_review_repair_attempt(pack_dir)


def _sync_current_review_repair_aliases(
    pack_dir: Path,
    *,
    request_path: Path | None = None,
    summary_path: Path | None = None,
) -> None:
    alias_paths = {
        "request": _latest_review_repair_request_path(pack_dir),
        "summary": _latest_review_repair_summary_path(pack_dir),
    }
    for source, alias in ((request_path, alias_paths["request"]), (summary_path, alias_paths["summary"])):
        if source is None:
            continue
        if path_exists(alias):
            unlink_path(alias)
        copy_file(source, alias)


def _has_accepted_proof_debt(review_result: dict[str, Any], task_record: dict[str, Any]) -> bool:
    obligation_review = review_result.get("obligation_review", {}) if isinstance(review_result, dict) else {}
    if isinstance(obligation_review, dict):
        items = obligation_review.get("items", [])
        if isinstance(items, list) and any(
            isinstance(item, dict) and str(item.get("status", "") or "").strip().lower() == "accepted_as_proof_debt"
            for item in items
        ):
            return True
    proof_summary = task_record.get("proof_obligation_summary", {}) if isinstance(task_record, dict) else {}
    status_counts = proof_summary.get("status_counts", {}) if isinstance(proof_summary, dict) else {}
    if isinstance(status_counts, dict):
        try:
            return int(status_counts.get("accepted_as_proof_debt", 0) or 0) > 0
        except (TypeError, ValueError):
            return False
    return False


def _review_completion_status(review_result: dict[str, Any], task_record: dict[str, Any], task_status_projection=None) -> TaskStatus:
    if task_status_projection is not None and str(task_status_projection.task_status) != "pass":
        return TaskStatus.COMPLETED_WITH_PROOF_DEBT
    if _has_accepted_proof_debt(review_result, task_record):
        return TaskStatus.COMPLETED_WITH_PROOF_DEBT
    return TaskStatus.COMPLETED


def _classify_review_task_status(task_id: str, task: dict[str, Any], review_result: dict[str, Any]):
    task_payload = dict(task)
    task_payload["block_id"] = task_id
    projection = project_normalized_semantic_review_result(review_result, task=task_payload).task_status_projection
    if projection is None:
        raise ValueError("operationally invalid semantic review has no task-status projection")
    return projection


def _review_with_task_status(task_id: str, task: dict[str, Any], review_result: dict[str, Any]) -> tuple[dict[str, Any], Any]:
    task_payload = dict(task)
    task_payload["block_id"] = task_id
    decision = project_normalized_semantic_review_result(review_result, task=task_payload)
    if decision.task_status_projection is None:
        raise ValueError("operationally invalid semantic review has no task-status projection")
    return decision.result, decision.task_status_projection


def _clear_current_review_repair_metadata(task_id: str, ledger: LedgerManager) -> None:
    ledger.update_runtime_metadata(
        task_id,
        current_review_repair_request_file="",
        current_review_repair_summary_file="",
        current_review_repair_seed_file="",
        current_review_repair_origin_result_file="",
        current_review_repair_archive_file="",
    )


def _set_current_review_repair_metadata(
    task_id: str,
    ledger: LedgerManager,
    *,
    request_file: str,
    summary_file: str,
    seed_file: str,
    origin_result_file: str,
    archive_file: str = "",
) -> None:
    ledger.update_runtime_metadata(
        task_id,
        current_review_repair_request_file=request_file,
        current_review_repair_summary_file=summary_file,
        current_review_repair_seed_file=seed_file,
        current_review_repair_origin_result_file=origin_result_file,
        current_review_repair_archive_file=archive_file,
    )


def _invalid_codex_review_result(review_input: dict[str, Any], reason: str, raw_result: Any | None = None) -> dict[str, Any]:
    raw = {
        "verdict": "inconclusive",
        "confidence": "none",
        "summary": reason,
        "reviewer_independence": {
            "role": "independent_read_only_reviewer",
            "read_only": True,
            "did_edit_candidate": False,
            "used_current_review_request": False,
            "attestation": f"Review-apply generated invalid-result record: {reason}",
        },
        "source_claims": [],
        "claim_mapping": [],
        "findings": [{"severity": "error", "category": "review_apply", "message": reason}],
        "recommended_disposition": "needs_review",
    }
    if raw_result is not None:
        raw["raw_result"] = raw_result
    result = normalize_reviewer_result(
        raw,
        review_input=review_input,
        runner_metadata={"status": "codex_handoff_invalid", "reason": reason},
    )
    result["normalization_reason"] = reason
    return result


def _write_normalized_codex_review_artifacts(
    pack_dir: Path,
    review_input: dict[str, Any],
    normalized_result: dict[str, Any],
) -> dict[str, Any]:
    attempt = int(review_input.get("attempt") or 0) or len(list_versioned_json_files(pack_dir, "semantic_review_input"))
    paths = next_semantic_review_artifact_paths(pack_dir, attempt)
    latest = latest_semantic_review_artifact_paths(pack_dir)
    normalized_result = dict(normalized_result)
    normalized_result["review_input_file"] = str(paths["input"]) if path_exists(paths["input"]) else str(normalized_result.get("review_input_file", ""))
    normalized_result["review_prompt_file"] = str(paths["prompt"]) if path_exists(paths["prompt"]) else str(normalized_result.get("review_prompt_file", ""))
    normalized_result["review_result_file"] = str(paths["result"])
    normalized_result["review_report_file"] = str(paths["report"])
    write_json(paths["result"], normalized_result)
    write_text(paths["report"], render_semantic_review_report(normalized_result))
    for key, path in paths.items():
        if not path_exists(path):
            continue
        if path_exists(latest[key]):
            unlink_path(latest[key])
        copy_file(path, latest[key])
    return normalized_result


def _build_review_repair_contract(
    *,
    task: dict[str, Any],
    review_input: dict[str, Any],
    review_result: dict[str, Any],
    failed_review_input_file: Path,
    failed_review_result_file: Path,
    failed_review_report_file: Path,
    failed_review_subject_file: Path,
    next_draft_seed_file: Path,
    attempt: int,
    origin_review_mode: str,
) -> dict[str, Any]:
    review_basis = review_input.get("review_basis", {}) if isinstance(review_input.get("review_basis", {}), dict) else {}
    findings = review_result.get("findings", []) if isinstance(review_result.get("findings", []), list) else []
    downstream = review_result.get("downstream_adequacy", {}) if isinstance(review_result.get("downstream_adequacy", {}), dict) else {}
    blocking_issues = downstream.get("blocking_issues", []) if isinstance(downstream.get("blocking_issues", []), list) else []
    forbidden_shortcuts = review_basis.get("forbidden_weakenings", []) if isinstance(review_basis.get("forbidden_weakenings", []), list) else []
    proof_obligations = review_basis.get("proof_obligations", {}) if isinstance(review_basis.get("proof_obligations", {}), dict) else {}
    proof_obligations_file = str(review_basis.get("proof_obligations_file", "") or "").strip()
    if proof_obligations_file:
        current_proof_obligations = read_json_safely(Path(proof_obligations_file), {})
        if isinstance(current_proof_obligations, dict):
            proof_obligations = current_proof_obligations
    proof_obligation_summary = (
        review_basis.get("proof_obligation_summary", {})
        if isinstance(review_basis.get("proof_obligation_summary", {}), dict)
        else summarize_proof_obligations(proof_obligations) if proof_obligations else {}
    )
    if proof_obligations:
        proof_obligation_summary = summarize_proof_obligations(proof_obligations)
    proof_obligation_blockers = extract_obligation_review_blockers(review_result)
    obligation_review = review_result.get("obligation_review", {}) if isinstance(review_result.get("obligation_review", {}), dict) else {}

    must_fix: list[str] = []
    summary = str(review_result.get("summary", "") or "").strip()
    if summary:
        must_fix.append(summary)
    normalization_reason = str(review_result.get("normalization_reason", "") or "").strip()
    if normalization_reason:
        must_fix.append(normalization_reason)
    for finding in findings:
        if isinstance(finding, dict):
            message = str(finding.get("message", "") or finding.get("summary", "") or "").strip()
            if message and message not in must_fix:
                must_fix.append(message)
    for blocker in proof_obligation_blockers:
        obligation_id = str(blocker.get("obligation_id", "") or "(unassigned)").strip()
        issue = str(blocker.get("issue", "") or "").strip()
        message = f"Proof obligation `{obligation_id}`: {issue or 'unresolved blocker'}"
        if message not in must_fix:
            must_fix.append(message)
    if not must_fix:
        must_fix.append(f"Resolve semantic review verdict `{review_result.get('verdict', 'inconclusive')}` for {task['block_id']}.")

    must_preserve = dedupe_strings(
        [
            f"Preserve the original task statement: {str(task.get('content', '') or '').strip()}",
            *[
                f"Preserve allowed abstraction: {item}"
                for item in review_basis.get("allowed_abstractions", [])
                if isinstance(item, str) and item.strip()
            ],
        ]
    )
    downstream_blockers = dedupe_strings(
        [
            str(item.get("issue", "") or item.get("summary", "") or "").strip()
            for item in blocking_issues
            if isinstance(item, dict)
        ]
    )
    result_text = read_file_safely(failed_review_result_file) if path_exists(failed_review_result_file) else ""
    subject_text = read_file_safely(failed_review_subject_file) if path_exists(failed_review_subject_file) else ""
    return {
        "schema_version": "phase2.review_repair.request.v1",
        "task_id": task["block_id"],
        "origin_review_mode": origin_review_mode,
        "origin_review_attempt": int(review_input.get("attempt") or 0) or attempt,
        "review_subject_kind": str(review_input.get("review_subject_kind", "") or "candidate"),
        "failed_verdict": str(review_result.get("verdict", "inconclusive") or "inconclusive"),
        "failed_phase2_status": str(review_result.get("phase2_status", "") or ""),
        "failed_phase2_status_reason": str(review_result.get("phase2_status_reason", "") or ""),
        "failed_phase2_status_evidence_type": str(review_result.get("phase2_status_evidence_type", "") or ""),
        "failed_review_input_file": str(failed_review_input_file),
        "failed_review_result_file": str(failed_review_result_file),
        "failed_review_report_file": str(failed_review_report_file),
        "failed_review_subject_file": str(failed_review_subject_file),
        "failed_review_subject_hash": str(review_input.get("review_subject_hash", "") or review_input.get("candidate", {}).get("hash", "") or sha256_text(subject_text)),
        "review_basis_hash": str(review_input.get("review_basis_hash", "") or ""),
        "review_result_hash": sha256_text(result_text) if result_text else "",
        "origin_prompt_version": int(review_input.get("prompt_version") or SEMANTIC_REVIEW_PROMPT_VERSION),
        "origin_rubric_version": int(review_input.get("rubric_version") or SEMANTIC_REVIEW_RUBRIC_VERSION),
        "origin_result_schema_version": str(review_result.get("schema_version", "") or ""),
        "source_task_content": str(task.get("content", "") or ""),
        "must_fix": must_fix,
        "must_preserve": must_preserve,
        "forbidden_shortcuts": [item for item in forbidden_shortcuts if isinstance(item, str) and item.strip()],
        "proof_obligations_file": proof_obligations_file,
        "proof_obligation_summary": proof_obligation_summary,
        "proof_obligation_blockers": proof_obligation_blockers,
        "obligation_review": obligation_review,
        "scaffold_hypotheses": proof_obligations.get("scaffold_hypotheses", []) if isinstance(proof_obligations, dict) else [],
        "downstream_blockers": downstream_blockers,
        "next_draft_seed_file": str(next_draft_seed_file),
    }


def _write_review_repair_artifacts(
    *,
    task: dict[str, Any],
    ledger: LedgerManager,
    settings,
    pack_dir: Path,
    review_input: dict[str, Any],
    review_result: dict[str, Any],
    failed_review_input_file: Path,
    failed_review_result_file: Path,
    failed_review_report_file: Path,
    failed_review_subject_file: Path,
    next_draft_seed_file: Path,
    origin_review_mode: str,
) -> dict[str, Any]:
    attempt = _next_review_repair_attempt(pack_dir)
    request_path = _review_repair_request_path(pack_dir, attempt)
    summary_path = _review_repair_summary_path(pack_dir, attempt)
    request_payload = _build_review_repair_contract(
        task=task,
        review_input=review_input,
        review_result=review_result,
        failed_review_input_file=failed_review_input_file,
        failed_review_result_file=failed_review_result_file,
        failed_review_report_file=failed_review_report_file,
        failed_review_subject_file=failed_review_subject_file,
        next_draft_seed_file=next_draft_seed_file,
        attempt=attempt,
        origin_review_mode=origin_review_mode,
    )
    triage_result = write_semantic_fail_triage_artifacts(
        task=task,
        pack_dir=pack_dir,
        review_input=review_input,
        review_result=review_result,
        repair_request=request_payload,
        failed_review_subject_file=failed_review_subject_file,
        attempt=attempt,
    )
    request_payload["semantic_fail_triage"] = triage_result
    write_json(request_path, request_payload)
    write_text(summary_path, _render_review_repair_summary(request_payload))
    _sync_current_review_repair_aliases(pack_dir, request_path=request_path, summary_path=summary_path)
    ledger.update_runtime_metadata(
        task["block_id"],
        latest_review_repair_request_file=str(request_path),
        latest_review_repair_summary_file=str(summary_path),
        latest_semantic_fail_triage_file=str(triage_result.get("triage_path", "")),
        latest_semantic_fail_triage_category=str(triage_result.get("category", "")),
        latest_semantic_fail_triage_needs_diagnoser=bool(triage_result.get("needs_diagnoser", False)),
        latest_semantic_fail_triage_local_repair_allowed=bool(triage_result.get("local_repair_allowed", False)),
        latest_diagnoser_prompt_file=str(triage_result.get("prompt_path", "")),
        latest_diagnosis_state=str(triage_result.get("diagnosis_state", "")),
    )
    _set_current_review_repair_metadata(
        task["block_id"],
        ledger,
        request_file=str(request_path),
        summary_file=str(summary_path),
        seed_file=str(next_draft_seed_file),
        origin_result_file=str(failed_review_result_file),
    )
    return {
        "request_path": request_path,
        "summary_path": summary_path,
        "request_payload": request_payload,
    }


async def apply_codex_review_result_once(
    task_id: str,
    ledger: LedgerManager,
    settings,
    review_result_arg: str,
) -> ApplyOutcome:
    task = resolve_phase2_task(task_id, ledger, settings)
    task_id = task["block_id"]
    registered_task = ledger.ledger.get("tasks", {}).get(task_id)
    if not isinstance(registered_task, dict):
        return ApplyOutcome(
            success=False,
            detail=f"Phase 2 task is not registered in the ledger for review-apply: {task_id}",
            disposition="codex_review_invalid_no_promotion",
        )
    output_binding = resolve_phase2_output_binding(task, ledger, settings)
    apply_original_status = str(ledger.ledger.get("tasks", {}).get(task_id, {}).get("status", ""))
    pack_dir = settings.phase2_prompt_packs_dir / task_id
    if not path_exists(pack_dir):
        raise FileNotFoundError(f"Phase 2 prompt pack does not exist for review-apply: {task_id}")

    result_path = Path(review_result_arg).expanduser()
    if not result_path.is_absolute():
        result_path = (Path.cwd() / result_path).resolve()
    if not path_exists(result_path):
        raise FileNotFoundError(f"Review result file not found: {result_path}")
    try:
        raw_result = json.loads(read_file_safely(result_path))
    except Exception as exc:
        raw_result = {"_json_error": str(exc)}

    review_input_path = _resolve_codex_review_input_path(result_path, raw_result)
    if review_input_path is None or not path_exists(review_input_path):
        review_input = {
            "task": {"block_id": task_id},
            "mode": "review-apply",
            "attempt": len(list_versioned_json_files(pack_dir, "verify_result")) + 1,
            "prompt_version": SEMANTIC_REVIEW_PROMPT_VERSION,
            "rubric_version": SEMANTIC_REVIEW_RUBRIC_VERSION,
            "candidate": {"file": str(result_path), "hash": "", "lean": ""},
            "reviewer_backend_id": "codex-handoff",
            "cache_key": "",
        }
        normalized_review = _invalid_codex_review_result(review_input, "review_input_file is missing or does not exist", raw_result)
    else:
        review_input = read_json_safely(review_input_path, {})
        if not isinstance(review_input, dict):
            review_input = {
                "task": {"block_id": task_id},
                "mode": "review-apply",
                "attempt": len(list_versioned_json_files(pack_dir, "verify_result")) + 1,
                "prompt_version": SEMANTIC_REVIEW_PROMPT_VERSION,
                "rubric_version": SEMANTIC_REVIEW_RUBRIC_VERSION,
                "candidate": {"file": str(result_path), "hash": "", "lean": ""},
                "reviewer_backend_id": "codex-handoff",
                "cache_key": "",
            }
            normalized_review = _invalid_codex_review_result(review_input, "review input JSON is invalid", raw_result)
        else:
            normalized_review = evaluate_semantic_review_result(
                raw_result,
                review_input=review_input,
                runner_metadata={"status": "codex_handoff_applied", "result_file": str(result_path)},
            ).result
    review_task_payload = review_input.get("task", {}) if isinstance(review_input.get("task", {}), dict) else {}
    review_candidate_payload = review_input.get("candidate", {}) if isinstance(review_input.get("candidate", {}), dict) else {}
    review_basis = review_input.get("review_basis", {}) if isinstance(review_input.get("review_basis", {}), dict) else {}
    proof_obligations_file = str(review_basis.get("proof_obligations_file", "") or "").strip()
    source_plan = str(task.get("source_plan", "unknown") or "unknown")
    existing_official_output = select_latest_existing_task_file(task_id, source_plan, settings)
    completed_status_values = {TaskStatus.COMPLETED.value, TaskStatus.COMPLETED_WITH_PROOF_DEBT.value}
    existing_completed_output = (
        apply_original_status in completed_status_values
        and existing_official_output is not None
        and path_exists(existing_official_output)
    )

    review_subject_kind = str(review_input.get("review_subject_kind", "") or "candidate")
    subject_file_raw = str(review_input.get("review_subject_file", "") or review_candidate_payload.get("file", result_path))
    candidate_path = Path(subject_file_raw).expanduser()
    if not candidate_path.is_absolute():
        candidate_path = (pack_dir / candidate_path).resolve()
    candidate_code = read_file_safely(candidate_path) if path_exists(candidate_path) else str(review_candidate_payload.get("lean", "") or "")
    review_subject_hash = str(review_input.get("review_subject_hash", "") or review_candidate_payload.get("hash", "") or "")

    def already_promoted_candidate_review() -> bool:
        if not existing_completed_output or review_subject_kind != "candidate":
            return False
        if not isinstance(normalized_review, dict):
            return False
        if str(normalized_review.get("verdict", "") or "").strip().lower() != "pass":
            return False
        if str(normalized_review.get("recommended_disposition", "") or "").strip().lower() != "promote":
            return False
        if _classify_review_task_status(task_id, task, normalized_review).task_status != "pass":
            return False
        expected_hash = str(review_candidate_payload.get("hash", "") or review_subject_hash or "")
        if not expected_hash or existing_official_output is None:
            return False
        existing_output_code = read_file_safely(existing_official_output)
        return bool(existing_output_code) and sha256_text(existing_output_code) == expected_hash

    def finish(
        *,
        success: bool,
        detail_text: str,
        diagnostics: list[dict[str, Any]],
        semantic_review: dict[str, Any],
        disposition: str,
        state_transition: str,
        final_build_success: bool = False,
        final_build_output: str = "",
        repair_ready: dict[str, Any] | None = None,
        next_action: str = "",
    ) -> ApplyOutcome:
        task_status_projection = None
        if isinstance(semantic_review, dict) and str(semantic_review.get("cache_class", "") or "").strip().lower() == "semantic_verdict":
            task_status_projection = _classify_review_task_status(task_id, task, semantic_review)
            semantic_review = dict(semantic_review)
            semantic_review["phase2_status"] = task_status_projection.task_status
            semantic_review["phase2_status_reason"] = task_status_projection.reason
            semantic_review["phase2_status_evidence_type"] = task_status_projection.evidence_type
            semantic_review["task_status"] = task_status_projection.task_status
            semantic_review["task_status_reason"] = task_status_projection.reason
            semantic_review["task_status_evidence_type"] = task_status_projection.evidence_type
            semantic_review["task_role"] = task_status_projection.task_role
            if "Task status:" not in detail_text:
                detail_text = f"{detail_text} Task status: {task_status_projection.task_status} ({task_status_projection.reason})."
            if success and task_status_projection.task_status != "pass":
                if not disposition.endswith("_non_clean"):
                    disposition = f"{disposition}_non_clean"
                if state_transition == "completed":
                    state_transition = "non_clean_completed"
                if "Non-clean apply" not in detail_text:
                    detail_text = (
                        f"{detail_text} Non-clean apply: review verdict is pass, but task_status="
                        f"{task_status_projection.task_status}; this is not textbook completion."
                    )
        verify_result_path = write_review_compat_summary(
            task_id=task_id,
            ledger=ledger,
            task=task,
            settings=settings,
            pack_dir=pack_dir,
            mode="review-apply",
            candidate_path=candidate_path,
            candidate_code=candidate_code,
            detail_text=detail_text,
            diagnostics=diagnostics,
            disposition=disposition,
            semantic_review=semantic_review,
            final_build_success=final_build_success,
            final_build_output=final_build_output,
            success=success,
            state_transition=state_transition,
        )
        history = record_semantic_review_attempt(
            pack_dir=pack_dir,
            task_id=task_id,
            candidate_path=candidate_path,
            candidate_code=candidate_code,
            verify_result_path=verify_result_path,
            semantic_review=semantic_review,
            disposition=disposition,
            review_subject_kind=review_subject_kind,
            success=success,
            repair_ready=repair_ready,
            auto_loop_metadata=auto_loop_attempt_payload(ledger.ledger.get("tasks", {}).get(task_id, {})),
        )
        failure_counters = phase2_failure_counters_from_history(history)
        ledger.update_runtime_metadata(
            task_id,
            phase2_build_fail_counter=failure_counters.build_fail_counter,
            phase2_review_fail_counter=failure_counters.review_fail_counter,
        )
        if task_status_projection is not None:
            ledger.update_runtime_metadata(
                task_id,
                phase2_review_verdict=task_status_projection.review_verdict,
                phase2_completion_class=str(semantic_review.get("completion_class", "") or ""),
                latest_semantic_review_result_file=str(semantic_review.get("review_result_file", "") or ""),
                **task_status_projection.as_metadata(),
            )
            if review_subject_kind == "official_output":
                ledger.update_runtime_metadata(
                    task_id,
                    latest_official_review_verdict=task_status_projection.review_verdict,
                    latest_official_review_result_file=str(semantic_review.get("review_result_file", "") or ""),
                    latest_official_review_requires_repair=task_status_projection.task_status == "fail",
                    latest_official_review_detail=detail_text,
                    official_output_quarantine_policy="not_quarantined_by_default",
                )
        if success:
            _clear_current_review_metadata(task_id, ledger)
            _clear_current_review_repair_metadata(task_id, ledger)
            ledger.update_runtime_metadata(task_id, **auto_loop_field_defaults())
        elif disposition.endswith("_invalid_no_promotion"):
            if review_subject_kind != "official_output":
                ledger.update_runtime_metadata(task_id, **auto_loop_field_defaults())
        elif task_status_projection is not None and task_status_projection.task_status == "allowed_exception":
            _clear_current_review_metadata(task_id, ledger)
            _clear_current_review_repair_metadata(task_id, ledger)
            ledger.update_runtime_metadata(task_id, **auto_loop_field_defaults())
        elif repair_ready is not None:
            _clear_current_review_metadata(task_id, ledger)
            _set_current_review_repair_metadata(
                task_id,
                ledger,
                request_file=str(repair_ready.get("request_path", "")),
                summary_file=str(repair_ready.get("summary_path", "")),
                seed_file=str(repair_ready.get("request_payload", {}).get("next_draft_seed_file", "") or ""),
                origin_result_file=str(repair_ready.get("request_payload", {}).get("failed_review_result_file", "") or ""),
            )
        else:
            _clear_current_review_metadata(task_id, ledger)
        if review_subject_kind == "candidate":
            if success:
                ledger.update_runtime_metadata(
                    task_id,
                    pack_candidate_state="draft",
                    latest_build_ready_candidate_kind="",
                    latest_build_ready_candidate_file="",
                    latest_build_ready_candidate_hash="",
                )
            elif disposition.endswith("_no_promotion"):
                ledger.update_runtime_metadata(task_id, pack_candidate_state="review_rejected")
            completion_status = _review_completion_status(
                semantic_review,
                ledger.ledger.get("tasks", {}).get(task_id, {}),
                task_status_projection,
            )
            if success:
                ledger.update_status(task_id, completion_status)
            elif existing_completed_output:
                ledger.update_status(task_id, TaskStatus(apply_original_status))
            elif failure_counters.review_fail_counter >= failure_counters.limit:
                ledger.update_status(task_id, TaskStatus.FAILED_LOCAL, error=detail_text)
            else:
                ledger.update_status(task_id, TaskStatus.PACKED)
        else:
            if success:
                ledger.update_status(
                    task_id,
                    _review_completion_status(
                        semantic_review,
                        ledger.ledger.get("tasks", {}).get(task_id, {}),
                        task_status_projection,
                    ),
                )
            elif disposition == "official_output_review_fail":
                if apply_original_status:
                    try:
                        ledger.update_status(task_id, TaskStatus(apply_original_status))
                    except ValueError:
                        pass
                else:
                    ledger.update_status(task_id, TaskStatus.PACKED)
            elif apply_original_status:
                try:
                    ledger.update_status(task_id, TaskStatus(apply_original_status))
                except ValueError:
                    pass
        refresh_pack_runtime_view(task, ledger, settings, pack_dir)
        if success and review_subject_kind in {"candidate", "official_output", "existing_support"}:
            post_apply_basis = build_semantic_review_basis(
                task,
                ledger,
                settings,
                review_subject_kind=review_subject_kind,
                review_subject_hash=review_subject_hash,
                review_subject_file=candidate_path,
                materialize_proof_obligations=False,
            )
            ledger.update_runtime_metadata(
                task_id,
                latest_applied_review_subject_hash=review_subject_hash,
                latest_applied_review_origin_basis_hash=str(review_input.get("review_basis_hash", "") or ""),
                latest_applied_review_post_basis_hash=sha256_json(post_apply_basis),
                latest_applied_review_input_hash=str(normalized_review.get("review_input_hash", "") or ""),
                latest_applied_review_result_file=str(normalized_review.get("review_result_file", "") or ""),
                latest_applied_review_result_hash=sha256_json(normalized_review),
                latest_applied_review_subject_kind=review_subject_kind,
            )
        return ApplyOutcome(success=success, detail=detail_text, disposition=disposition, next_action=next_action, repair_ready=repair_ready)

    validation_error = ""
    if not isinstance(review_input.get("task"), dict):
        validation_error = "review input task must be a JSON object"
    elif not isinstance(review_input.get("candidate"), dict):
        validation_error = "review input candidate must be a JSON object"
    input_task_id = canonicalize_block_id(str(review_task_payload.get("block_id", "") or ""))
    if not validation_error and input_task_id != task_id:
        validation_error = f"review input task id mismatch: expected {task_id}, got {input_task_id}"
    result_task_id = canonicalize_block_id(str(raw_result.get("task_id", "") if isinstance(raw_result, dict) else ""))
    if not validation_error and result_task_id and result_task_id != task_id:
        validation_error = f"review result task id mismatch: expected {task_id}, got {result_task_id}"
    if not validation_error and not _review_version_matches(review_input.get("prompt_version"), SEMANTIC_REVIEW_PROMPT_VERSION):
        validation_error = "review input prompt_version does not match current semantic review prompt version"
    if not validation_error and not _review_version_matches(review_input.get("rubric_version"), SEMANTIC_REVIEW_RUBRIC_VERSION):
        validation_error = "review input rubric_version does not match current semantic review rubric version"
    if isinstance(raw_result, dict):
        if not validation_error and not _review_version_matches(raw_result.get("prompt_version"), SEMANTIC_REVIEW_PROMPT_VERSION):
            validation_error = "review result prompt_version does not match current semantic review prompt version"
        if not validation_error and not _review_version_matches(raw_result.get("rubric_version"), SEMANTIC_REVIEW_RUBRIC_VERSION):
            validation_error = "review result rubric_version does not match current semantic review rubric version"
        expected_candidate_hash = str(review_candidate_payload.get("hash", "") or "")
        result_candidate_hash = str(raw_result.get("candidate_hash", "") or "")
        if not validation_error and result_candidate_hash != expected_candidate_hash:
            validation_error = "review result candidate hash does not match semantic review input candidate hash"
    elif not validation_error:
        validation_error = "review result is not a JSON object"
    already_promoted = not validation_error and already_promoted_candidate_review()
    if not validation_error:
        validation_error, freshness = _validate_review_input_freshness(
            task=task,
            ledger=ledger,
            settings=settings,
            pack_dir=pack_dir,
            review_input=review_input,
            allow_promoted_candidate=already_promoted,
        )
        if not validation_error:
            review_subject_kind = str(freshness.get("review_subject_kind", review_subject_kind))
            candidate_path = Path(str(freshness.get("subject_file_path", candidate_path)))
            candidate_code = str(freshness.get("candidate_code", candidate_code))
            review_subject_hash = str(freshness.get("current_review_subject_hash", review_subject_hash))

    if not validation_error and already_promoted:
        return ApplyOutcome(
            success=True,
            detail="Codex semantic review already promoted; no changes made.",
            disposition="codex_review_already_promoted",
        )

    verdict = str(normalized_review.get("verdict", "inconclusive"))
    cache_class = str(normalized_review.get("cache_class", "semantic_verdict") or "semantic_verdict").strip().lower()
    detail = str(normalized_review.get("normalization_reason", "") or normalized_review.get("summary", "") or f"Codex review verdict: {verdict}")
    if validation_error:
        return ApplyOutcome(
            success=False,
            detail=validation_error,
            disposition="codex_review_invalid_no_promotion",
        )
    if cache_class != "semantic_verdict":
        invalid_reason = validation_error or detail or "invalid reviewer output"
        return ApplyOutcome(
            success=False,
            detail=invalid_reason,
            disposition="codex_review_invalid_no_promotion",
        )
    normalized_review, task_status_projection = _review_with_task_status(task_id, task, normalized_review)
    normalized_review = _write_normalized_codex_review_artifacts(pack_dir, review_input, normalized_review)
    obligation_update_path = Path(proof_obligations_file) if proof_obligations_file else proof_obligation_path(pack_dir)
    if output_binding.is_obligation_task:
        seed_focused_child_obligations_from_review(
            obligation_update_path,
            normalized_review,
            focus_obligation_ids=output_binding.focus_obligation_ids,
            owner_obligations_path=output_binding.proof_obligations_file,
        )
    updated_obligations = apply_obligation_review_to_file(obligation_update_path, normalized_review)
    if updated_obligations:
        obligation_owner_task_id = canonicalize_block_id(str(updated_obligations.get("task_id", "") or task_id))
        ledger.update_runtime_metadata(
            obligation_owner_task_id,
            proof_obligations_file=str(obligation_update_path),
            proof_obligation_summary=summarize_proof_obligations(updated_obligations),
        )
    if verdict != "pass":
        diagnostics = review_diagnostics(normalized_review)
        if review_subject_kind == "official_output":
            disposition = "official_output_review_fail" if verdict == "fail" else "official_output_review_inconclusive"
        else:
            disposition = "codex_review_fail_no_promotion" if verdict == "fail" else "codex_review_inconclusive_no_promotion"
        repair_seed_path = candidate_path
        if review_subject_kind == "official_output" and verdict == "fail":
            ledger.update_runtime_metadata(
                task_id,
                latest_official_review_verdict=verdict,
                latest_official_review_result_file=str(result_path),
                latest_official_review_requires_repair=True,
                latest_official_review_detail=detail,
                official_output_quarantine_policy="not_quarantined_by_default",
            )
        repair_ready = _write_review_repair_artifacts(
            task=task,
            ledger=ledger,
            settings=settings,
            pack_dir=pack_dir,
            review_input=review_input,
            review_result=normalized_review,
            failed_review_input_file=Path(str(normalized_review.get("review_input_file", review_input_path or ""))),
            failed_review_result_file=Path(str(normalized_review.get("review_result_file", result_path))),
            failed_review_report_file=Path(str(normalized_review.get("review_report_file", pack_dir / "semantic_review_report.json"))),
            failed_review_subject_file=candidate_path,
            next_draft_seed_file=repair_seed_path,
            origin_review_mode="review-apply",
        )
        triage = repair_ready.get("request_payload", {}).get("semantic_fail_triage", {}) if isinstance(repair_ready, dict) else {}
        needs_diagnoser = bool(isinstance(triage, dict) and triage.get("needs_diagnoser", False))
        failure_detail = detail
        if needs_diagnoser:
            prompt_path = str(triage.get("prompt_path", "") or "").strip()
            prompt_note = f" Diagnoser prompt: {prompt_path}" if prompt_path else ""
            failure_detail = (
                f"{detail} Semantic-fail triage requires read-only diagnoser before ordinary repair."
                f"{prompt_note}"
            )
        return finish(
            success=False,
            detail_text=failure_detail,
            diagnostics=diagnostics,
            semantic_review=normalized_review,
            disposition=disposition,
            state_transition="none" if (existing_completed_output or review_subject_kind == "official_output") else "review_apply_to_failed_local",
            repair_ready=repair_ready,
            next_action="diagnoser" if needs_diagnoser else "review_fix",
        )
    if task_status_projection.task_status != "pass":
        detail_text = (
            f"{detail} Task status: {task_status_projection.task_status} ({task_status_projection.reason}). "
            f"Non-clean apply: review verdict is pass, but phase2_status={task_status_projection.task_status}; "
            "this result is recorded for repair/report and is not landed as completion."
        )
        repair_ready = None
        if task_status_projection.task_status == "fail":
            repair_ready = _write_review_repair_artifacts(
                task=task,
                ledger=ledger,
                settings=settings,
                pack_dir=pack_dir,
                review_input=review_input,
                review_result=normalized_review,
                failed_review_input_file=Path(str(normalized_review.get("review_input_file", review_input_path or ""))),
                failed_review_result_file=Path(str(normalized_review.get("review_result_file", result_path))),
                failed_review_report_file=Path(
                    str(normalized_review.get("review_report_file", pack_dir / "semantic_review_report.md"))
                ),
                failed_review_subject_file=candidate_path,
                next_draft_seed_file=candidate_path,
                origin_review_mode="review-apply",
            )
        return finish(
            success=False,
            detail_text=detail_text,
            diagnostics=hard_check_diagnostic("phase2_status_not_pass", task_status_projection.reason),
            semantic_review=normalized_review,
            disposition=f"codex_review_pass_{task_status_projection.task_status}_no_promotion",
            state_transition="none" if (existing_completed_output or review_subject_kind == "official_output") else "review_apply_no_completion",
            repair_ready=repair_ready,
            next_action="review_fix" if task_status_projection.task_status == "fail" else "repair_dependency_gate",
        )
    if review_subject_kind == "official_output":
        if not output_binding.is_obligation_task:
            # Apply-gate build re-verification. The existing official output was
            # sanity-built at review-prep, but the freshness gate only ties the
            # output file's own hash, not its imports: a dependency that changed
            # after prep can leave the recorded output un-buildable while the
            # subject hash is unchanged. Re-run the module build now so we never
            # land COMPLETED on top of a stale pass. On failure we do not demote
            # the official output (mirrors the existing-output review-fail
            # policy); we record repair-required and refuse the clean landing.
            apply_build_success, apply_build_output = run_official_module_build(task_id, settings)
            if not apply_build_success:
                diagnostics = parse_diagnostics(apply_build_output, "final_build_failed", "apply_official_output_build")
                fail_detail = (
                    apply_build_output
                    or f"lake build ToyApollo.Output.{task_id} failed at review-apply."
                )
                outcome = finish(
                    success=False,
                    detail_text=(
                        f"{fail_detail} Existing official output rebuilt unclean at review-apply; "
                        "not landed as completion and not demoted (repair required)."
                    ),
                    diagnostics=diagnostics,
                    semantic_review=normalized_review,
                    disposition="official_output_apply_build_failed",
                    state_transition="none",
                    final_build_success=False,
                    final_build_output=apply_build_output,
                )
                # finish() recomputes latest_official_review_requires_repair from
                # the (passing) semantic verdict; the apply-time build failure
                # must still flag repair, so set it after finish() wrote metadata.
                ledger.update_runtime_metadata(
                    task_id,
                    latest_official_review_requires_repair=True,
                    latest_official_apply_build_failed=True,
                    latest_official_apply_build_detail=fail_detail,
                    official_output_quarantine_policy="not_quarantined_by_default",
                )
                return outcome
        ledger.register_success(task_id, candidate_code, ledger._hash_text(candidate_code))
        if output_binding.is_obligation_task:
            ledger.update_runtime_metadata(task_id, obligation_task_state="closed")
            reconcile_obligation_tasks_for_task(output_binding.output_owner_task_id, ledger, settings)
        rebuilt = not output_binding.is_obligation_task
        return finish(
            success=True,
            detail_text=(
                "Semantic review passed; existing official output rebuilt cleanly at review-apply."
                if rebuilt else
                "Semantic review passed for the existing runnable official output (obligation task; apply-time build skipped)."
            ),
            diagnostics=[],
            semantic_review=normalized_review,
            disposition="official_output_review_pass",
            state_transition="none",
            final_build_success=True,
            final_build_output=(
                "Existing official output rebuilt at review-apply."
                if rebuilt else
                "Existing official output was already validated before review."
            ),
        )
    if review_subject_kind == "existing_support":
        if output_binding.is_obligation_task:
            # Obligation support landing is the dormant path; leave it unchanged
            # and skip the apply-time build (obligation handling is scoped out of
            # this fix).
            ledger.update_status(task_id, TaskStatus.COMPLETED)
            ledger.update_runtime_metadata(task_id, obligation_task_state="closed")
            reconcile_obligation_tasks_for_task(output_binding.output_owner_task_id, ledger, settings)
        else:
            # Apply-gate build re-verification for a non-obligation support
            # landing. The recorded review subject is a snapshot, not a live
            # module, so resolve the real landing module from the obligations
            # file and rebuild it before landing COMPLETED. On failure: do not
            # land completion (the task stays at its pre-apply status).
            support_target = support_review_target_from_obligations(pack_dir, settings)
            support_module = str(support_target.get("module", "") or "")
            if not support_module:
                return finish(
                    success=False,
                    detail_text=(
                        "Existing support landing module could not be resolved from "
                        "proof_obligations.json at review-apply; support landing not completed."
                    ),
                    diagnostics=hard_check_diagnostic("support_module_unresolved", "missing landing_module"),
                    semantic_review=normalized_review,
                    disposition="existing_support_apply_module_unresolved",
                    state_transition="none",
                )
            apply_build_success, apply_build_output = run_lean_module_build(support_module, settings)
            if not apply_build_success:
                diagnostics = parse_diagnostics(apply_build_output, "final_build_failed", "apply_support_build")
                return finish(
                    success=False,
                    detail_text=(
                        apply_build_output
                        or f"lake build {support_module} failed at review-apply; support landing not completed."
                    ),
                    diagnostics=diagnostics,
                    semantic_review=normalized_review,
                    disposition="existing_support_apply_build_failed",
                    state_transition="none",
                    final_build_success=False,
                    final_build_output=apply_build_output,
                )
        rebuilt = not output_binding.is_obligation_task
        return finish(
            success=True,
            detail_text=(
                "Semantic review passed; existing support module rebuilt cleanly at review-apply."
                if rebuilt else
                "Semantic review passed for the existing support landing (obligation task; apply-time build skipped)."
            ),
            diagnostics=[],
            semantic_review=normalized_review,
            disposition="existing_support_review_pass",
            state_transition="completed",
            final_build_success=True,
            final_build_output=(
                "Existing support module rebuilt at review-apply."
                if rebuilt else
                "Existing support module was already validated before review."
            ),
        )

    final_success, final_output = run_staged_official_build(
        task_id, source_plan, settings, pack_dir, candidate_code,
        attempt=int(review_input.get("attempt") or 0) or 1,
        mode="review-apply",
        restore_on_success=output_binding.is_obligation_task,
        output_owner_task_id=output_binding.output_owner_task_id,
    )
    if not final_success:
        diagnostics = parse_diagnostics(final_output, "final_build_failed", "final_build")
        return finish(
            success=False,
            detail_text=final_output or f"lake build ToyApollo.Output.{task_id} failed after Codex review pass.",
            diagnostics=diagnostics,
            semantic_review=normalized_review,
            disposition="codex_review_apply_final_build_failed",
            state_transition="none" if existing_completed_output else "review_apply_to_failed_local",
            final_build_success=False,
            final_build_output=final_output,
        )

    if output_binding.is_obligation_task:
        ledger.update_status(task_id, TaskStatus.COMPLETED)
        reconcile_obligation_tasks_for_task(output_binding.output_owner_task_id, ledger, settings)
    else:
        ledger.register_success(task_id, candidate_code, ledger._hash_text(candidate_code))
    return finish(
        success=True,
        detail_text="Codex semantic review passed; candidate promoted and final build succeeded.",
        diagnostics=[],
        semantic_review=normalized_review,
        disposition="codex_review_pass_promoted",
        state_transition="completed",
        final_build_success=True,
        final_build_output=final_output,
    )


async def apply_codex_review_result(
    task_id: str,
    ledger: LedgerManager,
    settings,
    review_result_arg: str,
) -> tuple[bool, str]:
    outcome = await apply_codex_review_result_once(task_id, ledger, settings, review_result_arg)
    return outcome.success, outcome.detail
