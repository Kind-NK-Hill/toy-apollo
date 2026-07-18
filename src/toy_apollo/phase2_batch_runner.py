from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
from typing import Any

from src.block_id_naming import canonicalize_block_id

from .phase2_batch_controller import BatchReport, analyze_batch_state, _task_has_family_consumable_support
from .phase2_math_review_gate import math_review_gate_blocker, math_review_gate_state
from .phase2_pack_shared.io import read_json_safely, sha256_json
from .phase2_pack_generation import resolve_phase2_task
from .phase2_proof_obligations import summarize_proof_obligations
from .phase2_review_decision import evaluate_semantic_review_result
from .phase2_review_request import (
    _load_current_codex_review_request,
    _resolve_review_binding_path,
    _validate_review_input_freshness,
)


DIAGNOSER_RESULT_PREFIX = "diagnoser_result"
DIAGNOSER_RESULT_ALIAS = "diagnoser_result.json"
SOURCE_DECISION_RESOLUTION_FILE = "source_decision_resolution.json"
SOURCE_STATEMENT_RISK_SKIP_TASK_IDS = frozenset({"thm_1_2", "ex_1_3_2"})
DIAGNOSER_RESULT_REQUIRED_FIELDS = frozenset(
    {
        "route_wrong",
        "statement_mismatch",
        "local_repair_allowed",
        "recommended_next_action",
    }
)


@dataclass(frozen=True)
class BatchRunnerAction:
    task_id: str
    action: str
    command: str
    reason: str
    task_kind: str = ""
    fanout: int = 0
    conflict_group: str = ""
    worker_slot: int = 0


@dataclass(frozen=True)
class BatchRunnerPlan:
    report: BatchReport
    actions: tuple[BatchRunnerAction, ...]
    all_actions: tuple[BatchRunnerAction, ...] = ()
    hidden_actions: tuple[BatchRunnerAction, ...] = ()


@dataclass(frozen=True)
class BatchRunnerExecution:
    plan: BatchRunnerPlan
    executed: tuple[BatchRunnerAction, ...]
    details: tuple[str, ...]


def build_live_batch_state(task_ids: list[str], ledger, settings=None, *, batch_id: str = "live-ledger") -> dict[str, Any]:
    """Project current ledger rows into the batch-controller input shape.

    This is intentionally read-only. Completion authority remains build/review/apply;
    this helper only makes the existing state schedulable.
    """
    records = getattr(ledger, "ledger", {}).get("tasks", {})
    tasks: list[dict[str, Any]] = []
    for raw_task_id in task_ids:
        task_id = canonicalize_block_id(str(raw_task_id or ""))
        if not task_id:
            continue
        record = records.get(task_id, {})
        if not isinstance(record, dict):
            record = {}
        tasks.append(
            _batch_task_from_ledger_record(
                task_id,
                record,
                ledger=ledger,
                settings=settings,
                all_records=records,
            )
        )
    return {"batch_id": batch_id, "tasks": tasks}


def plan_batch_from_ledger(
    task_ids: list[str],
    ledger,
    settings,
    *,
    objective: str = "textbook-complete",
    task_kinds: list[str] | tuple[str, ...] | None = None,
    limit: int | None = None,
    worker_slots: int = 0,
    include_legacy: bool = False,
) -> BatchRunnerPlan:
    state = build_live_batch_state(task_ids, ledger, settings)
    report = analyze_batch_state(state, objective=objective)
    raw_tasks = {str(task.get("task_id", "")): task for task in state.get("tasks", []) if isinstance(task, dict)}
    _augment_raw_tasks_with_dependency_records(raw_tasks, ledger, settings)
    fanout = _transitive_fanout(raw_tasks)
    all_actions = tuple(
        _action_for_row(
            row,
            settings,
            raw_tasks.get(row.task_id, {}),
            fanout.get(row.task_id, 0),
            raw_tasks=raw_tasks,
            ledger=ledger,
        )
        for row in report.rows
    )
    visible_actions, hidden_actions = _partition_default_visible_actions(
        all_actions,
        include_legacy=include_legacy,
    )
    actions = _select_worker_queue(
        visible_actions,
        task_kinds=task_kinds or (),
        limit=limit,
        worker_slots=worker_slots,
    )
    return BatchRunnerPlan(
        report=report,
        actions=actions,
        all_actions=all_actions,
        hidden_actions=hidden_actions,
    )


def render_batch_runner_plan(plan: BatchRunnerPlan) -> str:
    lines = [
        "# Phase2 Batch Runner Plan",
        "",
        f"- batch_id: `{plan.report.batch_id}`",
        f"- objective: `{plan.report.objective}`",
        f"- all_clean_or_allowed_exception: `{str(plan.report.all_clean_or_allowed_exception).lower()}`",
        _hidden_actions_summary_line(plan.hidden_actions),
        f"- ordinary_action_queue_clear: `{str(not plan.actions).lower()}`",
        _source_statement_risk_exceptions_summary_line(plan.hidden_actions),
        "",
        "| worker | task_id | kind | fanout | conflict_group | phase2_status | report_status | action | command | reason |",
        "|---:|---|---|---:|---|---|---|---|---|---|",
    ]
    rows = {row.task_id: row for row in plan.report.rows}
    for action in plan.actions:
        row = rows[action.task_id]
        lines.append(
            "| {worker} | {task_id} | {kind} | {fanout} | {conflict_group} | {phase2_status} | {report_status} | {action} | {command} | {reason} |".format(
                worker=action.worker_slot or "",
                task_id=action.task_id,
                kind=action.task_kind or "",
                fanout=action.fanout,
                conflict_group=action.conflict_group or "",
                phase2_status=row.task_status or "",
                report_status=row.report_status or "",
                action=action.action,
                command=action.command.replace("|", "\\|"),
                reason=action.reason.replace("|", "\\|"),
            )
        )
    if not plan.actions:
        hidden_actions = set(plan.hidden_actions)
        dispatch_required = [
            action
            for action in plan.all_actions
            if action not in hidden_actions
            if action.action
            in {
                "reviewer_required",
                "diagnoser_required",
                "math_review_gate_required",
                "blocking_proof_required",
                "source_statement_decision_required",
                "foundation_absorb_required",
            }
        ]
        if dispatch_required:
            counts = {
                "reviewer_required": sum(1 for action in dispatch_required if action.action == "reviewer_required"),
                "diagnoser_required": sum(1 for action in dispatch_required if action.action == "diagnoser_required"),
                "math_review_gate_required": sum(
                    1 for action in dispatch_required if action.action == "math_review_gate_required"
                ),
                "blocking_proof_required": sum(
                    1 for action in dispatch_required if action.action == "blocking_proof_required"
                ),
                "source_statement_decision_required": sum(
                    1 for action in dispatch_required if action.action == "source_statement_decision_required"
                ),
                "foundation_absorb_required": sum(
                    1 for action in dispatch_required if action.action == "foundation_absorb_required"
                ),
            }
            summary = ", ".join(
                f"{key}={value}" for key, value in counts.items() if value
            )
            lines.extend(
                [
                    "",
                    f"> subagent-dispatch-required: `{summary}`. The worker queue has no ordinary author actions; inspect the unfiltered plan and dispatch independent read-only reviewer/diagnoser/math-review subagents, resolve source/statement decisions, or absorb proof obligations into the parent/support family.",
                ]
            )
    lines.append("")
    return "\n".join(lines)


async def run_batch_actions(
    task_ids: list[str],
    ledger,
    settings,
    *,
    max_actions: int = 1,
    objective: str = "textbook-complete",
    task_kinds: list[str] | tuple[str, ...] | None = None,
    limit: int | None = None,
    worker_slots: int = 0,
    include_legacy: bool = False,
) -> BatchRunnerExecution:
    """Execute a small number of actions selected by the live batch plan.

    This is deliberately a thin dispatcher over existing single-task Phase2
    actions. It does not decide completion and does not hand-edit ledger state.
    """
    if max_actions < 1:
        raise ValueError("max_actions must be at least 1")

    from .phase2_review_loop import run_codex_auto_loop, run_codex_review_now

    plan = plan_batch_from_ledger(
        task_ids,
        ledger,
        settings,
        objective=objective,
        task_kinds=task_kinds,
        limit=limit,
        worker_slots=worker_slots,
        include_legacy=include_legacy,
    )
    executed: list[BatchRunnerAction] = []
    details: list[str] = []
    for action in plan.actions:
        if len(executed) >= max_actions:
            break
        if action.action == "review_existing":
            success, detail = await run_codex_review_now(
                action.task_id,
                ledger,
                settings,
                review_subject="existing",
                auto_apply_pass=False,
            )
        elif action.action == "auto_loop":
            success, detail = await run_codex_auto_loop(
                action.task_id,
                ledger,
                settings,
                review_subject="current",
            )
        else:
            continue
        executed.append(action)
        details.append(("PASS: " if success else "FAIL: ") + detail)
    return BatchRunnerExecution(plan=plan, executed=tuple(executed), details=tuple(details))


def _batch_task_from_ledger_record(
    task_id: str,
    record: dict[str, Any],
    *,
    ledger=None,
    settings=None,
    all_records: dict[str, Any] | None = None,
) -> dict[str, Any]:
    all_records = all_records if isinstance(all_records, dict) else {}
    pack_dir = _task_pack_dir(task_id, settings)
    current_review_result, current_review_result_path = _current_review_result_binding_from_record(
        record,
        pack_dir=pack_dir,
    )
    review_authority = _current_review_authority_projection(
        task_id,
        record,
        ledger=ledger,
        settings=settings,
        pack_dir=pack_dir,
        review_result=current_review_result,
        review_result_path=current_review_result_path,
    )
    proof_obligations = _proof_obligations_from_pack(task_id, settings)
    proof_obligation_summary = (
        summarize_proof_obligations(proof_obligations)
        if proof_obligations is not None
        else record.get("proof_obligation_summary", {})
    )
    review_verdict = review_authority.get("phase2_review_verdict", "") if review_authority else (
        record.get("phase2_review_verdict", "")
        or record.get("review_verdict", "")
        or record.get("current_review_verdict", "")
        or current_review_result.get("verdict", "")
    )
    proof_class = review_authority.get("phase2_proof_class", "") if review_authority else (
        record.get("phase2_proof_class", "")
        or record.get("proof_class", "")
        or current_review_result.get("proof_class", "")
        or record.get("completion_class", "")
        or current_review_result.get("completion_class", "")
    )
    completion_class = review_authority.get("phase2_completion_class", "") if review_authority else (
        record.get("phase2_completion_class", "")
        or record.get("completion_class", "")
        or current_review_result.get("completion_class", "")
    )
    return {
        "task_id": task_id,
        "status": record.get("status", ""),
        "type": record.get("type", record.get("task_type", "")),
        "dependencies": _dependencies_from_record(record, task_id=task_id, settings=settings),
        "pack_dir": str(_task_pack_dir(task_id, settings)),
        "phase2_status": review_authority.get(
            "phase2_status",
            record.get("phase2_status", record.get("phase2_task_status", "")),
        ),
        "phase2_status_reason": review_authority.get("phase2_status_reason") or record.get(
            "phase2_status_reason",
            record.get("phase2_task_status_reason", ""),
        ),
        "phase2_status_evidence_type": review_authority.get("phase2_status_evidence_type") or record.get(
            "phase2_status_evidence_type",
            record.get("phase2_task_status_evidence_type", ""),
        ),
        "phase2_review_verdict": review_verdict,
        "review_verdict": review_verdict,
        "phase2_proof_class": proof_class,
        "proof_class": proof_class,
        "phase2_completion_class": completion_class,
        "completion_class": completion_class,
        "current_class": record.get("current_class", ""),
        "stop_reason": record.get("stop_reason", record.get("current_auto_loop_stop_reason", "")),
        "current_auto_loop_phase": record.get("current_auto_loop_phase", ""),
        "current_auto_loop_status": record.get("current_auto_loop_status", ""),
        "current_review_request_file": record.get("current_review_request_file", ""),
        "current_review_expected_result_file": record.get("current_review_expected_result_file", ""),
        "proof_obligation_summary": proof_obligation_summary,
        "proof_obligations": proof_obligations if proof_obligations is not None else record.get("proof_obligations", {}),
        "failure_events": record.get("failure_events", []),
        "build_fail_counter": record.get("build_fail_counter", 0),
        "review_fail_counter": record.get("review_fail_counter", 0),
        "latest_verify_result_file": record.get("latest_verify_result_file", ""),
        "latest_verify_failure": _latest_verify_failure(record.get("latest_verify_result_file", "")),
        "latest_semantic_fail_triage_file": record.get("latest_semantic_fail_triage_file", ""),
        "latest_semantic_fail_triage_category": record.get("latest_semantic_fail_triage_category", ""),
        "latest_semantic_fail_triage_needs_diagnoser": record.get(
            "latest_semantic_fail_triage_needs_diagnoser",
            False,
        ),
        "latest_semantic_fail_triage_local_repair_allowed": record.get(
            "latest_semantic_fail_triage_local_repair_allowed",
            False,
        ),
        "latest_math_proof_skeleton_file": record.get("latest_math_proof_skeleton_file", ""),
        "latest_math_proof_skeleton_hash": record.get("latest_math_proof_skeleton_hash", ""),
        "latest_math_review_result_file": record.get("latest_math_review_result_file", ""),
        "latest_math_review_result_hash": record.get("latest_math_review_result_hash", ""),
        "latest_math_review_verdict": record.get("latest_math_review_verdict", ""),
        "latest_diagnoser_prompt_file": record.get("latest_diagnoser_prompt_file", ""),
        "latest_candidate_file": record.get("latest_candidate_file", ""),
        "latest_build_candidate_file": record.get("latest_build_candidate_file", ""),
        "latest_build_ready_candidate_file": record.get("latest_build_ready_candidate_file", ""),
        "draft_file": record.get("draft_file", ""),
        "pack_candidate_state": record.get("pack_candidate_state", ""),
        "parent_task_id": record.get("parent_task_id", ""),
        "target_task_id": record.get("target_task_id", ""),
        "parent_block_id": record.get("parent_block_id", ""),
        "obligation_id": record.get("obligation_id", ""),
        "obligation_child_task_ids": _obligation_child_task_ids(task_id, all_records),
        "obligation_child_fingerprints": _obligation_child_fingerprints(task_id, all_records),
    }


def _current_review_result_binding_from_record(
    record: dict[str, Any],
    *,
    pack_dir: Path,
) -> tuple[dict[str, Any], Path | None]:
    for key in (
        "current_review_expected_result_file",
        "latest_semantic_review_result_file",
        "latest_official_review_result_file",
    ):
        raw_path = str(record.get(key, "") or "").strip()
        if not raw_path:
            continue
        path = _resolve_review_binding_path(raw_path, pack_dir=pack_dir)
        if not path.is_file():
            continue
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if isinstance(payload, dict):
            return payload, path.resolve()
    return {}, None


def _current_review_result_from_record(record: dict[str, Any], *, pack_dir: Path | None = None) -> dict[str, Any]:
    resolved_pack_dir = pack_dir or Path.cwd()
    payload, _ = _current_review_result_binding_from_record(record, pack_dir=resolved_pack_dir)
    return payload


def _review_freshness_projection(reason: str) -> dict[str, Any]:
    return {
        "phase2_status": "needs_fresh_review",
        "phase2_status_reason": reason,
        "phase2_status_evidence_type": "freshness_error",
        "phase2_review_verdict": "",
        "phase2_proof_class": "",
        "phase2_completion_class": "",
    }


def _current_review_authority_projection(
    task_id: str,
    record: dict[str, Any],
    *,
    ledger,
    settings,
    pack_dir: Path,
    review_result: dict[str, Any],
    review_result_path: Path | None,
) -> dict[str, Any]:
    """Revalidate a ledger PASS against the current official review contract.

    The batch scheduler is read-only: it never rewrites review artifacts or the
    ledger. A historical PASS is schedulable as PASS only when its bound input,
    subject, basis, normalized class projection, and review-apply receipt all
    still agree with current state.
    """

    claimed_status = str(record.get("phase2_status", record.get("phase2_task_status", "")) or "").strip().lower()
    if claimed_status not in {"pass", "allowed_exception"}:
        return {}
    if ledger is None or settings is None:
        return _review_freshness_projection("current review freshness cannot be checked without ledger/settings")
    if not review_result or review_result_path is None:
        return _review_freshness_projection("ledger PASS has no readable current official review result")

    raw_input_path = str(review_result.get("review_input_file", "") or "").strip()
    if not raw_input_path:
        return _review_freshness_projection("current review result is missing review_input_file/input binding")
    review_input_path = _resolve_review_binding_path(raw_input_path, pack_dir=pack_dir)
    review_input = read_json_safely(review_input_path, {}) if review_input_path.is_file() else {}
    if not isinstance(review_input, dict) or not review_input:
        return _review_freshness_projection("current review input is missing or invalid")
    task = review_input.get("task", {})
    if not isinstance(task, dict) or str(task.get("block_id", "") or "") != task_id:
        return _review_freshness_projection("current review input task binding is missing or mismatched")

    has_apply_receipt = bool(str(record.get("latest_applied_review_post_basis_hash", "") or "").strip())
    freshness_error, _ = _validate_review_input_freshness(
        task=task,
        ledger=ledger,
        settings=settings,
        pack_dir=pack_dir,
        review_input=review_input,
        allow_promoted_candidate=has_apply_receipt,
    )
    if freshness_error:
        return _review_freshness_projection(freshness_error)

    decision = evaluate_semantic_review_result(
        review_result,
        review_input=review_input,
        runner_metadata={
            "status": "batch_read_only_revalidation",
            "result_file": str(review_result_path),
        },
    )
    projection = decision.task_status_projection
    if projection is None:
        reason = str(decision.result.get("normalization_reason", "") or "current review is not a semantic verdict")
        if "class" in reason.lower():
            return {
                "phase2_status": "fail",
                "phase2_status_reason": reason,
                "phase2_status_evidence_type": "needs_class_normalization",
                "phase2_review_verdict": str(decision.result.get("verdict", "") or ""),
                "phase2_proof_class": "",
                "phase2_completion_class": "",
            }
        return _review_freshness_projection(reason)

    normalized = decision.result
    authority = {
        "phase2_status": projection.task_status,
        "phase2_status_reason": projection.reason,
        "phase2_status_evidence_type": (
            "needs_class_normalization"
            if projection.evidence_type == "class_not_task_pass"
            else projection.evidence_type
        ),
        "phase2_review_verdict": projection.review_verdict,
        "phase2_proof_class": projection.proof_class,
        "phase2_completion_class": str(normalized.get("completion_class", "") or ""),
    }
    if projection.task_status not in {"pass", "allowed_exception"}:
        return authority

    receipt_result_raw = str(record.get("latest_applied_review_result_file", "") or "").strip()
    receipt_result_path = (
        _resolve_review_binding_path(receipt_result_raw, pack_dir=pack_dir).resolve()
        if receipt_result_raw
        else None
    )
    receipt_result_hash = str(record.get("latest_applied_review_result_hash", "") or "")
    receipt_input_hash = str(record.get("latest_applied_review_input_hash", "") or "")
    receipt_subject_kind = str(record.get("latest_applied_review_subject_kind", "") or "")
    if receipt_result_path is None or not receipt_result_path.is_file():
        return _review_freshness_projection("current PASS result has no matching review-apply result receipt")
    if receipt_result_hash != sha256_json(review_result):
        return _review_freshness_projection("current PASS result does not match its review-apply result hash")
    if receipt_input_hash != str(normalized.get("review_input_hash", "") or ""):
        return _review_freshness_projection("current PASS result has no matching review-apply input receipt")
    if receipt_subject_kind != str(review_input.get("review_subject_kind", "") or ""):
        return _review_freshness_projection("current PASS result has no matching review-apply subject-kind receipt")
    if bool(record.get("latest_official_review_requires_repair", False)) or bool(
        record.get("latest_official_apply_build_failed", False)
    ):
        return _review_freshness_projection("current official review receipt is marked repair-required")
    return authority


def _proof_obligations_from_pack(task_id: str, settings=None) -> dict[str, Any] | None:
    path = _task_pack_dir(task_id, settings) / "proof_obligations.json"
    if not path.is_file():
        return None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return payload if isinstance(payload, dict) else None


def _augment_raw_tasks_with_dependency_records(raw_tasks: dict[str, dict[str, Any]], ledger, settings) -> None:
    records = getattr(ledger, "ledger", {}).get("tasks", {})
    if not isinstance(records, dict):
        return
    stack: list[str] = []
    for task in raw_tasks.values():
        if isinstance(task, dict):
            stack.extend(_canonical_dependency_list(task.get("dependencies", [])))
            if str(task.get("type", "") or "") == "Phase2ObligationTask":
                stack.extend(
                    _canonical_dependency_list(
                        [
                            task.get("parent_task_id", ""),
                            task.get("target_task_id", ""),
                            task.get("parent_block_id", ""),
                        ]
                    )
                )
    while stack:
        dep_id = stack.pop()
        if not dep_id or dep_id in raw_tasks:
            continue
        record = records.get(dep_id, {})
        if not isinstance(record, dict):
            continue
        dep_task = _batch_task_from_ledger_record(
            dep_id,
            record,
            ledger=ledger,
            settings=settings,
            all_records=records,
        )
        raw_tasks[dep_id] = dep_task
        stack.extend(_canonical_dependency_list(dep_task.get("dependencies", [])))


def _obligation_child_task_ids(task_id: str, all_records: dict[str, Any]) -> list[str]:
    parent = canonicalize_block_id(task_id)
    if not parent or not isinstance(all_records, dict):
        return []
    prefix = f"obl_{parent}_"
    child_ids: list[str] = []
    for raw_child_id, raw_child in all_records.items():
        child_id = canonicalize_block_id(str(raw_child_id or ""))
        if not child_id:
            continue
        child = raw_child if isinstance(raw_child, dict) else {}
        child_parent = canonicalize_block_id(str(child.get("parent_block_id", "") or ""))
        child_type = str(child.get("type", "") or "")
        if (child_type == "Phase2ObligationTask" and child_parent == parent) or child_id.startswith(prefix):
            child_ids.append(child_id)
    return sorted(set(child_ids))


def _obligation_child_fingerprints(task_id: str, all_records: dict[str, Any]) -> dict[str, str]:
    child_ids = _obligation_child_task_ids(task_id, all_records)
    fingerprints: dict[str, str] = {}
    for child_id in child_ids:
        child = all_records.get(child_id, {})
        if not isinstance(child, dict):
            continue
        fingerprint = str(child.get("obligation_fingerprint", "") or "").strip()
        if fingerprint:
            fingerprints[child_id] = fingerprint
    return fingerprints


def _dependencies_from_record(record: dict[str, Any], *, task_id: str = "", settings=None) -> list[str]:
    pack_dependencies = _pack_manifest_hard_dependencies(task_id, settings)
    if pack_dependencies is not None:
        return _dedupe_dependencies(pack_dependencies, task_id=task_id)

    dependencies: list[str] = []
    for key in (
        "dependencies",
        "selected_dependencies",
        "phase2_dependencies",
        "soft_imports",
        "candidate_soft_imports",
        "final_import_union",
    ):
        raw = record.get(key)
        if isinstance(raw, list):
            dependencies.extend(canonicalize_block_id(str(item)) for item in raw if canonicalize_block_id(str(item)))
    return _dedupe_dependencies(dependencies, task_id=task_id)


def _pack_manifest_hard_dependencies(task_id: str, settings=None) -> list[str] | None:
    if not task_id or settings is None:
        return None
    prompt_root = Path(getattr(settings, "phase2_prompt_packs_dir", "phase2_prompt_packs"))
    task_path = prompt_root / task_id / "task.json"
    payload = read_json_safely(task_path, None)
    if not isinstance(payload, dict):
        return None
    if str(payload.get("type", "") or "").strip() != "Phase2ObligationTask":
        return None
    if "dependencies" not in payload:
        return None
    raw_dependencies = payload.get("dependencies", [])
    if not isinstance(raw_dependencies, list):
        return []
    return [canonicalize_block_id(str(item)) for item in raw_dependencies if canonicalize_block_id(str(item))]


def _dedupe_dependencies(dependencies: list[str], *, task_id: str) -> list[str]:
    selected: list[str] = []
    seen: set[str] = set()
    canonical_task_id = canonicalize_block_id(task_id)
    for dep in dependencies:
        canonical_dep = canonicalize_block_id(str(dep))
        if not canonical_dep or canonical_dep == canonical_task_id or canonical_dep in seen:
            continue
        seen.add(canonical_dep)
        selected.append(canonical_dep)
    return selected


def _promoted_child_obligations_reason(task_id: str, raw_task: dict[str, Any], settings=None) -> str:
    return ""


def _child_obligations_match_current_parent_fingerprints(task_id: str, raw_task: dict[str, Any], settings=None) -> bool:
    obligations = _current_promotable_obligations(task_id, settings)
    if not obligations:
        return False
    child_fingerprints = raw_task.get("obligation_child_fingerprints", {})
    if not isinstance(child_fingerprints, dict):
        return False
    parent = canonicalize_block_id(task_id)
    for obligation in obligations:
        obligation_id = str(obligation.get("id", "") or "").strip()
        if not obligation_id:
            return False
        child_id = _obligation_task_id(parent, obligation_id)
        current_fingerprint = _obligation_fingerprint(parent, obligation)
        if child_fingerprints.get(child_id) != current_fingerprint:
            return False
    return True


def _current_promotable_obligations(task_id: str, settings=None) -> list[dict[str, Any]]:
    path = _task_pack_dir(task_id, settings) / "proof_obligations.json"
    if not path.is_file():
        return []
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return []
    if not isinstance(payload, dict):
        return []
    raw_obligations = payload.get("obligations", [])
    if not isinstance(raw_obligations, list):
        return []
    return [
        obligation
        for obligation in raw_obligations
        if isinstance(obligation, dict) and _is_promotable_obligation(obligation)
    ]


def _is_promotable_obligation(obligation: dict[str, Any]) -> bool:
    status = str(obligation.get("status", "") or "").strip().lower()
    return status in {"accepted_as_proof_debt", "open", "partial", "blocked", "in_progress"}


def _obligation_task_id(parent_task_id: str, obligation_id: str) -> str:
    parent = canonicalize_block_id(parent_task_id)
    raw_obligation = re.sub(r"[^A-Za-z0-9_]+", "_", str(obligation_id or "")).strip("_").lower()
    raw_obligation = re.sub(r"_+", "_", raw_obligation) or "obligation"
    return canonicalize_block_id(f"obl_{parent}_{raw_obligation}")


def _obligation_fingerprint(parent_task_id: str, obligation: dict[str, Any]) -> str:
    payload = {
        "parent_task_id": parent_task_id,
        "id": obligation.get("id", ""),
        "kind": obligation.get("kind", ""),
        "source_ref": obligation.get("source_ref", ""),
        "lean_landing": obligation.get("lean_landing", ""),
        "notes": obligation.get("notes", ""),
        "depends_on": obligation.get("depends_on", []),
        "scaffold_hypotheses": obligation.get("scaffold_hypotheses", []),
        "source_output_alignment": obligation.get("source_output_alignment", {}),
    }
    raw = json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()


def _action_for_row(
    row,
    settings,
    raw_task: dict[str, Any] | None = None,
    fanout: int = 0,
    raw_tasks: dict[str, dict[str, Any]] | None = None,
    ledger=None,
) -> BatchRunnerAction:
    raw_task = raw_task if isinstance(raw_task, dict) else {}
    raw_tasks = raw_tasks if isinstance(raw_tasks, dict) else {}
    task_kind = _task_kind(row.task_id, raw_task)
    conflict_group = f"task:{row.task_id}"
    def action(name: str, command: str, reason: str) -> BatchRunnerAction:
        return BatchRunnerAction(
            row.task_id,
            name,
            command,
            reason,
            task_kind=task_kind,
            fanout=fanout,
            conflict_group=conflict_group,
        )

    if row.clean_or_allowed_exception:
        return action("none", "", "task is already clean or an explicit allowed exception")
    if row.task_status_evidence_type == "obl_absorption_manual_fail":
        return action(
            "foundation_absorb_required",
            "",
            row.task_status_reason
            or "former obligation content was absorbed into the parent/support file and must be reviewed there",
        )
    if row.task_status == "fail" and _task_has_family_consumable_support(raw_task):
        return action(
            "inspect",
            "",
            "family support is covered, but direct downstream obligations remain open",
        )
    if row.blocked_dependency:
        return action(
            "skip_blocked",
            "",
            f"blocked by upstream task {row.blocked_dependency}",
        )
    if row.proof_debt_dependency:
        return action(
            "skip_blocked",
            "",
            f"blocked by upstream proof debt {row.proof_debt_dependency}",
        )
    nonconsumable_debt_dependency = _first_nonconsumable_proof_debt_dependency(row.task_id, raw_tasks)
    if nonconsumable_debt_dependency:
        return action(
            "skip_blocked",
            "",
            f"blocked by upstream accepted proof debt {nonconsumable_debt_dependency}",
        )
    diagnoser_dependency = _first_diagnoser_required_dependency(row.task_id, raw_tasks)
    if diagnoser_dependency:
        return action(
            "skip_blocked",
            "",
            f"blocked by upstream diagnoser-required semantic failure {diagnoser_dependency}",
        )
    parent_statement_decision = _parent_source_statement_decision_required(raw_task, raw_tasks, settings)
    if parent_statement_decision:
        return action(
            "skip_blocked",
            "",
            f"blocked by parent source/statement decision {parent_statement_decision}",
        )
    if row.task_status == "blocked":
        return action("blocked", "", row.task_status_reason or "dependency gate blocked")
    reviewer_reason, stale_request_reason = _reviewer_required_blocker(
        row.task_id,
        raw_task,
        ledger=ledger,
        settings=settings,
    )
    if reviewer_reason:
        return action("reviewer_required", "", reviewer_reason)
    if stale_request_reason and _official_output_exists(settings, row.task_id):
        return action(
            "review_existing",
            _phase2_command("review-now", row.task_id, "--review-subject existing"),
            f"stale pending review request: {stale_request_reason}",
        )
    verify_failure = raw_task.get("latest_verify_failure", {})
    verify_disposition = (
        str(verify_failure.get("disposition", "") or "").strip()
        if isinstance(verify_failure, dict)
        else ""
    )
    verify_summary = (
        str(verify_failure.get("summary", "") or "").strip()
        if isinstance(verify_failure, dict)
        else ""
    )
    if (
        row.report_status == "needs_fresh_review"
        and row.task_status_evidence_type == "freshness_error"
        and verify_disposition in {"", "review_existing_required", "codex_review_required"}
        and _official_output_exists(settings, row.task_id)
    ):
        return action(
            "review_existing",
            _phase2_command("review-now", row.task_id, "--review-subject existing"),
            verify_summary
            if verify_disposition == "review_existing_required" and verify_summary
            else row.task_status_reason
            or "the previous review binding is stale; generate a fresh existing-output review",
        )
    diagnoser_result = _load_diagnoser_result(raw_task)
    stop_requires_diagnoser = str(raw_task.get("stop_reason", "") or "").strip().lower() == "diagnoser_required"
    if stop_requires_diagnoser and not diagnoser_result:
        return action("diagnoser_required", "", "auto-loop stopped because read-only diagnoser is required")
    diagnoser_reason = _semantic_fail_triage_blocker(raw_task)
    if diagnoser_reason:
        return action("diagnoser_required", "", diagnoser_reason)
    diagnoser_author_reason = _diagnoser_result_author_reason(
        raw_task,
        diagnoser_result,
        stop_requires_diagnoser=stop_requires_diagnoser,
    )
    if diagnoser_author_reason and _diagnoser_result_requires_source_statement_decision(diagnoser_result):
        if not _source_statement_decision_resolved(raw_task, diagnoser_result, settings):
            return action("source_statement_decision_required", "", diagnoser_author_reason)
        child_reason = _promoted_child_obligations_reason(row.task_id, raw_task, settings)
        if child_reason:
            return action(
                "foundation_absorb_required",
                "",
                f"{diagnoser_author_reason}; source decision resolved; {child_reason}",
            )
        if _current_promotable_obligations(row.task_id, settings):
            return action(
                "foundation_absorb_required",
                "",
                f"{diagnoser_author_reason}; source decision resolved; absorb remaining concrete obligations into parent/support files",
            )
    if diagnoser_author_reason and _diagnoser_result_requires_obligation_promotion(diagnoser_result):
        child_reason = _promoted_child_obligations_reason(row.task_id, raw_task, settings)
        if child_reason:
            return action("foundation_absorb_required", "", f"{diagnoser_author_reason}; {child_reason}")
        return action(
            "foundation_absorb_required",
            "",
            f"{diagnoser_author_reason}; obligation child promotion is disabled; absorb proof obligations into parent/support files",
        )
    math_gate_state = math_review_gate_state(
        row.task_id,
        raw_task,
        pack_dir=raw_task.get("pack_dir", ""),
    )
    math_gate_reason = math_review_gate_blocker(
        row.task_id,
        raw_task,
        pack_dir=raw_task.get("pack_dir", ""),
    )
    if math_gate_reason:
        if math_gate_state.stop_mode == "blocking_proof":
            return action("blocking_proof_required", "", math_gate_reason)
        return action("math_review_gate_required", "", math_gate_reason)
    if diagnoser_author_reason:
        return action(
            "auto_loop",
            _phase2_command("auto-loop", row.task_id, "--review-subject current"),
            diagnoser_author_reason,
        )
    if row.report_status == "needs_class_normalization":
        if _official_output_exists(settings, row.task_id):
            return action(
                "review_existing",
                _phase2_command("review-now", row.task_id, "--review-subject existing"),
                row.task_status_reason or "official output needs a fresh classified semantic review",
            )
        return action(
            "diagnostic_restore_or_rebuild_output"
            if _review_or_build_candidate_exists(raw_task)
            else "restore_or_rebuild_output",
            "",
            "class normalization requires a fresh review, but no official output file was found",
        )
    verify_failure = raw_task.get("latest_verify_failure", {})
    if isinstance(verify_failure, dict) and verify_failure:
        verify_disposition = str(verify_failure.get("disposition", "") or "").strip()
        verify_summary = str(
            verify_failure.get("summary", "") or "latest verify result failed; repair through auto-loop"
        )
        if verify_disposition == "review_existing_required":
            if _official_output_exists(settings, row.task_id):
                return action(
                    "review_existing",
                    _phase2_command("review-now", row.task_id, "--review-subject existing"),
                    verify_summary,
                )
            return action(
                "diagnostic_restore_or_rebuild_output"
                if _review_or_build_candidate_exists(raw_task)
                else "restore_or_rebuild_output",
                "",
                f"{verify_summary}; official output required by verify disposition was not found",
            )
        return action(
            "auto_loop",
            _phase2_command("auto-loop", row.task_id, "--review-subject current"),
            verify_summary,
        )
    if row.report_status == "needs_fresh_review":
        if _official_output_exists(settings, row.task_id):
            return action(
                "review_existing",
                _phase2_command("review-now", row.task_id, "--review-subject existing"),
                row.task_status_reason or "official output needs a fresh classified semantic review",
            )
        return action(
            "diagnostic_restore_or_rebuild_output"
            if _review_or_build_candidate_exists(raw_task)
            else "restore_or_rebuild_output",
            "",
            "fresh existing review is needed, but no official output file was found"
            + (
                "; draft/candidate exists, so this is diagnostic and should not displace parent-facing repair/review work"
                if _review_or_build_candidate_exists(raw_task)
                else ""
            ),
        )
    if row.task_status == "fail":
        return action(
            "auto_loop",
            _phase2_command("auto-loop", row.task_id, "--review-subject current"),
            row.task_status_reason or row.issue or "task-level proof status is not pass",
        )
    return action(
        "inspect",
        "",
        row.issue or row.next_action or "no automatic action selected",
    )


def _select_worker_queue(
    actions: tuple[BatchRunnerAction, ...],
    *,
    task_kinds: list[str] | tuple[str, ...],
    limit: int | None,
    worker_slots: int,
) -> tuple[BatchRunnerAction, ...]:
    kind_filter = {_normalize_kind(kind) for kind in task_kinds if _normalize_kind(kind)}
    if not kind_filter and not limit and worker_slots <= 0:
        return actions
    selected = [
        action
        for action in actions
        if action.action
        not in {
            "none",
            "skip_blocked",
            "blocked",
            "diagnoser_required",
            "reviewer_required",
            "source_statement_decision_required",
            "math_review_gate_required",
            "blocking_proof_required",
            "inspect",
        }
        and (not kind_filter or action.task_kind in kind_filter)
    ]
    selected.sort(key=lambda action: (_action_priority(action.action), -action.fanout, action.task_id))
    if limit is not None and limit > 0:
        selected = selected[:limit]
    if worker_slots > 0:
        selected = [
            BatchRunnerAction(
                action.task_id,
                action.action,
                action.command,
                action.reason,
                task_kind=action.task_kind,
                fanout=action.fanout,
                conflict_group=action.conflict_group,
                worker_slot=(index % worker_slots) + 1,
            )
            for index, action in enumerate(selected)
        ]
    return tuple(selected)


def _partition_default_visible_actions(
    actions: tuple[BatchRunnerAction, ...],
    *,
    include_legacy: bool,
) -> tuple[tuple[BatchRunnerAction, ...], tuple[BatchRunnerAction, ...]]:
    visible: list[BatchRunnerAction] = []
    hidden: list[BatchRunnerAction] = []
    for action in actions:
        hidden_category = _default_hidden_action_category(action)
        if hidden_category and (not include_legacy or _always_hide_action_category(hidden_category)):
            hidden.append(action)
        else:
            visible.append(action)
    return tuple(visible), tuple(hidden)


def _hidden_actions_summary_line(hidden_actions: tuple[BatchRunnerAction, ...]) -> str:
    if not hidden_actions:
        return "- hidden legacy/audit items: `0`"
    counts = Counter(
        category
        for action in hidden_actions
        for category in [_default_hidden_action_category(action)]
        if category
    )
    detail = ", ".join(f"{name}={count}" for name, count in sorted(counts.items()))
    return f"- hidden legacy/audit items: `{len(hidden_actions)}` ({detail})"


def _source_statement_risk_exceptions_summary_line(hidden_actions: tuple[BatchRunnerAction, ...]) -> str:
    task_ids = sorted(
        action.task_id
        for action in hidden_actions
        if _default_hidden_action_category(action) == "source_statement_risk"
    )
    if not task_ids:
        return "- deferred_source_statement_risk_exceptions: `0`"
    return "- deferred_source_statement_risk_exceptions: `{count}` ({tasks})".format(
        count=len(task_ids),
        tasks=", ".join(f"`{task_id}`" for task_id in task_ids),
    )


def _default_hidden_action_category(action: BatchRunnerAction) -> str:
    if _is_skipped_source_statement_risk(action):
        return "source_statement_risk"
    if _is_legacy_obligation_task_id(action.task_id) or action.task_kind == "obligation":
        return "legacy_obligation"
    if _is_section_intro_remark(action):
        return "section_intro_remark"
    if action.action == "diagnostic_restore_or_rebuild_output":
        return "diagnostic_restore_or_rebuild_output"
    return ""


def _always_hide_action_category(category: str) -> bool:
    return category in {"section_intro_remark", "source_statement_risk"}


def _action_priority(action: str) -> int:
    return {
        "foundation_absorb_required": 1,
        "auto_loop": 2,
        "review_existing": 3,
        "diagnostic_restore_or_rebuild_output": 8,
        "restore_or_rebuild_output": 6,
        "inspect": 7,
    }.get(action, 9)


def _task_kind(task_id: str, raw_task: dict[str, Any]) -> str:
    raw_kind = str(raw_task.get("type", "") or "").strip()
    kind = _normalize_kind(raw_kind)
    if kind:
        return kind
    if task_id.startswith("thm_"):
        return "theorem"
    if task_id.startswith("def_"):
        return "definition"
    if task_id.startswith("prob_"):
        return "problem"
    if task_id.startswith("ex_"):
        return "exercise"
    if task_id.startswith("rem_"):
        return "remark"
    return ""


def _is_legacy_obligation_task_id(task_id: str) -> bool:
    canonical = canonicalize_block_id(str(task_id or ""))
    return canonical.startswith("obl_")


def _is_section_intro_remark(action: BatchRunnerAction) -> bool:
    task_id = canonicalize_block_id(str(action.task_id or ""))
    return task_id.startswith("intro_") and action.task_kind == "remark"


def _is_skipped_source_statement_risk(action: BatchRunnerAction) -> bool:
    task_id = canonicalize_block_id(str(action.task_id or ""))
    if task_id not in SOURCE_STATEMENT_RISK_SKIP_TASK_IDS:
        return False
    return action.action in {
        "blocked",
        "diagnoser_required",
        "source_statement_decision_required",
        "skip_blocked",
    }


def _normalize_kind(raw: str) -> str:
    text = str(raw or "").strip().lower().replace("_", " ").replace("-", " ")
    aliases = {
        "theorem": "theorem",
        "thm": "theorem",
        "definition": "definition",
        "def": "definition",
        "problem": "problem",
        "prob": "problem",
        "exercise": "exercise",
        "ex": "exercise",
        "remark": "remark",
        "rem": "remark",
        "phase2obligationtask": "obligation",
        "phase2 obligation task": "obligation",
        "obligation": "obligation",
    }
    return aliases.get(text, "")


def _transitive_fanout(raw_tasks: dict[str, dict[str, Any]]) -> dict[str, int]:
    dependencies = {
        task_id: [
            canonicalize_block_id(str(dep))
            for dep in raw_task.get("dependencies", [])
            if canonicalize_block_id(str(dep))
        ]
        for task_id, raw_task in raw_tasks.items()
    }
    fanout = {task_id: 0 for task_id in raw_tasks}
    for task_id in raw_tasks:
        seen: set[str] = set()
        stack = list(dependencies.get(task_id, []))
        while stack:
            dep = stack.pop()
            if dep in seen:
                continue
            seen.add(dep)
            if dep in fanout:
                fanout[dep] += 1
            stack.extend(dependencies.get(dep, []))
    return fanout


def _official_output_exists(settings, task_id: str) -> bool:
    output_dir = Path(getattr(settings, "toyapollo_output_dir", "ToyApollo/Output"))
    return (output_dir / f"{task_id}.lean").exists()


def _review_or_build_candidate_exists(raw_task: dict[str, Any]) -> bool:
    candidate_keys = (
        "latest_build_ready_candidate_file",
        "latest_build_candidate_file",
        "latest_candidate_file",
        "draft_file",
    )
    for key in candidate_keys:
        raw_path = str(raw_task.get(key, "") or "").strip()
        if raw_path and Path(raw_path).is_file():
            return True
    pack_dir_raw = str(raw_task.get("pack_dir", "") or "").strip()
    if not pack_dir_raw:
        return False
    pack_dir = Path(pack_dir_raw)
    if (pack_dir / "draft.lean").is_file():
        return True
    try:
        return any(pack_dir.glob("candidate_v*.lean"))
    except OSError:
        return False


def _first_nonconsumable_proof_debt_dependency(task_id: str, raw_tasks: dict[str, dict[str, Any]]) -> str:
    task = raw_tasks.get(task_id, {})
    if not isinstance(task, dict):
        return ""
    seen: set[str] = set()
    stack = list(reversed(_canonical_dependency_list(task.get("dependencies", []))))
    while stack:
        dep_id = stack.pop()
        if dep_id in seen:
            continue
        seen.add(dep_id)
        dep_task = raw_tasks.get(dep_id, {})
        if isinstance(dep_task, dict):
            if _record_has_nonconsumable_proof_debt(dep_task):
                return dep_id
            stack.extend(reversed(_canonical_dependency_list(dep_task.get("dependencies", []))))
    return ""


def _first_diagnoser_required_dependency(task_id: str, raw_tasks: dict[str, dict[str, Any]]) -> str:
    task = raw_tasks.get(task_id, {})
    if not isinstance(task, dict):
        return ""
    seen: set[str] = set()
    stack = list(reversed(_canonical_dependency_list(task.get("dependencies", []))))
    while stack:
        dep_id = stack.pop()
        if dep_id in seen:
            continue
        seen.add(dep_id)
        dep_task = raw_tasks.get(dep_id, {})
        if isinstance(dep_task, dict):
            if _record_requires_diagnoser(dep_task):
                return dep_id
            stack.extend(reversed(_canonical_dependency_list(dep_task.get("dependencies", []))))
    return ""


def _record_requires_diagnoser(record: dict[str, Any]) -> bool:
    if _load_diagnoser_result(record):
        return False
    if str(record.get("stop_reason", "") or "").strip().lower() == "diagnoser_required":
        return True
    return bool(_semantic_fail_triage_blocker(record))


def _parent_source_statement_decision_required(
    raw_task: dict[str, Any],
    raw_tasks: dict[str, dict[str, Any]],
    settings=None,
) -> str:
    if str(raw_task.get("type", "") or "") != "Phase2ObligationTask":
        return ""
    parent_id = canonicalize_block_id(
        str(
            raw_task.get("parent_task_id", "")
            or raw_task.get("target_task_id", "")
            or raw_task.get("parent_block_id", "")
            or ""
        )
    )
    if not parent_id:
        return ""
    parent = raw_tasks.get(parent_id, {})
    if not isinstance(parent, dict):
        return ""
    diagnoser_result = _load_diagnoser_result(parent)
    if not _diagnoser_result_requires_source_statement_decision(diagnoser_result):
        return ""
    if _source_statement_decision_resolved(parent, diagnoser_result, settings):
        return ""
    return parent_id


def _canonical_dependency_list(raw_dependencies: Any) -> list[str]:
    if not isinstance(raw_dependencies, list):
        return []
    return [
        canonicalize_block_id(str(dep))
        for dep in raw_dependencies
        if canonicalize_block_id(str(dep))
    ]


def _record_has_nonconsumable_proof_debt(record: dict[str, Any]) -> bool:
    status = str(record.get("status", "") or "").strip().upper().replace("-", "_")
    if status == "COMPLETED_WITH_PROOF_DEBT":
        return True
    summary = record.get("proof_obligation_summary", {})
    if isinstance(summary, dict) and _status_counts_include_accepted_proof_debt(summary.get("status_counts", {})):
        return True
    obligations = record.get("proof_obligations", {})
    if isinstance(obligations, dict):
        if _status_counts_include_accepted_proof_debt(obligations.get("status_counts", {})):
            return True
        raw_items = obligations.get("obligations", [])
        for item in raw_items if isinstance(raw_items, list) else []:
            if isinstance(item, dict) and str(item.get("status", "") or "").strip().lower() == "accepted_as_proof_debt":
                return True
    return False


def _status_counts_include_accepted_proof_debt(status_counts: Any) -> bool:
    if not isinstance(status_counts, dict):
        return False
    try:
        return int(status_counts.get("accepted_as_proof_debt", 0) or 0) > 0
    except (TypeError, ValueError):
        return False


def _semantic_fail_triage_blocker(raw_task: dict[str, Any]) -> str:
    triage_state = _semantic_fail_triage_state(raw_task)
    needs_diagnoser = bool(triage_state.get("needs_diagnoser", False))
    local_repair_allowed = bool(triage_state.get("local_repair_allowed", False))
    category = str(triage_state.get("category", "") or "").strip()
    prompt_path = str(triage_state.get("prompt_path", "") or "").strip()
    if not needs_diagnoser or local_repair_allowed:
        return ""
    if _load_diagnoser_result(raw_task):
        return ""
    parts = [
        "semantic-fail triage",
        f"category `{category}`" if category else "",
        "requires read-only diagnoser before ordinary auto-loop",
        f"prompt={prompt_path}" if prompt_path else "",
    ]
    return "; ".join(part for part in parts if part)


def _reviewer_required_blocker(
    task_id: str,
    raw_task: dict[str, Any],
    *,
    ledger,
    settings,
) -> tuple[str, str]:
    expected_path = _resolve_existing_path(raw_task.get("current_review_expected_result_file", ""))
    request_path = _resolve_existing_path(raw_task.get("current_review_request_file", ""))
    phase = str(raw_task.get("current_auto_loop_phase", "") or "").strip().lower()
    status = str(raw_task.get("current_auto_loop_status", "") or "").strip().lower()
    pending_request = (
        request_path is not None
        and request_path.exists()
        and expected_path is not None
        and not expected_path.exists()
    ) or (
        phase == "reviewing"
        and status == "active"
        and expected_path is not None
        and not expected_path.exists()
    )
    if pending_request:
        if ledger is None or settings is None or not hasattr(settings, "phase2_prompt_packs_dir"):
            return "", "current pending review freshness cannot be checked without ledger/settings"
        try:
            task = resolve_phase2_task(task_id, ledger, settings)
            validation_error, request_info = _load_current_codex_review_request(
                task=task,
                ledger=ledger,
                settings=settings,
                pack_dir=settings.phase2_prompt_packs_dir / task_id,
            )
        except (AttributeError, KeyError, OSError, TypeError, ValueError) as exc:
            return "", f"current pending review request could not be validated: {exc}"
        if validation_error:
            return "", validation_error
        if bool(request_info.get("result_exists")):
            return "", "current pending review already has a result and is no longer reviewer-pending"
        current_request_path = Path(str(request_info.get("request_path", "") or request_path))
        current_expected_path = Path(str(request_info.get("expected_result_path", "") or expected_path))
        return (
            "; ".join(
                [
                    "waiting for independent semantic reviewer",
                    f"request={current_request_path}",
                    f"expected_result={current_expected_path}",
                ]
            ),
            "",
        )
    return "", ""


def _resolve_existing_path(raw_path: Any) -> Path | None:
    raw = str(raw_path or "").strip()
    if not raw:
        return None
    return Path(raw)


def _load_semantic_fail_triage(raw_task: dict[str, Any]) -> dict[str, Any]:
    path_text = str(raw_task.get("latest_semantic_fail_triage_file", "") or "").strip()
    if not path_text:
        return {}
    path = Path(path_text)
    if not path.exists():
        return {}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    return payload if isinstance(payload, dict) else {}


def _semantic_fail_triage_state(raw_task: dict[str, Any]) -> dict[str, Any]:
    triage = _load_semantic_fail_triage(raw_task)
    if triage:
        return {
            "needs_diagnoser": _truthy(triage.get("needs_diagnoser", False)),
            "local_repair_allowed": _truthy(triage.get("local_repair_allowed", False)),
            "category": str(triage.get("category", "") or "").strip(),
            "prompt_path": str(triage.get("prompt_path", "") or triage.get("prompt_alias_path", "") or "").strip(),
        }
    return {
        "needs_diagnoser": _truthy(raw_task.get("latest_semantic_fail_triage_needs_diagnoser", False)),
        "local_repair_allowed": _truthy(raw_task.get("latest_semantic_fail_triage_local_repair_allowed", False)),
        "category": str(raw_task.get("latest_semantic_fail_triage_category", "") or "").strip(),
        "prompt_path": str(raw_task.get("latest_diagnoser_prompt_file", "") or "").strip(),
    }


def _load_diagnoser_result(raw_task: dict[str, Any]) -> dict[str, Any]:
    for pack_dir in _diagnoser_pack_dirs(raw_task):
        for path in _diagnoser_result_candidates(pack_dir):
            try:
                payload = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError):
                continue
            if _diagnoser_result_payload_is_complete(payload):
                return {"path": str(path), "payload": payload}
    return {}


def _diagnoser_pack_dirs(raw_task: dict[str, Any]) -> list[Path]:
    candidates: list[Path] = []
    for key in ("pack_dir", "latest_semantic_fail_triage_file", "latest_diagnoser_prompt_file"):
        raw = str(raw_task.get(key, "") or "").strip()
        if not raw:
            continue
        path = Path(raw)
        candidates.append(path if key == "pack_dir" else path.parent)
    task_id = canonicalize_block_id(str(raw_task.get("task_id", "") or ""))
    if task_id and not candidates:
        candidates.append(Path("phase2_prompt_packs") / task_id)
    deduped: list[Path] = []
    seen: set[Path] = set()
    for path in candidates:
        if path in seen:
            continue
        seen.add(path)
        deduped.append(path)
    return deduped


def _diagnoser_result_candidates(pack_dir: Path) -> list[Path]:
    if not pack_dir.exists():
        return []
    versioned = sorted(
        [path for path in pack_dir.glob(f"{DIAGNOSER_RESULT_PREFIX}_v*.json") if path.is_file()],
        key=_diagnoser_result_sort_key,
        reverse=True,
    )
    candidates = list(versioned)
    alias = pack_dir / DIAGNOSER_RESULT_ALIAS
    if alias.is_file():
        candidates.append(alias)
    deduped: list[Path] = []
    seen: set[Path] = set()
    for path in candidates:
        if path in seen:
            continue
        seen.add(path)
        deduped.append(path)
    return deduped


def _diagnoser_result_sort_key(path: Path) -> tuple[int, str]:
    match = re.fullmatch(rf"{re.escape(DIAGNOSER_RESULT_PREFIX)}_v(\d+)\.json", path.name)
    return (int(match.group(1)) if match else -1, path.name)


def _diagnoser_result_payload_is_complete(payload: Any) -> bool:
    return (
        isinstance(payload, dict)
        and DIAGNOSER_RESULT_REQUIRED_FIELDS.issubset(payload.keys())
        and bool(str(payload.get("diagnosis_verdict", "") or payload.get("diagnosis_summary", "") or "").strip())
    )


def _diagnoser_result_author_reason(
    raw_task: dict[str, Any],
    diagnoser_result: dict[str, Any],
    *,
    stop_requires_diagnoser: bool,
) -> str:
    if not diagnoser_result:
        return ""
    triage_state = _semantic_fail_triage_state(raw_task)
    if not stop_requires_diagnoser and not bool(triage_state.get("needs_diagnoser", False)):
        return ""
    payload = diagnoser_result.get("payload", {})
    if not isinstance(payload, dict):
        return ""
    local_repair_allowed = _truthy(payload.get("local_repair_allowed", False))
    result_path = str(diagnoser_result.get("path", "") or "")
    diagnosis_kind = str(payload.get("diagnosis_kind", "") or "").strip()
    diagnosis_verdict = str(payload.get("diagnosis_verdict", "") or "").strip()
    recommended_next_action = str(payload.get("recommended_next_action", "") or "").strip()
    if "promote" in recommended_next_action.lower() or "child obligation" in recommended_next_action.lower():
        recommended_next_action = (
            "absorb proof obligations into parent/support files; obligation child promotion is disabled"
        )
    if local_repair_allowed:
        parts = [
            "diagnoser_result local_repair_allowed=true",
            "route back to ordinary repair/auto-loop",
        ]
    else:
        parts = [
            "diagnoser_result local_repair_allowed=false",
            "diagnosis requires source-facing rewrite/decomposition before ordinary proof repair",
        ]
    parts.extend(
        part
        for part in (
            f"result={result_path}" if result_path else "",
            f"diagnosis_kind={diagnosis_kind}" if diagnosis_kind else "",
            f"diagnosis_verdict={diagnosis_verdict}" if diagnosis_verdict else "",
            f"recommended_next_action={recommended_next_action}" if recommended_next_action else "",
        )
        if part
    )
    return "; ".join(parts)


def _diagnoser_result_requires_source_statement_decision(diagnoser_result: dict[str, Any]) -> bool:
    payload = diagnoser_result.get("payload", {})
    if not isinstance(payload, dict):
        return False
    if _truthy(payload.get("route_wrong", False)):
        return False
    if not _truthy(payload.get("statement_mismatch", False)):
        return False
    if _truthy(payload.get("local_repair_allowed", False)):
        return False
    recommended_next_action = str(payload.get("recommended_next_action", "") or "").strip().lower()
    diagnosis_verdict = str(payload.get("diagnosis_verdict", "") or "").strip().lower()
    return any(
        marker in f"{diagnosis_verdict}\n{recommended_next_action}"
        for marker in (
            "source/statement decision",
            "source-statement defect",
            "literal source statement",
            "literal statement",
        )
    )


def _source_statement_decision_resolved(
    raw_task: dict[str, Any],
    diagnoser_result: dict[str, Any],
    settings=None,
) -> bool:
    if not diagnoser_result:
        return False
    result_path = str(diagnoser_result.get("path", "") or "").strip()
    for pack_dir in _diagnoser_pack_dirs(raw_task):
        path = pack_dir / SOURCE_DECISION_RESOLUTION_FILE
        if not path.is_file():
            continue
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if _source_statement_decision_resolution_matches(payload, result_path):
            return True
    task_id = canonicalize_block_id(str(raw_task.get("task_id", "") or raw_task.get("block_id", "") or ""))
    if not task_id:
        return False
    path = _task_pack_dir(task_id, settings) / SOURCE_DECISION_RESOLUTION_FILE
    if not path.is_file():
        return False
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    return _source_statement_decision_resolution_matches(payload, result_path)


def _source_statement_decision_resolution_matches(payload: Any, diagnoser_result_path: str) -> bool:
    if not isinstance(payload, dict):
        return False
    status = str(payload.get("status", "") or "").strip().lower()
    if status not in {"resolved", "applied", "accepted"}:
        return False
    decision = str(payload.get("decision", "") or payload.get("source_decision", "") or "").strip()
    if not decision:
        return False
    resolves = payload.get("resolves_diagnoser_result", "")
    if not resolves:
        return True
    candidates = [resolves] if isinstance(resolves, str) else resolves
    if not isinstance(candidates, list):
        return False
    result_name = Path(diagnoser_result_path).name
    result_text = str(Path(diagnoser_result_path))
    return any(str(candidate) == result_text or Path(str(candidate)).name == result_name for candidate in candidates)


def _diagnoser_result_requires_obligation_promotion(diagnoser_result: dict[str, Any]) -> bool:
    payload = diagnoser_result.get("payload", {})
    if not isinstance(payload, dict):
        return False
    if _truthy(payload.get("local_repair_allowed", False)):
        return False
    diagnosis_kind = str(payload.get("diagnosis_kind", "") or "").strip().lower()
    diagnosis_verdict = str(payload.get("diagnosis_verdict", "") or "").strip().lower()
    recommended_next_action = str(payload.get("recommended_next_action", "") or "").strip().lower()
    required_child_obligations = payload.get("required_child_obligations")
    has_required_child_obligations = (
        isinstance(required_child_obligations, list) and len(required_child_obligations) > 0
    )
    decision_text = f"{diagnosis_kind}\n{diagnosis_verdict}\n{recommended_next_action}"
    if has_required_child_obligations and any(
        marker in decision_text
        for marker in (
            "child_obligation",
            "child obligation",
            "promotion",
            "promote",
        )
    ):
        return True
    return any(
        marker in decision_text
        for marker in (
            "deeper_child_obligation_promotion",
            "deeper child obligation promotion",
            "explicit_child_obligation_promotion",
            "explicit child obligation promotion",
            "explicit_open_debt_obligation_promotion",
            "explicit open-debt obligation promotion",
            "promotion_required",
            "obligation promotion",
            "promote obligations",
            "promote the obligations",
            "promote child obligations",
        )
    )


def _task_pack_dir(task_id: str, settings=None) -> Path:
    prompt_root = Path(getattr(settings, "phase2_prompt_packs_dir", "phase2_prompt_packs"))
    return prompt_root / task_id


def _truthy(value: Any) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return bool(value)
    if isinstance(value, str):
        return value.strip().lower() in {"1", "true", "yes", "y", "on"}
    return bool(value)


def _phase2_command(mode: str, task_id: str, extra: str = "") -> str:
    suffix = f" {extra}" if extra else ""
    return f"python .\\run_chapter.py --phase 2 --phase2-mode {mode} --tasks {task_id}{suffix}"


def _latest_verify_failure(raw_path: Any) -> dict[str, str]:
    path_text = str(raw_path or "").strip()
    if not path_text:
        return {}
    path = Path(path_text)
    if not path.exists():
        return {}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    if not isinstance(payload, dict) or payload.get("success") is True:
        return {}
    disposition = str(payload.get("disposition", "") or "").strip()
    primary_kind = str(payload.get("primary_failure_kind", "") or "").strip()
    diagnostic_text = _first_diagnostic_message(payload.get("diagnostics"))
    summary_parts = [
        part
        for part in (
            f"latest verify result failed",
            f"disposition={disposition}" if disposition else "",
            f"primary_failure_kind={primary_kind}" if primary_kind else "",
            diagnostic_text,
        )
        if part
    ]
    return {
        "disposition": disposition,
        "primary_failure_kind": primary_kind,
        "summary": "; ".join(summary_parts),
    }


def _first_diagnostic_message(raw_diagnostics: Any) -> str:
    if not isinstance(raw_diagnostics, list):
        return ""
    for item in raw_diagnostics:
        if not isinstance(item, dict):
            continue
        kind = str(item.get("kind", "") or "").strip()
        message = str(item.get("message", "") or "").strip()
        if kind or message:
            return ": ".join(part for part in (kind, message) if part)
    return ""
