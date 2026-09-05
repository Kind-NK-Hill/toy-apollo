from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from formalization_engine.block_id_naming import canonicalize_block_id, canonicalize_id_list
from formalization_engine.phase2_failure_budget import (
    PHASE2_FAILURE_STREAK_LIMIT,
    Phase2FailureCounters,
    phase2_failure_counters_from_task,
)
from formalization_engine.phase2_task_status import classify_phase2_task_status


COMPLETED = "COMPLETED"
COMPLETED_WITH_PROOF_DEBT = "COMPLETED_WITH_PROOF_DEBT"
FAILED_LOCAL = "FAILED_LOCAL"
DEPENDENCY_FAILED = "DEPENDENCY_FAILED"
DEPENDENCY_PROOF_DEBT = "DEPENDENCY_PROOF_DEBT"
MECHANISM_BLOCKER = "MECHANISM_BLOCKER"
USER_INTERRUPTED = "USER_INTERRUPTED"
NEEDS_DECOMPOSITION = "NEEDS_DECOMPOSITION"
NONTERMINAL = "NONTERMINAL"

TEXTBOOK_COMPLETE_OBJECTIVE = "textbook-complete"
DIAGNOSTIC_OBJECTIVE = "diagnostic"
OBJECTIVES = {TEXTBOOK_COMPLETE_OBJECTIVE, DIAGNOSTIC_OBJECTIVE}
DEFAULT_ALLOWED_BEYOND_BOOK_TASKS = {
    "thm_1_2",
    "ex_1_3_2",
    "thm_11_8",
    "thm_14_8",
}
FAMILY_CONSUMABLE_PROOF_CLASSES = {
    "source_route_finite_interval_covered",
    "source_route_support_completed_downstream_blocked",
}
FAMILY_CONSUMABLE_COMPLETION_CLASSES = {
    "finite_interval_completed_but_direct_downstream_blocked",
    "not_completed_downstream_blocked",
}

REPORTING_TERMINAL_STATUSES = {
    COMPLETED,
    COMPLETED_WITH_PROOF_DEBT,
    FAILED_LOCAL,
    DEPENDENCY_FAILED,
    DEPENDENCY_PROOF_DEBT,
    MECHANISM_BLOCKER,
    USER_INTERRUPTED,
}
ROOT_DEPENDENCY_FAILURE_REASONS = {
    "hard_failure",
    "nonprogress",
    "max_rounds",
    "build_budget_exhausted",
}
SUBSTANTIVE_FAILURE_KINDS = {
    "build_check_failure",
    "semantic_review_fail",
    "semantic_review_inconclusive",
    "review_apply_rejection",
}
REVIEW_APPLY_COUNTED_CLASSES = {"semantic", "freshness"}
COMPLEX_RETRY_BUDGET = PHASE2_FAILURE_STREAK_LIMIT


@dataclass(frozen=True)
class FailureBudget:
    counted: int
    required: int = COMPLEX_RETRY_BUDGET
    exhausted: bool = False
    skipped: list[str] = field(default_factory=list)


@dataclass(frozen=True)
class BatchTaskRow:
    task_id: str
    status: str
    declared_status: str
    task_status: str = ""
    report_status: str = ""
    task_status_reason: str = ""
    task_status_evidence_type: str = ""
    review_verdict: str = ""
    proof_class: str = ""
    stop_reason: str = ""
    dependencies: tuple[str, ...] = ()
    failed_dependency: str = ""
    blocked_dependency: str = ""
    proof_debt_dependency: str = ""
    substantive_failures: int = 0
    build_fail_streak: int = 0
    review_fail_streak: int = 0
    retry_budget_required: int = COMPLEX_RETRY_BUDGET
    retry_budget_exhausted: bool = False
    report_terminal: bool = False
    terminal: bool = False
    clean_or_allowed_exception: bool = False
    allowed_beyond_book_exception: bool = False
    issue: str = ""
    next_action: str = ""


@dataclass(frozen=True)
class BatchReport:
    batch_id: str
    rows: tuple[BatchTaskRow, ...]
    objective: str = TEXTBOOK_COMPLETE_OBJECTIVE
    allowed_beyond_book_tasks: tuple[str, ...] = ()
    issues: tuple[str, ...] = ()

    @property
    def all_terminal(self) -> bool:
        return all(row.terminal for row in self.rows)

    @property
    def all_reporting_terminal(self) -> bool:
        return all(row.report_terminal for row in self.rows)

    @property
    def all_clean_or_allowed_exception(self) -> bool:
        return all(row.clean_or_allowed_exception for row in self.rows)

    @property
    def counts(self) -> dict[str, int]:
        counts: dict[str, int] = {}
        for row in self.rows:
            counts[row.status] = counts.get(row.status, 0) + 1
        return counts


def load_batch_state(path: str | Path) -> dict[str, Any]:
    state_path = Path(path).expanduser()
    payload = json.loads(state_path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("Batch state must be a JSON object.")
    return payload


def analyze_batch_state(
    payload: dict[str, Any],
    *,
    objective: str = TEXTBOOK_COMPLETE_OBJECTIVE,
    allowed_beyond_book_tasks: set[str] | None = None,
) -> BatchReport:
    normalized_objective = _normalize_objective(objective)
    allowed_tasks = {
        canonicalize_block_id(task_id)
        for task_id in (allowed_beyond_book_tasks or DEFAULT_ALLOWED_BEYOND_BOOK_TASKS)
        if canonicalize_block_id(task_id)
    }
    tasks = payload.get("tasks", [])
    if not isinstance(tasks, list):
        raise ValueError("Batch state field `tasks` must be a list.")
    batch_id = str(payload.get("batch_id", "") or "(unnamed)")
    task_map: dict[str, dict[str, Any]] = {}
    issues: list[str] = []
    for raw_task in tasks:
        if not isinstance(raw_task, dict):
            issues.append("Ignored non-object task entry.")
            continue
        task_id = canonicalize_block_id(str(raw_task.get("task_id") or raw_task.get("block_id") or ""))
        if not task_id:
            issues.append("Ignored task entry without a valid task_id.")
            continue
        if task_id in task_map:
            issues.append(f"Duplicate task_id ignored after first occurrence: {task_id}")
            continue
        task_map[task_id] = raw_task

    hard_failed_roots = _hard_failed_roots(task_map)
    phase2_blocking_roots = _phase2_blocking_roots(task_map, allowed_beyond_book_tasks=allowed_tasks)
    proof_debt_roots = _proof_debt_roots(
        task_map,
        objective=normalized_objective,
        allowed_beyond_book_tasks=allowed_tasks,
    )
    rows: list[BatchTaskRow] = []
    for task_id in sorted(task_map):
        raw_task = task_map[task_id]
        declared_status = _normalize_status(raw_task.get("status"))
        stop_reason = str(raw_task.get("stop_reason", "") or "").strip()
        dependencies = tuple(canonicalize_id_list(raw_task.get("dependencies", [])))
        failed_dependency = _first_failed_transitive_dependency(task_id, task_map, hard_failed_roots)
        blocked_dependency = (
            ""
            if failed_dependency
            else _first_blocked_transitive_dependency(task_id, task_map, phase2_blocking_roots)
        )
        proof_debt_dependency = (
            ""
            if failed_dependency or blocked_dependency
            else _first_proof_debt_transitive_dependency(task_id, task_map, proof_debt_roots)
        )
        counters = phase2_failure_counters_from_task(raw_task)

        status = declared_status
        if _early_hard_failure_before_budget(declared_status, stop_reason, counters):
            status = NONTERMINAL
        if failed_dependency and declared_status not in {
            COMPLETED,
            COMPLETED_WITH_PROOF_DEBT,
            FAILED_LOCAL,
            MECHANISM_BLOCKER,
            USER_INTERRUPTED,
        }:
            status = DEPENDENCY_FAILED
        elif proof_debt_dependency and declared_status not in {
            COMPLETED,
            COMPLETED_WITH_PROOF_DEBT,
            FAILED_LOCAL,
            MECHANISM_BLOCKER,
            USER_INTERRUPTED,
            DEPENDENCY_FAILED,
        }:
            status = DEPENDENCY_PROOF_DEBT

        allowed_exception = _is_allowed_beyond_book_exception(
            task_id,
            raw_task,
            status=status,
            allowed_beyond_book_tasks=allowed_tasks,
        )
        task_status, task_status_reason, task_status_evidence_type, review_verdict, proof_class = (
            _task_level_projection_from_raw(task_id, raw_task)
        )
        report_status = _normalize_report_status(
            raw_task.get("phase2_status", raw_task.get("phase2_task_status"))
        )
        if report_status in {"pass", "fail", "blocked", "allowed_exception"}:
            report_status = task_status
        if task_status == "fail" and task_status_evidence_type == "needs_class_normalization":
            report_status = "needs_class_normalization"
        elif not report_status:
            report_status = task_status
        dependency_gate_root = failed_dependency or blocked_dependency or proof_debt_dependency
        if dependency_gate_root and not allowed_exception:
            had_current_pass = task_status == "pass" or report_status == "pass"
            needs_fresh_authority = had_current_pass or report_status == "needs_fresh_review"
            task_status = "blocked"
            report_status = "needs_fresh_review" if needs_fresh_authority else "blocked"
            if failed_dependency:
                task_status_reason = f"depends on failed hard dependency {failed_dependency}"
                task_status_evidence_type = "failed_dependency"
            elif proof_debt_dependency:
                task_status_reason = f"depends on non-consumable proof-debt dependency {proof_debt_dependency}"
                task_status_evidence_type = "proof_debt_dependency"
            else:
                task_status_reason = f"depends on non-current hard dependency {blocked_dependency}"
                task_status_evidence_type = (
                    "dependency_authority_invalidated" if needs_fresh_authority else "blocked_dependency"
                )
        elif not task_status and status == COMPLETED and not allowed_exception:
            report_status = "needs_fresh_review"
            if not task_status_reason:
                task_status_reason = "completed runtime status has no phase2_status/proof_class evidence"
            if not task_status_evidence_type:
                task_status_evidence_type = "missing_task_status"
        elif not task_status and blocked_dependency:
            task_status = "blocked"
            report_status = "blocked"
            task_status_reason = f"depends on phase2-blocked root {blocked_dependency}"
            task_status_evidence_type = "blocked_dependency"
        budget = count_substantive_failures(raw_task.get("failure_events", raw_task.get("substantive_failures", [])))
        issue = _row_issue(
            task_id=task_id,
            status=status,
            stop_reason=stop_reason,
            raw_task=raw_task,
            budget=budget,
            counters=counters,
            failed_dependency=failed_dependency,
            blocked_dependency=blocked_dependency,
            proof_debt_dependency=proof_debt_dependency,
            allowed_beyond_book_exception=allowed_exception,
        )
        if report_status in {"fail", "blocked", "needs_fresh_review", "needs_class_normalization"} and not issue:
            issue = task_status_reason or f"report status is {report_status}"
        next_action = _next_action(
            status=status,
            issue=issue,
            failed_dependency=failed_dependency,
            blocked_dependency=blocked_dependency,
            proof_debt_dependency=proof_debt_dependency,
            objective=normalized_objective,
            allowed_beyond_book_exception=allowed_exception,
        )
        if task_status == "fail":
            if task_status_evidence_type == "needs_class_normalization":
                next_action = "run fresh classified semantic review"
            else:
                next_action = "repair task-level proof status"
        elif task_status == "blocked":
            if failed_dependency:
                next_action = f"skip; blocked by failed dependency {failed_dependency}"
            elif blocked_dependency:
                next_action = f"skip; blocked by {blocked_dependency}"
            elif proof_debt_dependency:
                next_action = f"repair proof-debt root {proof_debt_dependency} before downstream"
            else:
                next_action = "repair dependency gate blocker"
        elif report_status == "needs_fresh_review":
            next_action = "run fresh semantic review"
        report_terminal = status in REPORTING_TERMINAL_STATUSES
        clean_or_allowed_exception = (status == COMPLETED and task_status == "pass") or (
            task_status == "allowed_exception" and allowed_exception
        ) or allowed_exception
        rows.append(
            BatchTaskRow(
                task_id=task_id,
                status=status,
                declared_status=declared_status,
                task_status=task_status,
                report_status=report_status,
                task_status_reason=task_status_reason,
                task_status_evidence_type=task_status_evidence_type,
                review_verdict=review_verdict,
                proof_class=proof_class,
                stop_reason=stop_reason,
                dependencies=dependencies,
                failed_dependency=failed_dependency,
                blocked_dependency=blocked_dependency,
                proof_debt_dependency=proof_debt_dependency,
                substantive_failures=budget.counted,
                build_fail_streak=counters.build_fail_counter,
                review_fail_streak=counters.review_fail_counter,
                retry_budget_required=budget.required,
                retry_budget_exhausted=counters.exhausted,
                report_terminal=report_terminal,
                terminal=_objective_terminal(
                    status=status,
                    objective=normalized_objective,
                    report_terminal=report_terminal,
                    clean_or_allowed_exception=clean_or_allowed_exception,
                ),
                clean_or_allowed_exception=clean_or_allowed_exception,
                allowed_beyond_book_exception=allowed_exception,
                issue=issue,
                next_action=next_action,
            )
        )

    return BatchReport(
        batch_id=batch_id,
        rows=tuple(rows),
        objective=normalized_objective,
        allowed_beyond_book_tasks=tuple(sorted(allowed_tasks)),
        issues=tuple(issues),
    )


def count_substantive_failures(events: Any) -> FailureBudget:
    if not isinstance(events, list):
        return FailureBudget(counted=0, exhausted=False, skipped=["failure_events is not a list"])

    counted = 0
    skipped: list[str] = []
    seen_fingerprints: set[tuple[str, str, str]] = set()
    for index, event in enumerate(events, start=1):
        if not isinstance(event, dict):
            skipped.append(f"event {index}: not an object")
            continue
        reason = _skip_failure_event_reason(event)
        if reason:
            skipped.append(f"event {index}: {reason}")
            continue

        kind = _normalize_failure_kind(event.get("kind") or event.get("stage"))
        fingerprint = str(event.get("failure_fingerprint") or event.get("fingerprint") or "").strip()
        strategy_key = _event_strategy_key(event)
        if fingerprint:
            key = (kind, fingerprint, strategy_key)
            if key in seen_fingerprints and not bool(event.get("strategy_changed")):
                skipped.append(f"event {index}: repeated failure fingerprint without strategy change")
                continue
            seen_fingerprints.add(key)
        counted += 1
    return FailureBudget(
        counted=counted,
        exhausted=counted >= COMPLEX_RETRY_BUDGET,
        skipped=skipped,
    )


def render_markdown_report(report: BatchReport) -> str:
    lines = [
        f"# Phase 2 Batch Status: {report.batch_id}",
        "",
        f"- Objective: `{report.objective}`",
        f"- All terminal: `{str(report.all_terminal).lower()}`",
        f"- All reporting terminal: `{str(report.all_reporting_terminal).lower()}`",
        f"- All clean or allowed exception: `{str(report.all_clean_or_allowed_exception).lower()}`",
        "- Authority note: batch state is a resume/report cache; proof status comes from the latest valid review result and apply gate.",
    ]
    if report.allowed_beyond_book_tasks:
        lines.append("- Allowed beyond-book tasks: `" + ", ".join(report.allowed_beyond_book_tasks) + "`")
    for status in sorted(report.counts):
        lines.append(f"- {status}: `{report.counts[status]}`")
    if report.issues:
        lines.append("- Batch issues: `" + "; ".join(report.issues) + "`")
    lines.extend(
        [
            "",
            "| task_id | ledger_status | phase2_status | report_status | review_verdict | proof_class | stop_reason | failed_dependency | blocked_dependency | proof_debt_dependency | substantive_failures | report_terminal | terminal | clean_or_allowed | next_action | issue |",
            "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | ---: | --- | --- | --- | --- | --- |",
        ]
    )
    for row in report.rows:
        lines.append(
            "| {task_id} | {status} | {task_status} | {report_status} | {review_verdict} | {proof_class} | {stop_reason} | {failed_dependency} | {blocked_dependency} | {proof_debt_dependency} | {failures} | {report_terminal} | {terminal} | {clean_or_allowed} | {next_action} | {issue} |".format(
                task_id=row.task_id,
                status=row.status,
                task_status=row.task_status or "",
                report_status=row.report_status or "",
                review_verdict=row.review_verdict or "",
                proof_class=row.proof_class or "",
                stop_reason=row.stop_reason or "",
                failed_dependency=row.failed_dependency or "",
                blocked_dependency=row.blocked_dependency or "",
                proof_debt_dependency=row.proof_debt_dependency or "",
                failures=row.substantive_failures,
                report_terminal=str(row.report_terminal).lower(),
                terminal=str(row.terminal).lower(),
                clean_or_allowed=str(row.clean_or_allowed_exception).lower(),
                next_action=row.next_action,
                issue=row.issue,
            )
        )
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Report Formalization Engine Phase 2 batch-controller checklist state."
    )
    parser.add_argument("state", help="Path to a batch-controller JSON checklist.")
    parser.add_argument(
        "--objective",
        choices=sorted(OBJECTIVES),
        default=TEXTBOOK_COMPLETE_OBJECTIVE,
        help=(
            "Batch objective. Default textbook-complete treats proof-debt states as unfinished; "
            "diagnostic preserves report-only terminal coverage."
        ),
    )
    parser.add_argument(
        "--allow-beyond-book",
        action="append",
        default=None,
        metavar="TASK_ID",
        help="Task id allowed as a beyond-book exception for textbook-complete clean gate.",
    )
    parser.add_argument("--json", action="store_true", dest="as_json", help="Emit normalized report JSON.")
    args = parser.parse_args(argv)

    try:
        report = analyze_batch_state(
            load_batch_state(args.state),
            objective=args.objective,
            allowed_beyond_book_tasks=set(args.allow_beyond_book or DEFAULT_ALLOWED_BEYOND_BOOK_TASKS),
        )
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    if args.as_json:
        payload = {
            "batch_id": report.batch_id,
            "objective": report.objective,
            "all_terminal": report.all_terminal,
            "all_reporting_terminal": report.all_reporting_terminal,
            "all_clean_or_allowed_exception": report.all_clean_or_allowed_exception,
            "allowed_beyond_book_tasks": list(report.allowed_beyond_book_tasks),
            "counts": report.counts,
            "issues": list(report.issues),
            "tasks": [
                {
                    "task_id": row.task_id,
                    "status": row.status,
                    "declared_status": row.declared_status,
                    "phase2_status": row.task_status,
                    "task_status": row.task_status,
                    "report_status": row.report_status,
                    "task_status_reason": row.task_status_reason,
                    "task_status_evidence_type": row.task_status_evidence_type,
                    "review_verdict": row.review_verdict,
                    "proof_class": row.proof_class,
                    "stop_reason": row.stop_reason,
                    "failed_dependency": row.failed_dependency,
                    "blocked_dependency": row.blocked_dependency,
                    "proof_debt_dependency": row.proof_debt_dependency,
                    "substantive_failures": row.substantive_failures,
                    "build_fail_streak": row.build_fail_streak,
                    "review_fail_streak": row.review_fail_streak,
                    "retry_budget_required": row.retry_budget_required,
                    "retry_budget_exhausted": row.retry_budget_exhausted,
                    "report_terminal": row.report_terminal,
                    "terminal": row.terminal,
                    "clean_or_allowed_exception": row.clean_or_allowed_exception,
                    "allowed_beyond_book_exception": row.allowed_beyond_book_exception,
                    "next_action": row.next_action,
                    "issue": row.issue,
                }
                for row in report.rows
            ],
        }
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(render_markdown_report(report), end="")
    return 0


def _normalize_status(raw: Any) -> str:
    status = str(raw or "").strip().upper().replace("-", "_")
    aliases = {
        "": NONTERMINAL,
        "TODO": NONTERMINAL,
        "READY": NONTERMINAL,
        "ACTIVE": NONTERMINAL,
        "BLOCKED": NONTERMINAL,
        "IN_PROGRESS": NONTERMINAL,
        "DEPENDENCY_FAILED": DEPENDENCY_FAILED,
        "DEPENDENCY-FAILED": DEPENDENCY_FAILED,
        "DEPENDENCY FAILED": DEPENDENCY_FAILED,
        "DEPENDENCY_PROOF_DEBT": DEPENDENCY_PROOF_DEBT,
        "DEPENDENCY-PROOF-DEBT": DEPENDENCY_PROOF_DEBT,
        "DEPENDENCY PROOF DEBT": DEPENDENCY_PROOF_DEBT,
        "MECHANISM_BLOCKER": MECHANISM_BLOCKER,
        "MECHANISM-BLOCKER": MECHANISM_BLOCKER,
        "NEEDS_DECOMPOSITION": NEEDS_DECOMPOSITION,
        "NEEDS-DECOMPOSITION": NEEDS_DECOMPOSITION,
        "NEEDS DECOMPOSITION": NEEDS_DECOMPOSITION,
        "USER_INTERRUPTED": USER_INTERRUPTED,
        "USER-INTERRUPTED": USER_INTERRUPTED,
    }
    status = aliases.get(status, status)
    if status in REPORTING_TERMINAL_STATUSES or status in {NONTERMINAL, NEEDS_DECOMPOSITION}:
        return status
    return NONTERMINAL


def _normalize_task_level_status(raw: Any) -> str:
    status = str(raw or "").strip().lower().replace("-", "_")
    if status in {"pass", "fail", "blocked", "allowed_exception"}:
        return status
    return ""


def _normalize_report_status(raw: Any) -> str:
    status = str(raw or "").strip().lower().replace("-", "_")
    if status in {"pass", "fail", "blocked", "allowed_exception", "needs_fresh_review", "needs_class_normalization"}:
        return status
    return ""


def _normalize_class_value(raw: Any) -> str:
    return str(raw or "").strip().lower().replace("-", "_").replace("/", "_").replace(" ", "_")


def _task_level_projection_from_raw(task_id: str, raw_task: dict[str, Any]) -> tuple[str, str, str, str, str]:
    task_status = _normalize_task_level_status(raw_task.get("phase2_status", raw_task.get("phase2_task_status")))
    task_status_reason = str(
        raw_task.get("phase2_status_reason", raw_task.get("phase2_task_status_reason", "")) or ""
    ).strip()
    task_status_evidence_type = str(
        raw_task.get("phase2_status_evidence_type", raw_task.get("phase2_task_status_evidence_type", "")) or ""
    ).strip()
    review_verdict = str(raw_task.get("phase2_review_verdict", "") or raw_task.get("review_verdict", "") or "").strip().lower()
    proof_class = str(
        raw_task.get("phase2_proof_class", "")
        or raw_task.get("proof_class", "")
        or raw_task.get("completion_class", "")
        or ""
    ).strip()
    completion_class = raw_task.get("phase2_completion_class", raw_task.get("completion_class", ""))
    if not task_status and (review_verdict or proof_class):
        projection = classify_phase2_task_status(
            task_id=task_id,
            task_type=str(raw_task.get("type", "") or raw_task.get("task_type", "") or ""),
            review_verdict=review_verdict,
            proof_class=proof_class,
            completion_class=completion_class,
        )
        task_status = projection.task_status
        task_status_reason = projection.reason
        task_status_evidence_type = projection.evidence_type
        proof_class = projection.proof_class or proof_class
    return task_status, task_status_reason, task_status_evidence_type, review_verdict, proof_class


def _hard_failed_roots(task_map: dict[str, dict[str, Any]]) -> set[str]:
    roots: set[str] = set()
    for task_id, raw_task in task_map.items():
        status = _normalize_status(raw_task.get("status"))
        stop_reason = str(raw_task.get("stop_reason", "") or "").strip()
        if (
            status == FAILED_LOCAL
            and stop_reason in ROOT_DEPENDENCY_FAILURE_REASONS
            and phase2_failure_counters_from_task(raw_task).exhausted
        ):
            roots.add(task_id)
    return roots


def _phase2_blocking_roots(
    task_map: dict[str, dict[str, Any]],
    *,
    allowed_beyond_book_tasks: set[str],
) -> set[str]:
    roots: set[str] = set()
    for task_id, raw_task in task_map.items():
        status = _normalize_status(raw_task.get("status"))
        task_status, _, task_status_evidence_type, _, _ = _task_level_projection_from_raw(task_id, raw_task)
        report_status = _normalize_report_status(
            raw_task.get("phase2_status", raw_task.get("phase2_task_status"))
        )
        if _is_allowed_beyond_book_exception(
            task_id,
            raw_task,
            status=status,
            allowed_beyond_book_tasks=allowed_beyond_book_tasks,
        ):
            continue
        if (
            status in {COMPLETED, COMPLETED_WITH_PROOF_DEBT}
            and status == COMPLETED_WITH_PROOF_DEBT
            and task_status not in {"fail", "blocked"}
            and report_status not in {"needs_fresh_review", "needs_class_normalization"}
            and task_status_evidence_type != "needs_class_normalization"
        ):
            # Proof debt has its own transitive gate and report classification.
            continue
        if (
            status == COMPLETED
            and task_status == "pass"
            and report_status not in {"needs_fresh_review", "needs_class_normalization"}
            and task_status_evidence_type != "needs_class_normalization"
        ):
            continue
        # Fail closed: a hard dependency is consumable only with current
        # COMPLETED+pass authority (or the explicit exception handled above).
        # This includes absent/blank status, NONTERMINAL, stale review, fail,
        # blocked, and unknown/unregistered dependency placeholders.
        roots.add(task_id)
    return roots


def _task_has_family_consumable_support(raw_task: dict[str, Any]) -> bool:
    proof_class = _normalize_class_value(
        raw_task.get("phase2_proof_class", "")
        or raw_task.get("proof_class", "")
        or raw_task.get("completion_class", "")
    )
    completion_class = _normalize_class_value(
        raw_task.get("phase2_completion_class", "")
        or raw_task.get("completion_class", "")
    )
    if proof_class not in FAMILY_CONSUMABLE_PROOF_CLASSES:
        return False
    if completion_class not in FAMILY_CONSUMABLE_COMPLETION_CLASSES:
        return False
    return True


def _proof_debt_roots(
    task_map: dict[str, dict[str, Any]],
    *,
    objective: str,
    allowed_beyond_book_tasks: set[str],
) -> set[str]:
    roots: set[str] = set()
    for task_id, raw_task in task_map.items():
        status = _normalize_status(raw_task.get("status"))
        if status == COMPLETED_WITH_PROOF_DEBT:
            if (
                objective == TEXTBOOK_COMPLETE_OBJECTIVE
                and _is_allowed_beyond_book_exception(
                    task_id,
                    raw_task,
                    status=COMPLETED_WITH_PROOF_DEBT,
                    allowed_beyond_book_tasks=allowed_beyond_book_tasks,
                )
            ):
                continue
            roots.add(task_id)
    return roots


def _first_failed_transitive_dependency(
    task_id: str,
    task_map: dict[str, dict[str, Any]],
    hard_failed_roots: set[str],
) -> str:
    seen: set[str] = set()
    stack = list(reversed(canonicalize_id_list(task_map[task_id].get("dependencies", []))))
    while stack:
        dep_id = stack.pop()
        if dep_id in seen:
            continue
        seen.add(dep_id)
        if dep_id in hard_failed_roots:
            return dep_id
        dep_task = task_map.get(dep_id)
        if isinstance(dep_task, dict):
            stack.extend(reversed(canonicalize_id_list(dep_task.get("dependencies", []))))
    return ""


def _first_blocked_transitive_dependency(
    task_id: str,
    task_map: dict[str, dict[str, Any]],
    phase2_blocking_roots: set[str],
) -> str:
    seen: set[str] = set()
    stack = list(reversed(canonicalize_id_list(task_map[task_id].get("dependencies", []))))
    while stack:
        dep_id = stack.pop()
        if dep_id in seen:
            continue
        seen.add(dep_id)
        if dep_id in phase2_blocking_roots:
            return dep_id
        dep_task = task_map.get(dep_id)
        if not isinstance(dep_task, dict):
            return dep_id
        stack.extend(reversed(canonicalize_id_list(dep_task.get("dependencies", []))))
    return ""


def _first_proof_debt_transitive_dependency(
    task_id: str,
    task_map: dict[str, dict[str, Any]],
    proof_debt_roots: set[str],
) -> str:
    seen: set[str] = set()
    stack = list(reversed(canonicalize_id_list(task_map[task_id].get("dependencies", []))))
    while stack:
        dep_id = stack.pop()
        if dep_id in seen:
            continue
        seen.add(dep_id)
        if dep_id in proof_debt_roots:
            return dep_id
        dep_task = task_map.get(dep_id)
        if isinstance(dep_task, dict):
            stack.extend(reversed(canonicalize_id_list(dep_task.get("dependencies", []))))
    return ""


def _row_issue(
    *,
    task_id: str,
    status: str,
    stop_reason: str,
    raw_task: dict[str, Any],
    budget: FailureBudget,
    counters: Phase2FailureCounters,
    failed_dependency: str,
    blocked_dependency: str,
    proof_debt_dependency: str,
    allowed_beyond_book_exception: bool,
) -> str:
    if failed_dependency and status != DEPENDENCY_FAILED:
        return f"depends on failed root {failed_dependency} but is not dependency-failed"
    if status == DEPENDENCY_FAILED and not failed_dependency:
        return "dependency-failed without a failed hard dependency in this batch"
    if proof_debt_dependency and status != DEPENDENCY_PROOF_DEBT:
        return f"depends on proof-debt root {proof_debt_dependency} but is not proof-debt-blocked"
    if status == DEPENDENCY_PROOF_DEBT and not proof_debt_dependency:
        return "dependency-proof-debt without an upstream accepted proof debt in this batch"
    if status == COMPLETED_WITH_PROOF_DEBT and not allowed_beyond_book_exception:
        return "legacy non-clean proof-debt status remains; re-review and repair the source spine before downstream use"
    if status == COMPLETED_WITH_PROOF_DEBT and allowed_beyond_book_exception:
        return ""
    if status == NEEDS_DECOMPOSITION:
        return "requires concrete proof-obligation decomposition before blocker/failure admission"
    if _early_hard_failure_before_budget(_normalize_status(raw_task.get("status")), stop_reason, counters):
        return (
            "hard_failure before build/review failure streak reaches 15 "
            f"(build={counters.build_fail_counter}/{counters.limit}, review={counters.review_fail_counter}/{counters.limit})"
        )
    if status == NONTERMINAL:
        return "nonterminal"
    return ""


def _next_action(
    *,
    status: str,
    issue: str,
    failed_dependency: str,
    blocked_dependency: str,
    proof_debt_dependency: str,
    objective: str,
    allowed_beyond_book_exception: bool,
) -> str:
    if status == COMPLETED:
        return "none"
    if status == COMPLETED_WITH_PROOF_DEBT:
        if allowed_beyond_book_exception:
            return "none; allowed beyond-book exception"
        return "run review-now --review-subject existing"
    if status == DEPENDENCY_FAILED:
        return f"skip; blocked by {failed_dependency}" if failed_dependency else "skip; dependency failed"
    if blocked_dependency:
        return f"skip; blocked by {blocked_dependency}"
    if status == DEPENDENCY_PROOF_DEBT:
        if objective == TEXTBOOK_COMPLETE_OBJECTIVE:
            return (
                f"repair proof-debt root {proof_debt_dependency} before downstream"
                if proof_debt_dependency
                else "repair upstream proof debt before downstream"
            )
        return (
            f"skip; blocked by proof debt in {proof_debt_dependency}"
            if proof_debt_dependency
            else "skip; dependency proof debt"
        )
    if status == FAILED_LOCAL:
        return "audit root failure"
    if status == MECHANISM_BLOCKER:
        return "resolve mechanism blocker or record user decision"
    if status == USER_INTERRUPTED:
        return "resume only on explicit user direction"
    if status == NEEDS_DECOMPOSITION:
        return "legacy decomposition status; repair named source steps through the ordinary review loop"
    if issue:
        return "continue or repair before final summary"
    return "continue independent task"


def _normalize_objective(raw: str) -> str:
    objective = str(raw or "").strip().lower().replace("_", "-")
    if objective not in OBJECTIVES:
        raise ValueError(f"Unsupported batch objective: {raw}")
    return objective


def _objective_terminal(
    *,
    status: str,
    objective: str,
    report_terminal: bool,
    clean_or_allowed_exception: bool,
) -> bool:
    if objective == DIAGNOSTIC_OBJECTIVE:
        return report_terminal
    if clean_or_allowed_exception:
        return True
    return status in {FAILED_LOCAL, DEPENDENCY_FAILED, MECHANISM_BLOCKER, USER_INTERRUPTED}


def _is_allowed_beyond_book_exception(
    task_id: str,
    raw_task: dict[str, Any],
    *,
    status: str,
    allowed_beyond_book_tasks: set[str],
) -> bool:
    if canonicalize_block_id(task_id) not in allowed_beyond_book_tasks:
        return False
    task_status = _normalize_task_level_status(raw_task.get("phase2_status", raw_task.get("phase2_task_status")))
    if task_status == "allowed_exception":
        return True
    if status != COMPLETED_WITH_PROOF_DEBT:
        return False
    current_class = str(raw_task.get("current_class", "") or raw_task.get("primary_class", "") or "").strip()
    if current_class == "beyond_book_exception":
        return True
    return False


def _is_complex_retry(raw_task: dict[str, Any]) -> bool:
    if bool(raw_task.get("complex_retry_after_under_evidenced_hard_stop")):
        return True
    if bool(raw_task.get("renewed_complex_retry")):
        return True
    return bool(raw_task.get("complex")) and bool(raw_task.get("under_evidenced_hard_stop"))


def _early_hard_failure_before_budget(status: str, stop_reason: str, counters: Phase2FailureCounters) -> bool:
    return status == FAILED_LOCAL and stop_reason == "hard_failure" and not counters.exhausted


def _skip_failure_event_reason(event: dict[str, Any]) -> str:
    kind = _normalize_failure_kind(event.get("kind") or event.get("stage"))
    if kind not in SUBSTANTIVE_FAILURE_KINDS:
        return f"uncounted kind {kind or '(missing)'}"
    if bool(event.get("setup_failure")) or bool(event.get("missing_reviewer_config")):
        return "setup/configuration failure"
    if bool(event.get("dependency_failed")):
        return "dependency-failed skip"
    if bool(event.get("mechanism_blocker")):
        return "mechanism blocker"
    if event.get("canonical_result") is False:
        return "missing canonical result"
    if kind == "build_check_failure" and not _meaningful_change(event):
        return "build-check failure without meaningful candidate or plan change"
    if kind in {"semantic_review_fail", "semantic_review_inconclusive"} and event.get("build_ready") is False:
        return "semantic review was not of a build-ready candidate"
    if kind == "review_apply_rejection":
        rejection_class = str(event.get("rejection_class", "") or "").strip().lower()
        if rejection_class not in REVIEW_APPLY_COUNTED_CLASSES:
            return "review-apply rejection was not semantic/freshness"
    return ""


def _normalize_failure_kind(raw: Any) -> str:
    kind = str(raw or "").strip().lower().replace("-", "_").replace(" ", "_")
    aliases = {
        "build_check": "build_check_failure",
        "build_failed": "build_check_failure",
        "build_failure": "build_check_failure",
        "semantic_review": "semantic_review_fail",
        "review_fail": "semantic_review_fail",
        "review_inconclusive": "semantic_review_inconclusive",
        "apply_rejection": "review_apply_rejection",
        "review_apply": "review_apply_rejection",
    }
    return aliases.get(kind, kind)


def _meaningful_change(event: dict[str, Any]) -> bool:
    return bool(
        event.get("candidate_changed")
        or event.get("plan_changed")
        or event.get("strategy_changed")
        or event.get("decomposition_changed")
        or event.get("meaningful_change")
    )


def _event_strategy_key(event: dict[str, Any]) -> str:
    parts = [
        str(event.get("candidate_hash", "") or ""),
        str(event.get("plan_hash", "") or ""),
        str(event.get("strategy_key", "") or ""),
        str(event.get("decomposition_hash", "") or ""),
    ]
    return "|".join(parts)


if __name__ == "__main__":
    raise SystemExit(main())
