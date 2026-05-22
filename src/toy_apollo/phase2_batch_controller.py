from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from src.block_id_naming import canonicalize_block_id, canonicalize_id_list
from src.toy_apollo.phase2_failure_budget import (
    PHASE2_FAILURE_STREAK_LIMIT,
    Phase2FailureCounters,
    phase2_failure_counters_from_task,
)
from src.toy_apollo.phase2_proof_obligations import needs_concrete_decomposition as proof_obligations_need_concrete


COMPLETED = "COMPLETED"
COMPLETED_WITH_PROOF_DEBT = "COMPLETED_WITH_PROOF_DEBT"
FAILED_LOCAL = "FAILED_LOCAL"
DEPENDENCY_FAILED = "DEPENDENCY_FAILED"
DEPENDENCY_PROOF_DEBT = "DEPENDENCY_PROOF_DEBT"
MECHANISM_BLOCKER = "MECHANISM_BLOCKER"
USER_INTERRUPTED = "USER_INTERRUPTED"
NEEDS_DECOMPOSITION = "NEEDS_DECOMPOSITION"
NONTERMINAL = "NONTERMINAL"

TERMINAL_STATUSES = {
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
    stop_reason: str = ""
    dependencies: tuple[str, ...] = ()
    failed_dependency: str = ""
    proof_debt_dependency: str = ""
    substantive_failures: int = 0
    build_fail_streak: int = 0
    review_fail_streak: int = 0
    retry_budget_required: int = COMPLEX_RETRY_BUDGET
    retry_budget_exhausted: bool = False
    terminal: bool = False
    issue: str = ""
    next_action: str = ""


@dataclass(frozen=True)
class BatchReport:
    batch_id: str
    rows: tuple[BatchTaskRow, ...]
    issues: tuple[str, ...] = ()

    @property
    def all_terminal(self) -> bool:
        return all(row.terminal for row in self.rows)

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


def analyze_batch_state(payload: dict[str, Any]) -> BatchReport:
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
    proof_debt_roots = _proof_debt_roots(task_map)
    rows: list[BatchTaskRow] = []
    for task_id in sorted(task_map):
        raw_task = task_map[task_id]
        declared_status = _normalize_status(raw_task.get("status"))
        stop_reason = str(raw_task.get("stop_reason", "") or "").strip()
        dependencies = tuple(canonicalize_id_list(raw_task.get("dependencies", [])))
        failed_dependency = _first_failed_transitive_dependency(task_id, task_map, hard_failed_roots)
        proof_debt_dependency = (
            ""
            if failed_dependency
            else _first_proof_debt_transitive_dependency(task_id, task_map, proof_debt_roots)
        )
        counters = phase2_failure_counters_from_task(raw_task)

        status = COMPLETED_WITH_PROOF_DEBT if declared_status == COMPLETED and _task_has_accepted_proof_debt(raw_task) else declared_status
        if _task_needs_concrete_decomposition(raw_task) and declared_status not in {COMPLETED, COMPLETED_WITH_PROOF_DEBT}:
            status = NEEDS_DECOMPOSITION
        elif _early_hard_failure_before_budget(declared_status, stop_reason, counters):
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

        budget = count_substantive_failures(raw_task.get("failure_events", raw_task.get("substantive_failures", [])))
        issue = _row_issue(
            task_id=task_id,
            status=status,
            stop_reason=stop_reason,
            raw_task=raw_task,
            budget=budget,
            counters=counters,
            failed_dependency=failed_dependency,
            proof_debt_dependency=proof_debt_dependency,
        )
        next_action = _next_action(
            status=status,
            issue=issue,
            failed_dependency=failed_dependency,
            proof_debt_dependency=proof_debt_dependency,
        )
        rows.append(
            BatchTaskRow(
                task_id=task_id,
                status=status,
                declared_status=declared_status,
                stop_reason=stop_reason,
                dependencies=dependencies,
                failed_dependency=failed_dependency,
                proof_debt_dependency=proof_debt_dependency,
                substantive_failures=budget.counted,
                build_fail_streak=counters.build_fail_counter,
                review_fail_streak=counters.review_fail_counter,
                retry_budget_required=budget.required,
                retry_budget_exhausted=counters.exhausted,
                terminal=status in TERMINAL_STATUSES,
                issue=issue,
                next_action=next_action,
            )
        )

    return BatchReport(batch_id=batch_id, rows=tuple(rows), issues=tuple(issues))


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
        f"- All terminal: `{str(report.all_terminal).lower()}`",
    ]
    for status in sorted(report.counts):
        lines.append(f"- {status}: `{report.counts[status]}`")
    if report.issues:
        lines.append("- Batch issues: `" + "; ".join(report.issues) + "`")
    lines.extend(
        [
            "",
            "| task_id | status | stop_reason | failed_dependency | proof_debt_dependency | substantive_failures | terminal | next_action | issue |",
            "| --- | --- | --- | --- | --- | ---: | --- | --- | --- |",
        ]
    )
    for row in report.rows:
        lines.append(
            "| {task_id} | {status} | {stop_reason} | {failed_dependency} | {proof_debt_dependency} | {failures} | {terminal} | {next_action} | {issue} |".format(
                task_id=row.task_id,
                status=row.status,
                stop_reason=row.stop_reason or "",
                failed_dependency=row.failed_dependency or "",
                proof_debt_dependency=row.proof_debt_dependency or "",
                failures=row.substantive_failures,
                terminal=str(row.terminal).lower(),
                next_action=row.next_action,
                issue=row.issue,
            )
        )
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Report ToyApollo Phase 2 batch-controller checklist state.")
    parser.add_argument("state", help="Path to a batch-controller JSON checklist.")
    parser.add_argument("--json", action="store_true", dest="as_json", help="Emit normalized report JSON.")
    args = parser.parse_args(argv)

    try:
        report = analyze_batch_state(load_batch_state(args.state))
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    if args.as_json:
        payload = {
            "batch_id": report.batch_id,
            "all_terminal": report.all_terminal,
            "counts": report.counts,
            "issues": list(report.issues),
            "tasks": [
                {
                    "task_id": row.task_id,
                    "status": row.status,
                    "declared_status": row.declared_status,
                    "stop_reason": row.stop_reason,
                    "failed_dependency": row.failed_dependency,
                    "proof_debt_dependency": row.proof_debt_dependency,
                    "substantive_failures": row.substantive_failures,
                    "build_fail_streak": row.build_fail_streak,
                    "review_fail_streak": row.review_fail_streak,
                    "retry_budget_required": row.retry_budget_required,
                    "retry_budget_exhausted": row.retry_budget_exhausted,
                    "terminal": row.terminal,
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
    if status in TERMINAL_STATUSES or status in {NONTERMINAL, NEEDS_DECOMPOSITION}:
        return status
    return NONTERMINAL


def _hard_failed_roots(task_map: dict[str, dict[str, Any]]) -> set[str]:
    roots: set[str] = set()
    for task_id, raw_task in task_map.items():
        status = _normalize_status(raw_task.get("status"))
        stop_reason = str(raw_task.get("stop_reason", "") or "").strip()
        if (
            status == FAILED_LOCAL
            and stop_reason in ROOT_DEPENDENCY_FAILURE_REASONS
            and not _task_needs_concrete_decomposition(raw_task)
            and phase2_failure_counters_from_task(raw_task).exhausted
        ):
            roots.add(task_id)
    return roots


def _proof_debt_roots(task_map: dict[str, dict[str, Any]]) -> set[str]:
    roots: set[str] = set()
    for task_id, raw_task in task_map.items():
        status = _normalize_status(raw_task.get("status"))
        if status == COMPLETED_WITH_PROOF_DEBT or (status == COMPLETED and _task_has_accepted_proof_debt(raw_task)):
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
    proof_debt_dependency: str,
) -> str:
    if failed_dependency and status != DEPENDENCY_FAILED:
        return f"depends on failed root {failed_dependency} but is not dependency-failed"
    if status == DEPENDENCY_FAILED and not failed_dependency:
        return "dependency-failed without a failed hard dependency in this batch"
    if proof_debt_dependency and status != DEPENDENCY_PROOF_DEBT:
        return f"depends on proof-debt root {proof_debt_dependency} but is not proof-debt-blocked"
    if status == DEPENDENCY_PROOF_DEBT and not proof_debt_dependency:
        return "dependency-proof-debt without an upstream accepted proof debt in this batch"
    if status == COMPLETED_WITH_PROOF_DEBT:
        return "accepted proof debt remains; run debt-fix before downstream use"
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


def _next_action(*, status: str, issue: str, failed_dependency: str, proof_debt_dependency: str) -> str:
    if status == COMPLETED:
        return "none"
    if status == COMPLETED_WITH_PROOF_DEBT:
        return "run debt-fix"
    if status == DEPENDENCY_FAILED:
        return f"skip; blocked by {failed_dependency}" if failed_dependency else "skip; dependency failed"
    if status == DEPENDENCY_PROOF_DEBT:
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
        return "split proof_obligations into concrete source nodes"
    if issue:
        return "continue or repair before final summary"
    return "continue independent task"


def _task_has_accepted_proof_debt(raw_task: dict[str, Any]) -> bool:
    summary = raw_task.get("proof_obligation_summary")
    if isinstance(summary, dict):
        status_counts = summary.get("status_counts", {})
        if _status_counts_include_proof_debt(status_counts):
            return True

    obligations = raw_task.get("proof_obligations")
    if isinstance(obligations, dict):
        if _status_counts_include_proof_debt(obligations.get("status_counts", {})):
            return True
        for item in obligations.get("obligations", []) if isinstance(obligations.get("obligations", []), list) else []:
            if isinstance(item, dict) and str(item.get("status", "") or "").strip().lower() == "accepted_as_proof_debt":
                return True

    obligation_review = raw_task.get("obligation_review")
    if isinstance(obligation_review, dict):
        for item in obligation_review.get("items", []) if isinstance(obligation_review.get("items", []), list) else []:
            if isinstance(item, dict) and str(item.get("status", "") or "").strip().lower() == "accepted_as_proof_debt":
                return True

    return False


def _status_counts_include_proof_debt(status_counts: Any) -> bool:
    if not isinstance(status_counts, dict):
        return False
    try:
        return int(status_counts.get("accepted_as_proof_debt", 0) or 0) > 0
    except (TypeError, ValueError):
        return False


def _task_needs_concrete_decomposition(raw_task: dict[str, Any]) -> bool:
    if bool(raw_task.get("needs_concrete_decomposition")) or bool(raw_task.get("needs_decomposition")):
        return True
    summary = raw_task.get("proof_obligation_summary")
    if isinstance(summary, dict) and bool(summary.get("needs_concrete_decomposition")):
        return True
    obligations = raw_task.get("proof_obligations")
    if isinstance(obligations, dict):
        return proof_obligations_need_concrete(obligations)
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
