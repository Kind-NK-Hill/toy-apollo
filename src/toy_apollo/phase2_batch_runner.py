from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path
from typing import Any

from src.block_id_naming import canonicalize_block_id

from .phase2_batch_controller import BatchReport, analyze_batch_state


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


@dataclass(frozen=True)
class BatchRunnerExecution:
    plan: BatchRunnerPlan
    executed: tuple[BatchRunnerAction, ...]
    details: tuple[str, ...]


def build_live_batch_state(task_ids: list[str], ledger, *, batch_id: str = "live-ledger") -> dict[str, Any]:
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
        tasks.append(_batch_task_from_ledger_record(task_id, record))
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
) -> BatchRunnerPlan:
    state = build_live_batch_state(task_ids, ledger)
    report = analyze_batch_state(state, objective=objective)
    raw_tasks = {str(task.get("task_id", "")): task for task in state.get("tasks", []) if isinstance(task, dict)}
    fanout = _transitive_fanout(raw_tasks)
    actions = tuple(
        _action_for_row(row, settings, raw_tasks.get(row.task_id, {}), fanout.get(row.task_id, 0))
        for row in report.rows
    )
    actions = _select_worker_queue(
        actions,
        task_kinds=task_kinds or (),
        limit=limit,
        worker_slots=worker_slots,
    )
    return BatchRunnerPlan(report=report, actions=actions)


def render_batch_runner_plan(plan: BatchRunnerPlan) -> str:
    lines = [
        "# Phase2 Batch Runner Plan",
        "",
        f"- batch_id: `{plan.report.batch_id}`",
        f"- objective: `{plan.report.objective}`",
        f"- all_clean_or_allowed_exception: `{str(plan.report.all_clean_or_allowed_exception).lower()}`",
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


def _batch_task_from_ledger_record(task_id: str, record: dict[str, Any]) -> dict[str, Any]:
    return {
        "task_id": task_id,
        "status": record.get("status", ""),
        "type": record.get("type", record.get("task_type", "")),
        "dependencies": _dependencies_from_record(record),
        "phase2_status": record.get("phase2_status", record.get("phase2_task_status", "")),
        "phase2_status_reason": record.get(
            "phase2_status_reason",
            record.get("phase2_task_status_reason", ""),
        ),
        "phase2_status_evidence_type": record.get(
            "phase2_status_evidence_type",
            record.get("phase2_task_status_evidence_type", ""),
        ),
        "review_verdict": record.get("review_verdict", record.get("current_review_verdict", "")),
        "proof_class": record.get("phase2_proof_class", record.get("proof_class", record.get("completion_class", ""))),
        "current_class": record.get("current_class", ""),
        "stop_reason": record.get("stop_reason", record.get("current_auto_loop_stop_reason", "")),
        "proof_obligation_summary": record.get("proof_obligation_summary", {}),
        "failure_events": record.get("failure_events", []),
        "build_fail_counter": record.get("build_fail_counter", 0),
        "review_fail_counter": record.get("review_fail_counter", 0),
        "latest_verify_result_file": record.get("latest_verify_result_file", ""),
        "latest_verify_failure": _latest_verify_failure(record.get("latest_verify_result_file", "")),
    }


def _dependencies_from_record(record: dict[str, Any]) -> list[str]:
    for key in (
        "dependencies",
        "selected_dependencies",
        "phase2_dependencies",
        "soft_imports",
        "candidate_soft_imports",
    ):
        raw = record.get(key)
        if isinstance(raw, list):
            return [canonicalize_block_id(str(item)) for item in raw if canonicalize_block_id(str(item))]
    return []


def _action_for_row(
    row,
    settings,
    raw_task: dict[str, Any] | None = None,
    fanout: int = 0,
) -> BatchRunnerAction:
    raw_task = raw_task if isinstance(raw_task, dict) else {}
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
    if row.task_status == "blocked":
        return action("blocked", "", row.task_status_reason or "dependency gate blocked")
    if row.report_status in {"needs_fresh_review", "needs_class_normalization"}:
        if _official_output_exists(settings, row.task_id):
            return action(
                "review_existing",
                _phase2_command("review-now", row.task_id, "--review-subject existing"),
                row.task_status_reason or "official output needs a fresh classified semantic review",
            )
        return action(
            "restore_or_rebuild_output",
            "",
            "fresh existing review is needed, but no official output file was found",
        )
    if row.task_status == "fail":
        return action(
            "auto_loop",
            _phase2_command("auto-loop", row.task_id, "--review-subject current"),
            row.task_status_reason or row.issue or "task-level proof status is not pass",
        )
    verify_failure = raw_task.get("latest_verify_failure", {})
    if isinstance(verify_failure, dict) and verify_failure:
        return action(
            "auto_loop",
            _phase2_command("auto-loop", row.task_id, "--review-subject current"),
            str(verify_failure.get("summary", "") or "latest verify result failed; repair through auto-loop"),
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
        if action.action not in {"none", "skip_blocked", "blocked"}
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


def _action_priority(action: str) -> int:
    return {
        "auto_loop": 0,
        "review_existing": 1,
        "restore_or_rebuild_output": 2,
        "inspect": 3,
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
