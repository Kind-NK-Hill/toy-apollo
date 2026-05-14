from __future__ import annotations

import json
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from src.block_id_naming import canonicalize_block_id, canonicalize_id_list, extract_chapter

from .core import LedgerManager, TaskStatus
from .integrations.offload_queue import build_plan_task_index
from .phase3_softdep_pack import build_selection_scope_id

PROBLEM_TYPE = "problem"


def _utc_stamp() -> str:
    return datetime.now(UTC).isoformat().replace("+00:00", "Z")


def _task_type(task: dict[str, Any]) -> str:
    return str(task.get("type", "")).strip().lower()


def _validate_problem_tasks(task_ids: list[str], plan_index: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    tasks: list[dict[str, Any]] = []
    for task_id in task_ids:
        task = plan_index.get(task_id)
        if task is None:
            raise FileNotFoundError(f"Task {task_id} was not found in plans/*.json")
        if _task_type(task) != PROBLEM_TYPE:
            raise ValueError(f"plan-batches only supports problem tasks: {task_id}")
        tasks.append(task)
    return tasks


def _effective_context(task: dict[str, Any], ledger: LedgerManager) -> dict[str, list[str]]:
    task_id = canonicalize_block_id(task["block_id"])
    record = ledger.ledger.get("tasks", {}).get(task_id, {})
    snapshot = record.get("candidate_snapshot", {}) if isinstance(record.get("candidate_snapshot"), dict) else {}
    hard_deps = canonicalize_id_list(task.get("dependencies", []))
    soft_imports = canonicalize_id_list(snapshot.get("soft_imports", []))
    return {
        "hard_dependencies": hard_deps,
        "soft_imports": soft_imports,
        "final_import_union": canonicalize_id_list(hard_deps + soft_imports),
    }


def _dep_status(ledger: LedgerManager, dep_id: str) -> str:
    dep_id = canonicalize_block_id(dep_id)
    if not dep_id:
        return "UNKNOWN"
    return str(ledger.ledger.get("tasks", {}).get(dep_id, {}).get("status", "UNKNOWN"))


def _ready_reason(task_id: str, selected_problem_deps: list[str], hard_deps: list[str], soft_imports: list[str]) -> str:
    if not selected_problem_deps:
        return (
            f"{task_id} has no unresolved problem-to-problem hard dependencies in the selected scope. "
            f"All non-problem imports in final union (hard={len(hard_deps)}, soft={len(soft_imports)}) are already COMPLETED."
        )
    joined = ", ".join(selected_problem_deps)
    return (
        f"{task_id} is ready because its problem dependencies [{joined}] are assigned to earlier execution batches, "
        f"and all non-problem imports in final union (hard={len(hard_deps)}, soft={len(soft_imports)}) are already COMPLETED."
    )


def _render_plan_markdown(scope_id: str, chapter: int | None, task_ids: list[str], plan_payload: dict[str, Any]) -> str:
    lines = [
        f"# Phase3 Execution Batch Plan for {scope_id}",
        "",
        f"- Chapter: `{chapter}`" if chapter is not None else "- Chapter: unknown",
        f"- Generated at: `{plan_payload['generated_at']}`",
        f"- Tasks in scope: `{', '.join(task_ids)}`",
        "",
        "## Batches",
        "",
    ]

    batches = plan_payload.get("batches", [])
    if not batches:
        lines.append("- No executable batches were produced.")
    else:
        for batch in batches:
            lines.append(f"### `{batch['batch_id']}`")
            lines.append("")
            for entry in batch.get("tasks", []):
                lines.append(f"- `{entry['task_id']}`")
                lines.append(f"  - hard deps: `{', '.join(entry['hard_dependencies']) if entry['hard_dependencies'] else '(none)'}`")
                lines.append(f"  - soft imports: `{', '.join(entry['soft_imports']) if entry['soft_imports'] else '(none)'}`")
                lines.append(f"  - final import union: `{', '.join(entry['final_import_union']) if entry['final_import_union'] else '(none)'}`")
                lines.append(f"  - blocked by: `{', '.join(entry['blocked_by']) if entry['blocked_by'] else '(none)'}`")
                lines.append(f"  - ready reason: {entry['ready_reason']}")
            lines.append("")

    lines.extend(["## Unscheduled", ""])
    unscheduled = plan_payload.get("unscheduled", [])
    if not unscheduled:
        lines.append("- None")
    else:
        for entry in unscheduled:
            lines.append(f"- `{entry['task_id']}`")
            lines.append(f"  - blocked by: `{', '.join(entry['blocked_by']) if entry['blocked_by'] else '(none)'}`")
            lines.append(
                f"  - missing completed deps: `{', '.join(entry['missing_completed_deps']) if entry['missing_completed_deps'] else '(none)'}`"
            )
            lines.append(f"  - reason: {entry['reason']}")
    lines.append("")
    return "\n".join(lines)


def write_execution_batch_plan(task_ids: list[str], ledger: LedgerManager, settings) -> Path:
    task_ids = canonicalize_id_list(task_ids)
    if not task_ids:
        raise ValueError("No valid task ids provided for plan-batches.")

    plan_index = build_plan_task_index(settings.plans_dir)
    tasks = _validate_problem_tasks(task_ids, plan_index)

    chapters = {extract_chapter(task["block_id"]) for task in tasks}
    if len(chapters) != 1 or None in chapters:
        raise ValueError("plan-batches requires all tasks to belong to the same chapter.")
    chapter = next(iter(chapters))

    for task_id in task_ids:
        if not ledger.has_confirmed_soft_imports(task_id):
            raise ValueError(
                f"Problem task {task_id} does not have confirmed soft selection. "
                "Run --phase 3 --phase3-mode soft-pack/soft-apply first."
            )

    scope_id = build_selection_scope_id(task_ids)
    output_root = settings.phase3_execution_batches_dir
    if output_root is None:
        raise ValueError("phase3_execution_batches_dir is not configured.")
    plan_dir = output_root / scope_id
    plan_dir.mkdir(parents=True, exist_ok=True)

    selected_set = set(task_ids)
    completed_or_planned: set[str] = {
        task_id
        for task_id in selected_set
        if _dep_status(ledger, task_id) == TaskStatus.COMPLETED.value
    }

    task_details: dict[str, dict[str, Any]] = {}
    unscheduled: dict[str, dict[str, Any]] = {}
    for task in tasks:
        task_id = canonicalize_block_id(task["block_id"])
        ctx = _effective_context(task, ledger)
        hard_deps = ctx["hard_dependencies"]
        soft_imports = ctx["soft_imports"]
        final_union = ctx["final_import_union"]
        blocking_problem_deps = [dep for dep in hard_deps if dep in selected_set and dep not in completed_or_planned]
        missing_completed_deps: list[str] = []
        for dep in final_union:
            dep_id = canonicalize_block_id(dep)
            if not dep_id:
                continue
            if dep_id in selected_set:
                continue
            if _dep_status(ledger, dep_id) != TaskStatus.COMPLETED.value:
                missing_completed_deps.append(dep_id)
        task_details[task_id] = {
            "task_id": task_id,
            "hard_dependencies": hard_deps,
            "soft_imports": soft_imports,
            "final_import_union": final_union,
            "blocking_problem_deps": blocking_problem_deps,
            "missing_completed_deps": canonicalize_id_list(missing_completed_deps),
        }

    batches: list[dict[str, Any]] = []
    remaining = [task_id for task_id in task_ids if _dep_status(ledger, task_id) != TaskStatus.COMPLETED.value]
    batch_num = 0
    while remaining:
        ready_now: list[str] = []
        for task_id in remaining:
            details = task_details[task_id]
            unresolved_problem_deps = [
                dep for dep in details["blocking_problem_deps"] if dep not in completed_or_planned
            ]
            if details["missing_completed_deps"]:
                continue
            if unresolved_problem_deps:
                continue
            ready_now.append(task_id)

        if not ready_now:
            for task_id in remaining:
                details = task_details[task_id]
                unresolved_problem_deps = [
                    dep for dep in details["blocking_problem_deps"] if dep not in completed_or_planned
                ]
                unscheduled[task_id] = {
                    "task_id": task_id,
                    "blocked_by": unresolved_problem_deps,
                    "missing_completed_deps": details["missing_completed_deps"],
                    "reason": (
                        "Task is not ready for Aristotle offload because it still depends on unresolved problem tasks "
                        "or on non-problem imports that are not COMPLETED."
                    ),
                }
            break

        batch_num += 1
        batch_id = f"{scope_id}__batch_{batch_num}"
        batch_entries: list[dict[str, Any]] = []
        for task_id in ready_now:
            details = task_details[task_id]
            planned_problem_deps = [
                dep
                for dep in details["blocking_problem_deps"]
                if dep in completed_or_planned
            ]
            batch_entries.append(
                {
                    "task_id": task_id,
                    "hard_dependencies": details["hard_dependencies"],
                    "soft_imports": details["soft_imports"],
                    "final_import_union": details["final_import_union"],
                    "blocked_by": planned_problem_deps,
                    "missing_completed_deps": details["missing_completed_deps"],
                    "ready_reason": _ready_reason(
                        task_id,
                        planned_problem_deps,
                        details["hard_dependencies"],
                        details["soft_imports"],
                    ),
                }
            )
        batches.append({"batch_id": batch_id, "tasks": batch_entries})
        completed_or_planned.update(ready_now)
        remaining = [task_id for task_id in remaining if task_id not in ready_now]

    payload = {
        "scope_id": scope_id,
        "chapter": chapter,
        "problem_ids": task_ids,
        "generated_at": _utc_stamp(),
        "selection_scope_id": scope_id,
        "batches": batches,
        "unscheduled": [unscheduled[task_id] for task_id in sorted(unscheduled.keys())],
    }
    (plan_dir / "batch_plan.json").write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
    (plan_dir / "batch_plan.md").write_text(
        _render_plan_markdown(scope_id, chapter, task_ids, payload),
        encoding="utf-8",
    )
    return plan_dir


def resolve_batch_plan(scope_or_batch_id: str, settings) -> tuple[Path, dict[str, Any], dict[str, Any] | None]:
    output_root = settings.phase3_execution_batches_dir
    if output_root is None:
        raise ValueError("phase3_execution_batches_dir is not configured.")
    requested = str(scope_or_batch_id).strip()
    if not requested:
        raise ValueError("A non-empty batch identifier is required.")

    direct_dir = output_root / requested
    if direct_dir.exists():
        plan_path = direct_dir / "batch_plan.json"
        if not plan_path.exists():
            raise FileNotFoundError(f"Batch plan file not found: {plan_path}")
        payload = json.loads(plan_path.read_text(encoding="utf-8"))
        return direct_dir, payload, None

    for plan_path in output_root.glob("*/batch_plan.json"):
        payload = json.loads(plan_path.read_text(encoding="utf-8"))
        for batch in payload.get("batches", []):
            if batch.get("batch_id") == requested:
                return plan_path.parent, payload, batch
    raise FileNotFoundError(f"No execution batch or scope matched: {requested}")


def task_ids_for_batch(scope_or_batch_id: str, settings) -> tuple[Path, list[str], str]:
    plan_dir, payload, batch = resolve_batch_plan(scope_or_batch_id, settings)
    if batch is None:
        all_batch_ids = [item.get("batch_id", "") for item in payload.get("batches", [])]
        raise ValueError(
            f"{scope_or_batch_id} is an execution scope, not a concrete batch id. "
            f"Available batch ids: {', '.join(all_batch_ids) if all_batch_ids else '(none)'}"
        )
    task_ids = [canonicalize_block_id(item.get("task_id")) for item in batch.get("tasks", [])]
    return plan_dir, canonicalize_id_list(task_ids), str(batch.get("batch_id", ""))
