import json
from pathlib import Path
from typing import Iterable

from src.aristotle_offloader import OffloadCandidate
from src.block_id_naming import (
    canonicalize_block_id,
    canonicalize_id_list,
    canonicalize_task_dict,
)

from ..core import TaskStatus


def _iter_plan_tasks(plans_dir: Path) -> Iterable[dict]:
    if not plans_dir.exists():
        return []
    tasks: list[dict] = []
    for plan_file in plans_dir.glob("*_plan.json"):
        try:
            with open(plan_file, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, list):
                tasks.extend([t for t in data if isinstance(t, dict)])
            elif isinstance(data, dict):
                tasks.append(data)
        except Exception:
            continue
    return tasks


def _iter_legacy_tasks(legacy_file: Path) -> Iterable[dict]:
    if not legacy_file.exists():
        return []
    try:
        with open(legacy_file, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, list):
            return [t for t in data if isinstance(t, dict)]
        if isinstance(data, dict):
            return [data]
    except Exception:
        return []
    return []


def build_plan_task_index(plans_dir: Path) -> dict[str, dict]:
    index: dict[str, dict] = {}
    for task in _iter_plan_tasks(plans_dir):
        task = canonicalize_task_dict(task)
        tid = task.get("block_id")
        if isinstance(tid, str) and tid and tid not in index:
            index[tid] = task
    return index


def build_legacy_task_index(legacy_file: Path) -> dict[str, dict]:
    index: dict[str, dict] = {}
    for task in _iter_legacy_tasks(legacy_file):
        task = canonicalize_task_dict(task)
        tid = task.get("block_id")
        if isinstance(tid, str) and tid and tid not in index:
            index[tid] = task
    return index


def _normalize_dependencies(raw: object) -> list[str]:
    return canonicalize_id_list(raw)


def _normalize_soft_imports(raw: object) -> list[str]:
    return canonicalize_id_list(raw)


def _normalize_depth(raw: object) -> int:
    if isinstance(raw, int):
        return raw
    if isinstance(raw, str) and raw.isdigit():
        return int(raw)
    return 0


def _candidate_payload_from_task(task_record: dict, fallback_source_plan: str) -> dict | None:
    snapshot = task_record.get("candidate_snapshot")
    if not isinstance(snapshot, dict):
        return None

    block_id = snapshot.get("block_id") or task_record.get("block_id")
    block_id = canonicalize_block_id(block_id)
    if not isinstance(block_id, str) or not block_id:
        return None

    content = snapshot.get("content", "")
    if not isinstance(content, str) or not content.strip():
        return None

    return {
        "block_id": block_id,
        "type": snapshot.get("type", task_record.get("type", "Problem")),
        "title": snapshot.get("title", task_record.get("title", block_id)),
        "content": content,
        "source_plan": snapshot.get("source_plan", fallback_source_plan),
        "dependencies": _normalize_dependencies(snapshot.get("dependencies", [])),
        "soft_imports": _normalize_soft_imports(snapshot.get("soft_imports", [])),
        "soft_imports_confirmed_at": str(task_record.get("soft_imports_confirmed_at", "") or ""),
        "depth": _normalize_depth(snapshot.get("depth", 0)),
    }


def _is_valid_candidate_payload(payload: dict | None) -> bool:
    if not isinstance(payload, dict):
        return False
    block_id = payload.get("block_id")
    content = payload.get("content")
    return isinstance(block_id, str) and bool(block_id) and isinstance(content, str) and bool(content.strip())


def _resolve_candidates_for_task_records(ledger, plans_dir: Path, task_records: list[dict]) -> tuple[list[OffloadCandidate], list[str]]:
    plan_index = build_plan_task_index(plans_dir)
    legacy_index = build_legacy_task_index(plans_dir / "offload_candidates_legacy.json")
    missing_ids: list[str] = []
    candidates: list[OffloadCandidate] = []

    for task_record in task_records:
        task_id = task_record.get("block_id")
        task_id = canonicalize_block_id(task_id)
        if not task_id:
            continue

        fallback_source_plan = task_record.get("source_plan", "unknown")
        candidate_payload: dict | None = None

        # fixed recovery order: plans/*_plan.json -> legacy export -> ledger snapshot
        plan_task = plan_index.get(task_id)
        if isinstance(plan_task, dict):
            plan_task = canonicalize_task_dict(plan_task)
            snapshot = task_record.get("candidate_snapshot", {})
            snapshot_soft_imports = []
            if isinstance(snapshot, dict):
                snapshot_soft_imports = _normalize_soft_imports(snapshot.get("soft_imports", []))
            plan_payload = {
                "block_id": task_id,
                "type": plan_task.get("type", "Problem"),
                "title": plan_task.get("title", task_id),
                "content": plan_task.get("content", ""),
                "source_plan": plan_task.get("source_plan", fallback_source_plan),
                "dependencies": _normalize_dependencies(plan_task.get("dependencies", [])),
                "soft_imports": snapshot_soft_imports or _normalize_soft_imports(plan_task.get("soft_imports", [])),
                "soft_imports_confirmed_at": str(task_record.get("soft_imports_confirmed_at", "") or ""),
                "depth": _normalize_depth(plan_task.get("depth", 0)),
            }
            candidate_payload = plan_payload if _is_valid_candidate_payload(plan_payload) else None

        if candidate_payload is None:
            legacy_task = legacy_index.get(task_id)
            if isinstance(legacy_task, dict):
                legacy_task = canonicalize_task_dict(legacy_task)
                legacy_payload = {
                    "block_id": task_id,
                    "type": legacy_task.get("type", task_record.get("type", "Problem")),
                    "title": legacy_task.get("title", task_record.get("title", task_id)),
                    "content": legacy_task.get("content", ""),
                    "source_plan": legacy_task.get("source_plan", fallback_source_plan),
                    "dependencies": _normalize_dependencies(legacy_task.get("dependencies", [])),
                    "soft_imports": _normalize_soft_imports(legacy_task.get("soft_imports", [])),
                    "soft_imports_confirmed_at": str(task_record.get("soft_imports_confirmed_at", "") or ""),
                    "depth": _normalize_depth(legacy_task.get("depth", 0)),
                }
                candidate_payload = legacy_payload if _is_valid_candidate_payload(legacy_payload) else None

        if candidate_payload is None:
            snapshot_payload = _candidate_payload_from_task(task_record, fallback_source_plan)
            candidate_payload = snapshot_payload if _is_valid_candidate_payload(snapshot_payload) else None

        if candidate_payload is None:
            missing_ids.append(task_id)
            continue

        raw_status = task_record.get("status")
        status = raw_status if isinstance(raw_status, str) and raw_status else TaskStatus.FAILED_LOCAL.value
        candidates.append(
            OffloadCandidate(
                block_id=candidate_payload["block_id"],
                type=candidate_payload["type"],
                title=candidate_payload["title"],
                content=candidate_payload["content"],
                source_plan=candidate_payload["source_plan"],
                dependencies=candidate_payload["dependencies"],
                soft_imports=candidate_payload.get("soft_imports", []),
                soft_imports_confirmed_at=candidate_payload.get("soft_imports_confirmed_at", ""),
                depth=candidate_payload["depth"],
                status=status,
            )
        )

    return candidates, missing_ids


def resolve_offload_candidates_from_ledger(ledger, plans_dir: Path) -> tuple[list[OffloadCandidate], list[str]]:
    failed_tasks = [
        task
        for task in ledger.get_tasks_by_status([TaskStatus.FAILED_LOCAL])
        if str(task.get("pack_candidate_state", "") or "") != "review_rejected"
    ]
    if not failed_tasks:
        return [], []
    return _resolve_candidates_for_task_records(ledger, plans_dir, failed_tasks)


def resolve_offload_candidates_for_task_ids(ledger, plans_dir: Path, task_ids: list[str]) -> tuple[list[OffloadCandidate], list[str]]:
    wanted = set(canonicalize_id_list(task_ids))
    if not wanted:
        return [], []
    task_records = []
    for task_id in wanted:
        record = ledger.ledger.get("tasks", {}).get(task_id)
        if isinstance(record, dict):
            task_records.append(record)
    return _resolve_candidates_for_task_records(ledger, plans_dir, task_records)


def export_legacy_candidates(candidates: list[OffloadCandidate], output_file: Path) -> None:
    output_file.parent.mkdir(parents=True, exist_ok=True)
    with open(output_file, "w", encoding="utf-8") as f:
        json.dump(candidates, f, indent=4, ensure_ascii=False)
