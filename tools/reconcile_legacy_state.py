from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.toy_apollo.state_store import refuse_legacy_ledger_write

try:
    from src.ledger_manager import TaskStatus

    VALID_STATUSES = {s.value for s in TaskStatus}
except Exception:
    VALID_STATUSES = {
        "DISCOVERED",
        "LOCAL_FIXING",
        "FAILED_LOCAL",
        "OFFLOADED",
        "HARVESTED",
        "ALIGNING",
        "COMPLETED",
        "COMPLETED_WITH_PROOF_DEBT",
        "USER_MODIFIED",
        "ORPHANED",
    }


LEGACY_ROOT_DEFAULT = REPO_ROOT.parent / "toy-apollo-archive-20260508"
CURRENT_LEDGER_DEFAULT = Path("project_ledger.json")
REPORT_DIR_DEFAULT = Path("reports/legacy_reconcile")

HIGH_STATUS_REQUIRES_EVIDENCE = {
    "HARVESTED",
    "ALIGNING",
    "COMPLETED",
    "COMPLETED_WITH_PROOF_DEBT",
    "USER_MODIFIED",
}


@dataclass
class ReconcileContext:
    legacy_root: Path
    current_ledger: Path
    report_dir: Path


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def timestamp_compact() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")


def load_json(path: Path) -> Any:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(payload, f, indent=4, ensure_ascii=False)


def safe_str(value: Any) -> str:
    return value if isinstance(value, str) else ""


def normalize_status(value: Any) -> str:
    raw = safe_str(value).strip().upper()
    if raw in VALID_STATUSES:
        return raw
    return ""


def normalize_dependencies(value: Any) -> list[str]:
    if not isinstance(value, list):
        return []
    deps: list[str] = []
    for item in value:
        if isinstance(item, str) and item:
            deps.append(item)
    return deps


def normalize_depth(value: Any) -> int:
    if isinstance(value, int):
        return value
    if isinstance(value, str) and value.isdigit():
        return int(value)
    return 0


def hash_text(content: str) -> str:
    if not content:
        return ""
    return hashlib.md5(content.encode("utf-8")).hexdigest()


def read_legacy_sources(legacy_root: Path) -> tuple[dict[str, dict], dict[str, dict], dict[str, dict], dict[str, str]]:
    ledger_file = legacy_root / "project_ledger.json"
    if not ledger_file.exists():
        raise FileNotFoundError(f"Legacy ledger missing: {ledger_file}")
    legacy_ledger = load_json(ledger_file)
    ledger_tasks_raw = legacy_ledger.get("tasks", {})
    ledger_tasks: dict[str, dict] = {}
    if isinstance(ledger_tasks_raw, dict):
        for tid, task in ledger_tasks_raw.items():
            if isinstance(tid, str) and tid and isinstance(task, dict):
                ledger_tasks[tid] = task

    symbols_raw = legacy_ledger.get("symbols", {})
    symbols: dict[str, str] = {}
    if isinstance(symbols_raw, dict):
        for sym, task_id in symbols_raw.items():
            if isinstance(sym, str) and sym and isinstance(task_id, str) and task_id:
                symbols[sym] = task_id

    plans_dir = legacy_root / "plans"
    plan_index: dict[str, dict] = {}
    if plans_dir.exists():
        for plan_file in plans_dir.glob("*_plan.json"):
            try:
                data = load_json(plan_file)
            except Exception:
                continue
            if isinstance(data, list):
                for task in data:
                    if not isinstance(task, dict):
                        continue
                    task_id = safe_str(task.get("block_id")).strip()
                    if task_id and task_id not in plan_index:
                        plan_index[task_id] = task
            elif isinstance(data, dict):
                task_id = safe_str(data.get("block_id")).strip()
                if task_id and task_id not in plan_index:
                    plan_index[task_id] = data

    unsolved_file = plans_dir / "unsolved_tasks.json"
    unsolved_index: dict[str, dict] = {}
    if unsolved_file.exists():
        try:
            unsolved_data = load_json(unsolved_file)
        except Exception:
            unsolved_data = []
        if isinstance(unsolved_data, list):
            for task in unsolved_data:
                if not isinstance(task, dict):
                    continue
                task_id = safe_str(task.get("block_id")).strip()
                if task_id and task_id not in unsolved_index:
                    unsolved_index[task_id] = task
        elif isinstance(unsolved_data, dict):
            task_id = safe_str(unsolved_data.get("block_id")).strip()
            if task_id:
                unsolved_index[task_id] = unsolved_data

    return ledger_tasks, plan_index, unsolved_index, symbols


def first_non_empty_string(values: list[Any]) -> str:
    for value in values:
        if isinstance(value, str) and value.strip():
            return value
    return ""


def first_dependencies(values: list[Any]) -> list[str]:
    for value in values:
        deps = normalize_dependencies(value)
        if deps:
            return deps
    return []


def first_depth(values: list[Any]) -> int:
    for value in values:
        depth = normalize_depth(value)
        if depth != 0:
            return depth
    return 0


def evidence_candidates(task_id: str, source_plan: str, legacy_root: Path) -> list[Path]:
    candidates = [
        legacy_root / "ToyApollo" / "Output" / f"{task_id}.lean",
        legacy_root / "output_lean_files" / "general" / f"{task_id}.lean",
        legacy_root / "output_lean_files" / f"{task_id}.lean",
    ]
    if source_plan:
        candidates.append(legacy_root / "output_lean_files" / source_plan / f"{task_id}.lean")
    return candidates


def find_evidence_file(task_id: str, source_plan: str, legacy_root: Path) -> Path | None:
    for candidate in evidence_candidates(task_id, source_plan, legacy_root):
        if candidate.exists():
            return candidate
    return None


def compute_file_md5(path: Path) -> str:
    digest = hashlib.md5()
    with open(path, "rb") as f:
        while True:
            chunk = f.read(1024 * 1024)
            if not chunk:
                break
            digest.update(chunk)
    return digest.hexdigest()


def parse_int(value: Any, default: int = 0) -> int:
    if isinstance(value, int):
        return value
    if isinstance(value, str) and value.isdigit():
        return int(value)
    return default


def build_task_record(
    task_id: str,
    legacy_task: dict | None,
    plan_task: dict | None,
    unsolved_task: dict | None,
    legacy_root: Path,
) -> tuple[dict[str, Any], dict[str, Any] | None]:
    legacy_task = legacy_task or {}
    plan_task = plan_task or {}
    unsolved_task = unsolved_task or {}

    legacy_snapshot = legacy_task.get("candidate_snapshot")
    if not isinstance(legacy_snapshot, dict):
        legacy_snapshot = {}

    source_statuses: dict[str, str] = {}
    reasons: list[str] = []

    legacy_status_raw = safe_str(legacy_task.get("status")).strip()
    legacy_status = normalize_status(legacy_status_raw)
    if legacy_status:
        source_statuses["legacy_ledger"] = legacy_status
    elif legacy_status_raw:
        source_statuses["legacy_ledger"] = f"INVALID:{legacy_status_raw}"
        reasons.append(f"invalid_legacy_status:{legacy_status_raw}")

    plan_status_raw = safe_str(plan_task.get("status")).strip()
    plan_status = normalize_status(plan_status_raw)
    if plan_status:
        source_statuses["plans"] = plan_status
    elif plan_status_raw:
        source_statuses["plans"] = f"INVALID:{plan_status_raw}"

    if unsolved_task:
        source_statuses["unsolved_tasks"] = "FAILED_LOCAL"

    if legacy_status:
        selected_status = legacy_status
    elif unsolved_task:
        selected_status = "FAILED_LOCAL"
    else:
        selected_status = "DISCOVERED"

    observed_valid_statuses = {v for v in source_statuses.values() if v in VALID_STATUSES}
    if len(observed_valid_statuses) > 1:
        reasons.append(f"status_conflict:{source_statuses}")

    source_plan = first_non_empty_string(
        [
            plan_task.get("source_plan"),
            unsolved_task.get("source_plan"),
            legacy_snapshot.get("source_plan"),
            legacy_task.get("source_plan"),
        ]
    )
    task_type = first_non_empty_string(
        [
            plan_task.get("type"),
            unsolved_task.get("type"),
            legacy_snapshot.get("type"),
            legacy_task.get("type"),
        ]
    )
    title = first_non_empty_string(
        [
            plan_task.get("title"),
            unsolved_task.get("title"),
            legacy_snapshot.get("title"),
            legacy_task.get("title"),
        ]
    )
    content = first_non_empty_string(
        [
            plan_task.get("content"),
            unsolved_task.get("content"),
            legacy_snapshot.get("content"),
            legacy_task.get("content"),
        ]
    )
    dependencies = first_dependencies(
        [
            plan_task.get("dependencies"),
            unsolved_task.get("dependencies"),
            legacy_snapshot.get("dependencies"),
            legacy_task.get("dependencies"),
        ]
    )
    depth = first_depth(
        [
            plan_task.get("depth"),
            unsolved_task.get("depth"),
            legacy_snapshot.get("depth"),
            legacy_task.get("depth"),
        ]
    )

    if not task_type:
        reasons.append("missing_type_context")
        task_type = "Problem"
    if not source_plan:
        reasons.append("missing_source_plan_context")
        source_plan = "unknown"
    if not content.strip():
        reasons.append("missing_candidate_content")

    output_hash = legacy_task.get("output_hash")
    if not isinstance(output_hash, str) or not output_hash.strip():
        output_hash = None

    if selected_status in HIGH_STATUS_REQUIRES_EVIDENCE:
        evidence_file = find_evidence_file(task_id, source_plan, legacy_root)
        if evidence_file is None:
            reasons.append(f"missing_output_evidence_for_high_status:{selected_status}")
        elif output_hash:
            try:
                file_hash = compute_file_md5(evidence_file)
            except Exception:
                file_hash = ""
            if file_hash and file_hash != output_hash:
                reasons.append(
                    f"output_hash_mismatch:{output_hash[:12]}!={file_hash[:12]}"
                )

    final_status = selected_status
    if reasons:
        final_status = "FAILED_LOCAL"

    exported_symbols = legacy_task.get("exported_symbols")
    if not isinstance(exported_symbols, list):
        exported_symbols = []
    exported_symbols = [s for s in exported_symbols if isinstance(s, str) and s]

    record: dict[str, Any] = {
        "block_id": task_id,
        "type": task_type,
        "title": title or task_id,
        "input_hash": hash_text(content),
        "status": final_status,
        "source_plan": source_plan,
        "output_hash": output_hash,
        "exported_symbols": exported_symbols,
        "last_error": safe_str(legacy_task.get("last_error")),
        "phase3_attempts": parse_int(legacy_task.get("phase3_attempts"), 0),
        "phase4_attempts": parse_int(legacy_task.get("phase4_attempts"), 0),
        "last_offload_error": safe_str(legacy_task.get("last_offload_error")),
        "last_align_error": safe_str(legacy_task.get("last_align_error")),
        "cloud_project_id": safe_str(legacy_task.get("cloud_project_id")),
        "last_offload_at": safe_str(legacy_task.get("last_offload_at")),
        "last_harvest_at": safe_str(legacy_task.get("last_harvest_at")),
        "candidate_snapshot": {
            "block_id": task_id,
            "type": task_type,
            "title": title or task_id,
            "content": content,
            "source_plan": source_plan,
            "dependencies": dependencies,
            "depth": depth,
        },
    }

    conflict_entry: dict[str, Any] | None = None
    if reasons:
        reconcile_reason = "; ".join(reasons)
        record["reconcile_reason"] = reconcile_reason
        if not record["last_offload_error"]:
            record["last_offload_error"] = reconcile_reason
        conflict_entry = {
            "task_id": task_id,
            "selected_status_before_downgrade": selected_status,
            "final_status": final_status,
            "reasons": reasons,
            "source_statuses": source_statuses,
            "source_plan": source_plan,
            "content_present": bool(content.strip()),
        }

    return record, conflict_entry


def build_preview_ledger(
    legacy_tasks: dict[str, dict],
    plan_index: dict[str, dict],
    unsolved_index: dict[str, dict],
    symbols: dict[str, str],
    legacy_root: Path,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    all_task_ids = set(legacy_tasks.keys()) | set(plan_index.keys()) | set(unsolved_index.keys())
    merged_tasks: dict[str, dict] = {}
    conflicts: list[dict[str, Any]] = []

    for task_id in sorted(all_task_ids):
        record, conflict_entry = build_task_record(
            task_id=task_id,
            legacy_task=legacy_tasks.get(task_id),
            plan_task=plan_index.get(task_id),
            unsolved_task=unsolved_index.get(task_id),
            legacy_root=legacy_root,
        )
        merged_tasks[task_id] = record
        if conflict_entry is not None:
            conflicts.append(conflict_entry)

    merged_symbols: dict[str, str] = {}
    for sym, task_id in symbols.items():
        if task_id in merged_tasks:
            merged_symbols[sym] = task_id

    preview = {"tasks": merged_tasks, "symbols": merged_symbols}
    return preview, conflicts


def summarize_statuses(tasks: dict[str, dict]) -> dict[str, int]:
    summary: dict[str, int] = {}
    for task in tasks.values():
        status = safe_str(task.get("status")) or "UNKNOWN"
        summary[status] = summary.get(status, 0) + 1
    return dict(sorted(summary.items(), key=lambda x: x[0]))


def write_report(
    report_file: Path,
    ctx: ReconcileContext,
    preview_ledger: dict[str, Any],
    conflicts: list[dict[str, Any]],
    apply_used: bool,
    backup_file: Path | None,
) -> None:
    tasks = preview_ledger.get("tasks", {})
    status_summary = summarize_statuses(tasks if isinstance(tasks, dict) else {})
    lines: list[str] = []
    lines.append("# Legacy State Reconcile Report")
    lines.append("")
    lines.append(f"- generated_at_utc: `{now_iso()}`")
    lines.append(f"- legacy_root: `{ctx.legacy_root}`")
    lines.append(f"- current_ledger: `{ctx.current_ledger}`")
    lines.append(f"- mode: `{'apply' if apply_used else 'dry-run'}`")
    if backup_file:
        lines.append(f"- backup_file: `{backup_file}`")
    lines.append("")
    lines.append("## Summary")
    lines.append("")
    lines.append(f"- total_tasks: `{len(tasks)}`")
    lines.append(f"- conflict_tasks: `{len(conflicts)}`")
    lines.append("")
    lines.append("## Status Counts")
    lines.append("")
    for status, count in status_summary.items():
        lines.append(f"- `{status}`: {count}")
    lines.append("")
    lines.append("## Conflict Samples")
    lines.append("")
    if not conflicts:
        lines.append("- No conflicts detected.")
    else:
        for item in conflicts[:30]:
            task_id = item.get("task_id", "")
            reasons = item.get("reasons", [])
            reason_text = ", ".join([r for r in reasons if isinstance(r, str)])
            lines.append(f"- `{task_id}`: {reason_text}")
        if len(conflicts) > 30:
            lines.append(f"- ... and {len(conflicts) - 30} more (see `reconcile_conflicts.json`).")
    lines.append("")
    report_file.parent.mkdir(parents=True, exist_ok=True)
    report_file.write_text("\n".join(lines) + "\n", encoding="utf-8")


def backup_current_ledger(current_ledger: Path) -> Path:
    backup_path = current_ledger.parent / f"project_ledger.backup.{timestamp_compact()}.json"
    if current_ledger.exists():
        backup_path.write_text(current_ledger.read_text(encoding="utf-8"), encoding="utf-8")
    else:
        write_json(backup_path, {"tasks": {}, "symbols": {}})
    return backup_path


def restore_ledger(current_ledger: Path, backup_file: Path) -> None:
    if not backup_file.exists():
        raise FileNotFoundError(f"Backup file not found: {backup_file}")
    data = load_json(backup_file)
    if not isinstance(data, dict) or "tasks" not in data:
        raise ValueError(f"Invalid backup content: {backup_file}")
    write_json(current_ledger, data)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Reconcile legacy unsolved/task state into current ledger (status-first, conservative)."
    )
    parser.add_argument(
        "--legacy-root",
        default=str(LEGACY_ROOT_DEFAULT),
        help="Legacy repository root (read-only).",
    )
    parser.add_argument(
        "--current-ledger",
        default=str(CURRENT_LEDGER_DEFAULT),
        help="Current workspace ledger path to write when --apply is used.",
    )
    parser.add_argument(
        "--report-dir",
        default=str(REPORT_DIR_DEFAULT),
        help="Output directory for reconcile reports.",
    )
    parser.add_argument(
        "--apply",
        action="store_true",
        help="Apply preview ledger to current ledger with automatic backup.",
    )
    parser.add_argument(
        "--restore",
        default="",
        help="Restore current ledger from a backup file and exit.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    legacy_root = Path(args.legacy_root).resolve()
    current_ledger = Path(args.current_ledger).resolve()
    report_dir = Path(args.report_dir).resolve()
    ctx = ReconcileContext(legacy_root=legacy_root, current_ledger=current_ledger, report_dir=report_dir)

    if args.apply or args.restore:
        refuse_legacy_ledger_write(current_ledger.parent, operation="legacy ledger reconcile/restore")

    if args.restore:
        restore_file = Path(args.restore).resolve()
        restore_ledger(current_ledger=current_ledger, backup_file=restore_file)
        print(f"♻️ Restored ledger from backup: {restore_file}")
        print(f"🧾 Current ledger: {current_ledger}")
        return 0

    legacy_tasks, plan_index, unsolved_index, symbols = read_legacy_sources(legacy_root)
    preview_ledger, conflicts = build_preview_ledger(
        legacy_tasks=legacy_tasks,
        plan_index=plan_index,
        unsolved_index=unsolved_index,
        symbols=symbols,
        legacy_root=legacy_root,
    )

    preview_file = report_dir / "reconcile_preview_ledger.json"
    conflict_file = report_dir / "reconcile_conflicts.json"
    report_file = report_dir / "reconcile_report.md"

    write_json(preview_file, preview_ledger)
    write_json(
        conflict_file,
        {
            "generated_at_utc": now_iso(),
            "legacy_root": str(legacy_root),
            "current_ledger": str(current_ledger),
            "total_tasks": len(preview_ledger.get("tasks", {})),
            "conflict_count": len(conflicts),
            "conflicts": conflicts,
        },
    )

    backup_file: Path | None = None
    if args.apply:
        backup_file = backup_current_ledger(current_ledger)
        write_json(current_ledger, preview_ledger)

    write_report(
        report_file=report_file,
        ctx=ctx,
        preview_ledger=preview_ledger,
        conflicts=conflicts,
        apply_used=bool(args.apply),
        backup_file=backup_file,
    )

    mode = "APPLY" if args.apply else "DRY-RUN"
    print(f"✅ Reconcile complete ({mode})")
    print(f"   legacy_root: {legacy_root}")
    print(f"   preview:     {preview_file}")
    print(f"   conflicts:   {conflict_file}")
    print(f"   report:      {report_file}")
    if backup_file:
        print(f"   backup:      {backup_file}")
        print(f"   ledger:      {current_ledger}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
