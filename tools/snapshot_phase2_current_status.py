from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from datetime import UTC, datetime
from pathlib import Path
from typing import Any


REPORT_JSON = "docs/phase2_current_status_snapshot.json"
REPORT_MD = "docs/phase2_current_status_snapshot.md"
EXCEPTION_STATUSES = ("fail", "blocked", "allowed_exception")
MISSING_SAMPLE_LIMIT = 25


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def utc_stamp() -> str:
    return datetime.now(UTC).isoformat().replace("+00:00", "Z")


def read_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return None


def rel(path: Path, root: Path) -> str:
    try:
        return path.relative_to(root).as_posix()
    except ValueError:
        return path.as_posix()


def is_legacy_obligation_task(task_id: str, record: dict[str, Any]) -> bool:
    if task_id.startswith("obl_"):
        return True
    kind = str(record.get("type", "") or "").replace("_", "").lower()
    return kind == "proofobligation"


def symbol_owner(symbol_record: Any) -> str:
    if not isinstance(symbol_record, dict):
        return ""
    for key in ("owner", "owner_task_id", "task_id"):
        value = str(symbol_record.get(key, "") or "")
        if value:
            return value
    return ""


def sorted_counter(counter: Counter[str]) -> dict[str, int]:
    return {key: counter[key] for key in sorted(counter)}


def exception_entry(task_id: str, record: dict[str, Any]) -> dict[str, Any]:
    entry = {
        "task_id": task_id,
        "type": str(record.get("type", "") or ""),
        "status": str(record.get("status", "") or ""),
        "phase2_status": str(record.get("phase2_status", "") or ""),
    }
    reason = str(record.get("phase2_status_reason", "") or "")
    if reason:
        entry["phase2_status_reason"] = reason
    pack = str(record.get("current_diagnoser_prompt_file", "") or "")
    if pack:
        entry["current_diagnoser_prompt_file"] = pack
    return entry


def build_snapshot(root: Path | None = None, *, generated_at: str | None = None) -> dict[str, Any]:
    root = root or repo_root()
    ledger_path = root / "project_ledger.json"
    raw = ledger_path.read_bytes() if ledger_path.exists() else b""
    ledger = read_json(ledger_path) if raw else {}
    if not isinstance(ledger, dict):
        ledger = {}

    tasks_raw = ledger.get("tasks", {})
    symbols_raw = ledger.get("symbols", {})
    tasks = tasks_raw if isinstance(tasks_raw, dict) else {}
    symbols = symbols_raw if isinstance(symbols_raw, dict) else {}

    task_items: list[tuple[str, dict[str, Any]]] = []
    legacy_obligation_task_count = 0
    for task_id, record_raw in sorted(tasks.items()):
        record = record_raw if isinstance(record_raw, dict) else {}
        if is_legacy_obligation_task(task_id, record):
            legacy_obligation_task_count += 1
            continue
        task_items.append((task_id, record))

    status_counts: Counter[str] = Counter()
    phase2_status_counts: Counter[str] = Counter()
    task_type_counts: Counter[str] = Counter()
    exceptions: dict[str, list[dict[str, Any]]] = {status: [] for status in EXCEPTION_STATUSES}
    missing_phase2_status_sample: list[dict[str, Any]] = []

    for task_id, record in task_items:
        status = str(record.get("status", "") or "missing")
        phase2_status = str(record.get("phase2_status", "") or "missing")
        task_type = str(record.get("type", "") or "missing")
        status_counts[status] += 1
        phase2_status_counts[phase2_status] += 1
        task_type_counts[task_type] += 1
        if phase2_status in exceptions:
            exceptions[phase2_status].append(exception_entry(task_id, record))
        elif phase2_status == "missing" and len(missing_phase2_status_sample) < MISSING_SAMPLE_LIMIT:
            missing_phase2_status_sample.append(exception_entry(task_id, record))

    legacy_obligation_symbol_owner_count = sum(
        1 for record in symbols.values() if symbol_owner(record).startswith("obl_")
    )
    hash_value = hashlib.sha256(raw).hexdigest() if raw else ""

    return {
        "generated_at": generated_at or utc_stamp(),
        "purpose": (
            "Tracked summary of the local Phase2 runtime ledger. This snapshot is audit context only; "
            "review-apply plus phase2_status remains the completion authority."
        ),
        "ledger": {
            "path": rel(ledger_path, root),
            "exists": ledger_path.exists(),
            "sha256": hash_value,
            "size_bytes": len(raw),
        },
        "summary": {
            "task_count": len(task_items),
            "symbol_count": len(symbols),
            "legacy_obligation_task_count": legacy_obligation_task_count,
            "legacy_obligation_symbol_owner_count": legacy_obligation_symbol_owner_count,
            "status_counts": sorted_counter(status_counts),
            "phase2_status_counts": sorted_counter(phase2_status_counts),
            "task_type_counts": sorted_counter(task_type_counts),
        },
        "exceptions": exceptions,
        "missing_phase2_status_sample": missing_phase2_status_sample,
    }


def markdown_report(payload: dict[str, Any]) -> str:
    summary = payload["summary"]
    ledger = payload["ledger"]
    lines = [
        "# Phase2 Current Status Snapshot",
        "",
        f"- generated_at: `{payload['generated_at']}`",
        f"- ledger: `{ledger['path']}`",
        f"- ledger_sha256: `{ledger['sha256']}`",
        f"- ledger_size_bytes: `{ledger['size_bytes']}`",
        f"- tasks: `{summary['task_count']}`",
        f"- symbols: `{summary['symbol_count']}`",
        f"- legacy_obligation_tasks: `{summary['legacy_obligation_task_count']}`",
        f"- legacy_obligation_symbol_owners: `{summary['legacy_obligation_symbol_owner_count']}`",
        "",
        "This report is audit context only. It does not replace `review-apply` or declare completion.",
        "",
        "## Status Counts",
        "",
    ]
    for key, value in summary["status_counts"].items():
        lines.append(f"- `{key}`: {value}")
    lines.extend(["", "## Phase2 Status Counts", ""])
    for key, value in summary["phase2_status_counts"].items():
        lines.append(f"- `{key}`: {value}")
    lines.extend(["", "## Exceptions", ""])
    for status in EXCEPTION_STATUSES:
        items = payload["exceptions"][status]
        lines.append(f"### {status}")
        lines.append("")
        if not items:
            lines.append("- none")
        for item in items:
            reason = item.get("phase2_status_reason")
            suffix = f" reason `{reason}`" if reason else ""
            lines.append(
                f"- `{item['task_id']}` `{item['type']}` ledger `{item['status']}`{suffix}"
            )
        lines.append("")
    missing = payload.get("missing_phase2_status_sample", [])
    lines.extend(["## Missing Phase2 Status Sample", ""])
    if not missing:
        lines.append("- none")
    for item in missing:
        lines.append(f"- `{item['task_id']}` `{item['type']}` ledger `{item['status']}`")
    return "\n".join(lines).rstrip() + "\n"


def write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def write_snapshot(
    root: Path | None = None,
    *,
    generated_at: str | None = None,
    report_json: str = REPORT_JSON,
    report_md: str = REPORT_MD,
) -> dict[str, Any]:
    root = root or repo_root()
    payload = build_snapshot(root, generated_at=generated_at)
    write_json(root / report_json, payload)
    md_path = root / report_md
    md_path.parent.mkdir(parents=True, exist_ok=True)
    md_path.write_text(markdown_report(payload), encoding="utf-8")
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="Write JSON and markdown reports.")
    parser.add_argument("--report-json", default=REPORT_JSON)
    parser.add_argument("--report-md", default=REPORT_MD)
    args = parser.parse_args()

    root = repo_root()
    payload = (
        write_snapshot(root, report_json=args.report_json, report_md=args.report_md)
        if args.write
        else build_snapshot(root)
    )
    print(json.dumps(payload["summary"], indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
