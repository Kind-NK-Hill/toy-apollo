from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.toy_apollo.phase1_plan_audit import audit_phase1_plans


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Read-only structural audit for existing Phase 1 plan files.",
    )
    parser.add_argument(
        "--plans-dir",
        type=Path,
        default=REPO_ROOT / "plans",
        help="Directory containing *_plan.json files.",
    )
    parser.add_argument(
        "--inputs-dir",
        type=Path,
        default=REPO_ROOT / "inputs",
        help="Directory containing source .tex files.",
    )
    parser.add_argument(
        "--ledger",
        type=Path,
        default=REPO_ROOT / "project_ledger.json",
        help="Path to project_ledger.json.",
    )
    parser.add_argument(
        "--stems",
        nargs="*",
        default=None,
        help="Optional source plan stems to audit. Defaults to all discovered plan stems.",
    )
    return parser.parse_args()


def build_summary(reports: list[dict]) -> dict[str, object]:
    status_counts = Counter(str(report.get("status", "unknown")) for report in reports)
    return {
        "total": len(reports),
        "status_counts": dict(status_counts),
        "error_plans": [
            report.get("source_plan", "")
            for report in reports
            if report.get("status") == "error"
        ],
        "warning_plans": [
            report.get("source_plan", "")
            for report in reports
            if report.get("status") == "warning"
        ],
    }


def main() -> int:
    args = parse_args()
    reports = audit_phase1_plans(
        plans_dir=args.plans_dir,
        inputs_dir=args.inputs_dir,
        ledger_path=args.ledger,
        stems=args.stems,
    )
    payload = {
        "reports": reports,
        "summary": build_summary(reports),
    }
    json.dump(payload, sys.stdout, indent=2, ensure_ascii=False)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
