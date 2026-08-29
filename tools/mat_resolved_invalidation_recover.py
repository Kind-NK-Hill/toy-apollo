"""Inspect or emit a fail-closed recovery receipt for an old invalidation."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.toy_apollo.state_invalidation_recovery import (  # noqa: E402
    ResolvedInvalidationRecoveryError,
    build_resolved_invalidation_recovery,
)


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Validate or emit a current-exact recovery for a stale invalidated "
            "MAT review receipt. It never writes SQLite or modifies old evidence."
        )
    )
    sub = parser.add_subparsers(dest="command", required=True)
    for command in ("inspect", "emit"):
        item = sub.add_parser(command)
        item.add_argument("--stale-receipt", type=Path, required=True)
        item.add_argument("--target-build", type=Path, required=True)
        item.add_argument("--invalidator-build", type=Path, action="append", required=True)
        item.add_argument("--consumer-manifest", type=Path, required=True)
        item.add_argument("--consumer-build", type=Path, action="append", default=[])
        if command == "emit":
            item.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    receipt = build_resolved_invalidation_recovery(
        stale_receipt_path=args.stale_receipt,
        target_build_path=args.target_build,
        invalidator_build_paths=args.invalidator_build,
        consumer_manifest_path=args.consumer_manifest,
        consumer_build_paths=args.consumer_build,
    )
    rendered = json.dumps(receipt, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    if args.command == "inspect":
        print(rendered, end="")
        return 0
    output = args.output.resolve()
    if output.exists():
        raise ResolvedInvalidationRecoveryError(f"refusing to overwrite recovery receipt: {output}")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered, encoding="utf-8")
    print(output)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ResolvedInvalidationRecoveryError as exc:
        print(f"MAT_RESOLVED_INVALIDATION_RECOVERY_ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
