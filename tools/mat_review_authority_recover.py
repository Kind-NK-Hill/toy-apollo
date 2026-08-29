from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.toy_apollo.state_review_apply_recovery import (  # noqa: E402
    HistoricalReviewApplyRecoveryError,
    build_historical_review_apply_recovery,
)


def _receipt(
    *,
    pack_dir: Path,
    result_path: Path,
    verify_path: Path,
) -> dict[str, object]:
    return build_historical_review_apply_recovery(
        pack_dir=pack_dir.resolve(),
        result_path=result_path.resolve(),
        verify_path=verify_path.resolve(),
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Inspect or emit immutable evidence that an old canonical Phase 2 "
            "review-apply succeeded. This never writes SQLite and never binds a current target."
        )
    )
    subparsers = parser.add_subparsers(dest="command", required=True)
    for command in ("inspect", "emit"):
        subparser = subparsers.add_parser(command)
        subparser.add_argument("--pack-dir", type=Path, required=True)
        subparser.add_argument("--review-result", type=Path, required=True)
        subparser.add_argument("--verify-result", type=Path, required=True)
        if command == "emit":
            subparser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    receipt = _receipt(
        pack_dir=args.pack_dir,
        result_path=args.review_result,
        verify_path=args.verify_result,
    )
    rendered = json.dumps(receipt, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    if args.command == "inspect":
        print(rendered, end="")
        return 0
    output = args.output.resolve()
    if output.parent != args.pack_dir.resolve():
        raise HistoricalReviewApplyRecoveryError(
            "recovery receipt must be emitted beside its task-local immutable evidence"
        )
    if output.exists():
        raise HistoricalReviewApplyRecoveryError(f"refusing to overwrite existing receipt: {output}")
    output.write_text(rendered, encoding="utf-8")
    print(str(output))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except HistoricalReviewApplyRecoveryError as exc:
        print(f"MAT_REVIEW_AUTHORITY_RECOVERY_ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
