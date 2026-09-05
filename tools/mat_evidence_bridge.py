from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formalization_engine.state_evidence_bridge import (  # noqa: E402
    EvidenceBridgeError,
    emit_final122_bridge_batch_receipt,
    inspect_evidence_bridge,
    inspect_final122_minimal_index,
    inspect_kenneth_authority_manifest,
    validate_evidence_bridge_receipt,
    validate_final122_bridge_batch_receipt,
)


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Inspect A/B strict evidence-bridge input or replay a future receipt. "
            "Emission is immutable/no-replace; no command builds, reviews, runs Lean, or writes SQLite."
        )
    )
    subparsers = parser.add_subparsers(dest="command", required=True)
    inspect = subparsers.add_parser("inspect")
    inspect.add_argument("--input", type=Path, required=True)
    validate = subparsers.add_parser("validate")
    validate.add_argument("--receipt", type=Path, required=True)
    authority_batch = subparsers.add_parser(
        "inspect-authority-batch",
        help="Inspect the consolidated Kenneth author-exact authority manifest",
    )
    authority_batch.add_argument("--manifest", type=Path, required=True)
    authority_batch.add_argument("--target-repo", type=Path, required=True)
    authority_batch.add_argument("--kenneth-repo", type=Path, required=True)
    final_inspect = subparsers.add_parser("inspect-final122", help="Replay the final A/B/U minimal pointer index")
    final_emit = subparsers.add_parser("emit-final122-batch", help="Atomically emit one immutable authority-item batch receipt")
    final_validate = subparsers.add_parser("validate-final122-batch", help="Replay an emitted final122 batch receipt")
    for item in (final_inspect, final_emit):
        item.add_argument("--index", type=Path, required=True)
    final_emit.add_argument("--output", type=Path, required=True)
    final_emit.add_argument("--created-at", required=True)
    final_validate.add_argument("--receipt", type=Path, required=True)
    for item in (final_inspect, final_emit, final_validate):
        item.add_argument("--target-repo", type=Path, required=True)
        item.add_argument("--kenneth-repo", type=Path, required=True)
    for item in (inspect, validate):
        item.add_argument("--source-repo", type=Path, action="append", required=True)
        item.add_argument("--target-repo", type=Path, required=True)
        item.add_argument("--kenneth-repo", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "inspect-final122":
        result = inspect_final122_minimal_index(
            args.index, target_repo=args.target_repo, kenneth_repo=args.kenneth_repo,
        )
    elif args.command == "emit-final122-batch":
        result = emit_final122_bridge_batch_receipt(
            args.index, args.output, target_repo=args.target_repo,
            kenneth_repo=args.kenneth_repo, created_at=args.created_at,
        )
    elif args.command == "validate-final122-batch":
        payload = validate_final122_bridge_batch_receipt(
            args.receipt, target_repo=args.target_repo, kenneth_repo=args.kenneth_repo,
        )
        result = {"status": "valid", "count": payload["count"], "target_commit": payload["target_commit"]}
    elif args.command == "inspect-authority-batch":
        result = inspect_kenneth_authority_manifest(
            args.manifest,
            target_repo=args.target_repo,
            kenneth_repo=args.kenneth_repo,
        )
    elif args.command == "inspect":
        result = inspect_evidence_bridge(
            args.input,
            source_repos=args.source_repo,
            target_repo=args.target_repo,
            kenneth_repo=args.kenneth_repo,
        )
    else:
        receipt, source, target = validate_evidence_bridge_receipt(
            args.receipt,
            source_repos=args.source_repo,
            target_repo=args.target_repo,
            kenneth_repo=args.kenneth_repo,
        )
        result = {
            "status": "valid",
            "task_id": receipt["task_id"],
            "bridge_route": receipt["bridge_route"],
            "authority_scope": receipt["authority_scope"],
            "source_subject_id": source.subject_id,
            "target_subject_id": target.subject_id,
        }
    print(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except EvidenceBridgeError as exc:
        print(f"MAT_EVIDENCE_BRIDGE_ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
