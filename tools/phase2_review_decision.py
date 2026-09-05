#!/usr/bin/env python3
"""Read-only Phase2 reviewer-result normalization and task-status projection.

This is the tracked decision boundary for campaign collectors. It never edits
the review input, raw reviewer result, prompt pack, proof obligations, or
ledger. Only ``--output`` may create a separate decision artifact.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


from formalization_engine.phase2_review_decision import evaluate_semantic_review_result  # noqa: E402


def _read_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:
        return {"_json_error": str(exc)}


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Normalize one Phase2 semantic-review result and emit its authoritative task-status projection."
    )
    parser.add_argument("--review-input", required=True, type=Path, help="semantic_review_input_vN.json")
    parser.add_argument("--review-result", required=True, type=Path, help="raw reviewer result JSON")
    parser.add_argument("--output", type=Path, help="optional separate decision JSON; inputs are never overwritten")
    return parser


def _paths_alias(left: Path, right: Path) -> bool:
    try:
        return left.samefile(right)
    except (FileNotFoundError, OSError):
        return left.resolve() == right.resolve()


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    if args.output is not None and (
        _paths_alias(args.output, args.review_input)
        or _paths_alias(args.output, args.review_result)
    ):
        sys.stderr.write("ERROR: --output must be a separate decision artifact, not the review input/result file.\n")
        return 2
    review_input = _read_json(args.review_input)
    raw_result = _read_json(args.review_result)
    if not isinstance(review_input, dict) or "_json_error" in review_input:
        payload = {
            "schema_version": "phase2.review_decision.v1",
            "review_input_file": str(args.review_input.resolve()),
            "review_result_file": str(args.review_result.resolve()),
            "is_semantic_verdict": False,
            "is_clean_pass": False,
            "phase2_status": None,
            "result": {
                "verdict": "inconclusive",
                "cache_class": "operational_failure",
                "normalization_reason": "review input is not a valid JSON object",
                "raw_result": review_input,
            },
        }
        exit_code = 2
    else:
        decision = evaluate_semantic_review_result(
            raw_result,
            review_input=review_input,
            runner_metadata={
                "status": "tracked_read_only_collector",
                "result_file": str(args.review_result.resolve()),
            },
        )
        projection = decision.task_status_projection
        payload = {
            "schema_version": "phase2.review_decision.v1",
            "review_input_file": str(args.review_input.resolve()),
            "review_result_file": str(args.review_result.resolve()),
            "is_semantic_verdict": decision.is_semantic_verdict,
            "is_clean_pass": decision.is_clean_pass,
            "phase2_status": projection.task_status if projection is not None else None,
            "result": decision.result,
        }
        exit_code = 0 if decision.is_semantic_verdict else 2

    rendered = json.dumps(payload, indent=2, ensure_ascii=False) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    sys.stdout.write(rendered)
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
