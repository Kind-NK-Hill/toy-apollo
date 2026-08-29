#!/usr/bin/env python3
"""Emit bounded current-exact MAT build evidence without semantic review."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.toy_apollo.state_exact_build_batch import (  # noqa: E402
    ExactBuildBatchError,
    collect_exact_build_selection,
    emit_current_exact_builds_batch,
)


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Build catalog-pinned MAT tasks in bounded combined batches and emit "
            "immutable mat.catalog.exact-build.v1 receipts"
        )
    )
    parser.add_argument("--task", action="append", default=[])
    parser.add_argument("--task-file", type=Path, action="append", default=[])
    parser.add_argument("--action-manifest", type=Path, action="append", default=[])
    parser.add_argument("--checkout", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--batch-size", type=int, default=12)
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--workspace-root", type=Path, default=REPO_ROOT.parent)
    parser.add_argument("--runtime-root", type=Path, default=REPO_ROOT)
    parser.add_argument("--campaign-id", default="current_exact_build_batch")
    parser.add_argument("--no-skip-existing", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    selection = collect_exact_build_selection(
        tasks=args.task,
        task_files=args.task_file,
        action_manifests=args.action_manifest,
    )
    result = emit_current_exact_builds_batch(
        workspace_root=args.workspace_root,
        runtime_root=args.runtime_root,
        task_ids=selection.task_ids,
        checkout=args.checkout,
        output_root=args.output_root,
        batch_size=args.batch_size,
        timeout=args.timeout,
        campaign_id=args.campaign_id,
        skip_existing=not args.no_skip_existing,
        expected_commits=selection.expected_commits,
        expected_task_modules=dict(selection.expected_task_modules),
    )
    if args.json:
        print(json.dumps(result, indent=2, ensure_ascii=False, sort_keys=True))
    else:
        print(
            "CURRENT_EXACT_BUILD_BATCH "
            f"status={result['status']} requested={result['requested']} "
            f"emitted={result['emitted']} skipped={result['skipped_existing']} "
            f"batches={result['build_batches']} commit={result['catalog_mat_commit']}"
        )
        for task in result["tasks"]:
            print(f"{task['status']} {task['task_id']} {task['receipt']}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ExactBuildBatchError as exc:
        print(f"MAT_CATALOG_EXACT_BUILD_BATCH_ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
