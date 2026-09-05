#!/usr/bin/env python3
"""Generate the unified Formalization workspace and catalog-task status report."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formalization_engine.workspace_status import (
    WorkspaceStatusError,
    build_workspace_status,
    capture_workspace_baseline,
    load_workspace_policy,
    render_workspace_status,
    write_workspace_outputs,
)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Inspect repositories, worktrees, state.sqlite3, all 452 tasks, and file roles"
    )
    parser.add_argument("--workspace-root", type=Path, default=REPO_ROOT.parent)
    parser.add_argument("--runtime-root", type=Path, default=REPO_ROOT)
    parser.add_argument(
        "--policy",
        type=Path,
        default=REPO_ROOT / "data" / "workspace_inventory" / "policy_v2.json",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        help="Default: <workspace>/ProbabilityTheoryFormalization-artifacts/workspace_status",
    )
    parser.add_argument(
        "--markdown",
        type=Path,
        help="Default: <workspace>/CURRENT_STATUS.md",
    )
    parser.add_argument("--write", action="store_true", help="Write current JSON, Markdown, and gzip JSONL inventory")
    parser.add_argument("--capture-baseline", action="store_true", help="Capture non-destructive Git patches and untracked listings")
    parser.add_argument("--compare-latest-rebuild", action="store_true", help="Compare the live state dataset with the newest check-only rebuild")
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args()

    workspace_root = args.workspace_root.resolve()
    runtime_root = args.runtime_root.resolve()
    output_dir = (
        args.output_dir.resolve()
        if args.output_dir
        else workspace_root / "ProbabilityTheoryFormalization-artifacts" / "workspace_status"
    )
    markdown_path = (
        args.markdown.resolve() if args.markdown else workspace_root / "CURRENT_STATUS.md"
    )
    payload, file_sets = build_workspace_status(
        workspace_root=workspace_root,
        runtime_root=runtime_root,
        policy_path=args.policy.resolve(),
        compare_latest_rebuild=args.compare_latest_rebuild,
    )
    result: dict[str, object] = {"status": payload}
    policy = load_workspace_policy(args.policy.resolve())
    if args.write:
        result["outputs"] = write_workspace_outputs(
            payload=payload,
            repository_file_sets=file_sets,
            workspace_root=workspace_root,
            runtime_root=runtime_root,
            policy=policy,
            output_dir=output_dir,
            markdown_path=markdown_path,
        )
    if args.capture_baseline:
        repositories = [workspace_root / path for path in policy["repositories"]]
        result["baseline"] = capture_workspace_baseline(
            workspace_root=workspace_root,
            repositories=repositories,
            worktrees=payload["worktrees"],
            output_root=output_dir,
        )
    if args.as_json:
        print(json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2))
    elif args.write or args.capture_baseline:
        print(json.dumps({key: value for key, value in result.items() if key != "status"}, ensure_ascii=False, sort_keys=True, indent=2))
    else:
        print(render_workspace_status(payload))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except WorkspaceStatusError as exc:
        print(f"WORKSPACE_STATUS_ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
