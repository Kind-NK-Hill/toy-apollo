from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formalization_engine.state_boundary_delta_receipt import (  # noqa: E402
    BoundaryDeltaReceiptError,
    _atomic_publish_no_replace,
    build_verified_boundary_delta,
    emit_verified_boundary_delta_batch,
)
from formalization_engine.block_id_naming import canonicalize_block_id, is_canonical_block_id  # noqa: E402


def _task_selection(tasks: list[str], task_files: list[Path]) -> list[str]:
    selected = list(tasks)
    for path in task_files:
        try:
            text = path.read_text(encoding="utf-8")
        except OSError as exc:
            raise BoundaryDeltaReceiptError(f"cannot read task file {path}: {exc}") from exc
        try:
            payload = json.loads(text)
        except json.JSONDecodeError:
            payload = [line.strip() for line in text.splitlines() if line.strip()]
        if isinstance(payload, dict):
            payload = payload.get("tasks", payload.get("task_ids"))
        if not isinstance(payload, list) or not all(isinstance(item, str) and item.strip() for item in payload):
            raise BoundaryDeltaReceiptError(f"task file must contain a JSON string list or one task per line: {path}")
        selected.extend(item.strip() for item in payload)
    if not selected:
        raise BoundaryDeltaReceiptError("emit-batch requires at least one --task or --task-file entry")
    canonical: list[str] = []
    for raw in selected:
        task_id = canonicalize_block_id(raw.strip())
        if task_id != raw.strip() or not task_id or not is_canonical_block_id(task_id):
            raise BoundaryDeltaReceiptError(f"emit-batch task must be a canonical task id: {raw!r}")
        canonical.append(task_id)
    if len(set(canonical)) != len(canonical):
        raise BoundaryDeltaReceiptError("emit-batch task selection contains duplicates")
    return canonical


def _task_directories(task_root: Path, tasks: list[str]) -> list[Path]:
    root = task_root.resolve()
    directories = [(root / task).resolve() for task in tasks]
    if any(path.parent != root for path in directories):
        raise BoundaryDeltaReceiptError("emit-batch task selection escapes --task-root")
    return directories


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Inspect or emit fail-closed evidence for an import/namespace/docs/path "
            "boundary delta. This command never writes SQLite or Lean files."
        )
    )
    subparsers = parser.add_subparsers(dest="command", required=True)
    for command in ("inspect", "emit"):
        item = subparsers.add_parser(command)
        item.add_argument("--source-authority", type=Path, required=True)
        item.add_argument("--source-scope", type=Path, required=True)
        item.add_argument("--source-repo", type=Path, action="append", required=True)
        item.add_argument("--target-build", type=Path, required=True)
        item.add_argument("--target-repo", type=Path, required=True)
        item.add_argument("--policy", type=Path, required=True)
        item.add_argument("--consumer-manifest", type=Path, required=True)
        item.add_argument("--consumer-build", type=Path, action="append", default=[])
        item.add_argument("--kenneth-repo", type=Path, required=True)
        item.add_argument("--kenneth-commit", required=True)
        item.add_argument("--author-decision", type=Path)
        if command == "emit":
            item.add_argument("--output", type=Path, required=True)
    batch = subparsers.add_parser(
        "emit-batch",
        help="Consume existing exact-build receipts and emit immutable per-task boundary receipts",
    )
    batch.add_argument("--task-root", type=Path, required=True)
    batch.add_argument("--task", action="append", default=[])
    batch.add_argument("--task-file", type=Path, action="append", default=[])
    batch.add_argument("--source-repo", type=Path, action="append", required=True)
    batch.add_argument("--target-repo", type=Path, required=True)
    batch.add_argument("--kenneth-repo", type=Path, required=True)
    batch.add_argument("--target-commit", required=True)
    batch.add_argument("--kenneth-commit", required=True)
    batch.add_argument("--authority-manifest", type=Path)
    batch.add_argument("--authority-manifest-sha256", default="")
    batch.add_argument("--workspace-root", type=Path)
    batch.add_argument("--exact-build-root", type=Path)
    batch.add_argument("--no-skip-existing", action="store_true")
    args = parser.parse_args()
    if args.command == "emit-batch":
        tasks = _task_selection(args.task, args.task_file)
        result = emit_verified_boundary_delta_batch(
            task_dirs=_task_directories(args.task_root, tasks),
            source_repos=args.source_repo,
            target_repo=args.target_repo,
            kenneth_repo=args.kenneth_repo,
            expected_target_commit=args.target_commit,
            expected_kenneth_commit=args.kenneth_commit,
            skip_existing=not args.no_skip_existing,
            authority_manifest_path=args.authority_manifest,
            authority_manifest_sha256=args.authority_manifest_sha256,
            workspace_root=args.workspace_root,
            exact_build_root=args.exact_build_root,
        )
        print(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True))
        return 2 if result["failed"] else 0
    receipt = build_verified_boundary_delta(
        source_authority_path=args.source_authority,
        source_scope_path=args.source_scope,
        source_repos=args.source_repo,
        target_build_path=args.target_build,
        target_repo=args.target_repo,
        policy_path=args.policy,
        consumer_manifest_path=args.consumer_manifest,
        consumer_build_paths=args.consumer_build,
        kenneth_repo=args.kenneth_repo,
        kenneth_commit=args.kenneth_commit,
        author_decision_path=args.author_decision,
    )
    rendered = json.dumps(receipt, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    if args.command == "inspect":
        print(rendered, end="")
        return 0
    output = args.output.resolve()
    _atomic_publish_no_replace(
        output, rendered.encode("utf-8"), label="single boundary receipt",
    )
    print(str(output))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except BoundaryDeltaReceiptError as exc:
        print(f"MAT_VERIFIED_BOUNDARY_DELTA_ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
