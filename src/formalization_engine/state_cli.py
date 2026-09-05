from __future__ import annotations

import argparse
from collections import Counter
import json
import sqlite3
import sys
from pathlib import Path
from typing import Any

from formalization_engine.block_id_naming import canonicalize_block_id

from .state_bundle_delta import analyze_current_mat_bundles
from .state_catalog_sync import CatalogSyncError, sync_active_catalog
from .state_migration import rebuild_invariants, rebuild_workspace_database
from .state_pr_review import (
    ExternalPrReviewError,
    adopt_external_pr_evidence,
    apply_external_pr_review,
    prepare_external_pr_review,
)
from .state_reconcile import refresh_workspace_state
from .state_snapshot import create_dataset_snapshot
from .state_store import StateIntegrityError, WorkspaceStateStore, canonical_state_path
from .state_transformation_receipt import (
    TransformationReceiptError,
    emit_validated_transformation,
    emit_validated_transformations_batch,
    inspect_validated_transformation,
)
from .task_catalog import CatalogError, load_catalog


def _state_path(settings) -> Path:
    raw = getattr(settings, "state_db_file", None)
    path = Path(raw or canonical_state_path(settings.artifact_root))
    WorkspaceStateStore.validate_canonical_path(
        path,
        runtime_root=Path(settings.runtime_root),
        artifact_root=Path(settings.artifact_root),
    )
    return path


def _print_json(payload: Any) -> None:
    print(json.dumps(payload, indent=2, ensure_ascii=False, sort_keys=True))


def _batch_task_ids(raw_tasks: list[str], task_file: Path | None) -> list[str]:
    tasks = list(raw_tasks)
    if task_file is not None:
        try:
            raw = task_file.expanduser().read_text(encoding="utf-8")
        except OSError as exc:
            raise TransformationReceiptError(f"Unable to read task list {task_file}: {exc}") from exc
        stripped = raw.strip()
        if stripped.startswith("["):
            try:
                parsed = json.loads(stripped)
            except json.JSONDecodeError as exc:
                raise TransformationReceiptError(f"Task list JSON is invalid: {exc}") from exc
            if not isinstance(parsed, list):
                raise TransformationReceiptError("Task list JSON must be an array")
            tasks.extend(str(item) for item in parsed)
        else:
            tasks.extend(
                item.strip()
                for line in raw.splitlines()
                for item in line.split(",")
                if item.strip() and not item.lstrip().startswith("#")
            )
    canonical = sorted({canonicalize_block_id(item) for item in tasks})
    if not canonical or any(not item for item in canonical):
        raise TransformationReceiptError("emit-batch requires valid --task or --task-file entries")
    return canonical


def _short_subject(head: dict[str, Any] | None) -> str:
    if not head:
        return "missing"
    bundle_hash = str(head.get("bundle_hash", "") or "")
    commit = str(head.get("source_commit", "") or "")
    freshness = str(head.get("freshness", "") or "")
    pieces = [bundle_hash[:12] or "unknown-hash"]
    if commit:
        pieces.append(f"commit={commit[:12]}")
    if freshness:
        pieces.append(f"freshness={freshness}")
    return " ".join(pieces)


def render_task_status(
    report: dict[str, Any],
    *,
    refresh_result: dict[str, Any] | None = None,
    profile: str = "mat",
) -> str:
    lines = [f"TASK={report.get('task_id', '')}", f"DATABASE_STATUS={report.get('database_status', 'unknown')}"]
    if report.get("database_status") != "ok":
        for action in report.get("actions", []):
            lines.append(f"ACTION={action}")
        return "\n".join(lines) + "\n"
    heads = report.get("heads", {})
    if profile == "mat":
        lines.extend(
            [
                f"MAT_MAIN={_short_subject(heads.get('mat_main'))}",
                f"MAT_CANDIDATE={_short_subject(heads.get('mat_candidate'))}",
                f"TOY_CURRENT={_short_subject(heads.get('toy_current'))}",
                f"KENNETH_MAIN={_short_subject(heads.get('kenneth_main'))}",
                f"KENNETH_PR_HEAD={_short_subject(heads.get('kenneth_pr_head'))}",
            ]
        )
    else:
        lines.extend(
            [
                f"{profile.upper()}_CURRENT={_short_subject(heads.get(f'{profile}_current'))}",
                f"{profile.upper()}_REVIEWED={_short_subject(heads.get(f'{profile}_reviewed'))}",
            ]
        )
    review = report.get("latest_current_review")
    if review:
        lines.append(
            "LATEST_REVIEW="
            f"{review.get('verdict', '')}/{review.get('phase2_status', '')} "
            f"subject={str(review.get('subject_id', ''))[:12]} "
            f"scope={review.get('authority_scope', '')}"
        )
    else:
        lines.append("LATEST_REVIEW=none_covering_current_heads")
    if profile == "mat":
        coverage = report.get("candidate_review_coverage")
        lines.append(
            "MAT_CANDIDATE_COVERAGE="
            + (
                f"{coverage.get('coverage_kind', 'exact')} review={str(coverage.get('review_id', ''))[:12]}"
                if coverage
                else "none"
            )
        )
        authority = report.get("candidate_authority_coverage")
        lines.append(
            "MAT_CANDIDATE_AUTHORITY="
            + (
                f"{authority.get('capability', '')} route={authority.get('bridge_route', '')} "
                f"binding={str(authority.get('binding_id', ''))[:12]}"
                if authority
                else "none"
            )
        )
        partial = report.get("candidate_partial_review")
        lines.append(
            "MAT_CANDIDATE_PARTIAL_REVIEW="
            + (
                f"{partial.get('coverage_kind', '')} review={str(partial.get('review_id', ''))[:12]}"
                if partial
                else "none"
            )
        )
    for role, item in sorted(report.get("head_partial_review_coverage", {}).items()):
        lines.append(
            f"PARTIAL_REVIEW={role} {item.get('coverage_kind', '')} "
            f"review={str(item.get('review_id', ''))[:12]}"
        )
    for role, item in sorted(report.get("head_authority_coverage", {}).items()):
        lines.append(
            f"TYPED_AUTHORITY={role} {item.get('capability', '')} "
            f"route={item.get('bridge_route', '')} "
            f"binding={str(item.get('binding_id', ''))[:12]}"
        )
    for integration in report.get("integrations", []):
        if integration.get("integration_kind") == "pull_request":
            lines.append(
                f"PR={integration.get('pr_number', '')} state={integration.get('state', '')} "
                f"head={str(integration.get('head_sha', ''))[:12]} "
                f"merge={str(integration.get('merge_sha', ''))[:12]} "
                f"freshness={integration.get('remote_freshness', '')}"
            )
    actions = report.get("actions", [])
    lines.append("ACTIONS=" + (",".join(actions) if actions else "none"))
    if refresh_result:
        errors = list((refresh_result.get("local") or {}).get("errors", []))
        errors.extend((refresh_result.get("remote") or {}).get("errors", []))
        lines.append("REFRESH=" + ("ok" if not errors else "partial"))
        for error in errors:
            lines.append(f"REFRESH_ERROR={error}")
    return "\n".join(lines) + "\n"


def _authoritative_completion(store: WorkspaceStateStore, settings) -> dict[str, Any]:
    try:
        catalog = load_catalog(
            workspace_root=Path(settings.workspace_root),
            runtime_root=Path(settings.runtime_root),
        )
        invariants = rebuild_invariants(store, catalog)
    except (CatalogError, OSError, sqlite3.DatabaseError, StateIntegrityError) as exc:
        return {
            "status": "unavailable",
            "all_required_pass": None,
            "compatible_pass_found": None,
            "catalog_expected": None,
            "required_incomplete": None,
            "error": str(exc),
            "source": "state.sqlite3 + pinned catalog",
        }

    compatible = invariants.get("compatible_pass", {})
    missing = list(compatible.get("all_catalog_missing", []))
    exact_current_coverage = int(
        invariants.get(
            "exact_current_catalog_bundle_coverage",
            invariants.get("exact_current_mat_bundle_coverage", 0),
        )
    )
    return {
        "profile": str(invariants.get("profile", getattr(settings, "profile", "mat"))),
        "status": "pass" if invariants.get("all_required_pass") else "fail",
        "all_required_pass": bool(invariants.get("all_required_pass")),
        "compatible_pass_found": int(compatible.get("all_catalog_found", 0)),
        "catalog_expected": int(compatible.get("all_catalog_expected", 0)),
        "required_incomplete": len(missing),
        "missing_task_ids": missing,
        "exact_current_catalog_bundle_coverage": exact_current_coverage,
        "exact_current_mat_bundle_coverage": exact_current_coverage,
        "source": "state.sqlite3 + pinned catalog",
    }


def _candidate_maintenance(rows: list[dict[str, Any]]) -> dict[str, Any]:
    action_counts: Counter[str] = Counter()
    for row in rows:
        action_counts.update(str(action) for action in row.get("actions", []))
        if row.get("active_runs"):
            action_counts["active_run"] += 1
    return {
        "count": len(rows),
        "action_counts": dict(sorted(action_counts.items())),
        "scope": "working_tree_candidate_maintenance",
        "affects_authoritative_catalog_completion": False,
    }


def render_worklist(
    rows: list[dict[str, Any]],
    *,
    completion: dict[str, Any] | None = None,
    refresh_result: dict[str, Any] | None = None,
) -> str:
    completion = completion or {"status": "unavailable"}
    maintenance = _candidate_maintenance(rows)
    lines = [
        f"AUTHORITATIVE_CATALOG_COMPLETION\t{str(completion.get('status', 'unavailable')).upper()}",
    ]
    if completion.get("catalog_expected") is not None:
        lines.extend(
            [
                "CATALOG_COMPATIBLE_PASS\t"
                f"{completion.get('compatible_pass_found', 0)}/{completion.get('catalog_expected', 0)}",
                f"REQUIRED_INCOMPLETE\t{completion.get('required_incomplete', 0)}",
            ]
        )
    elif completion.get("error"):
        lines.append(f"COMPLETION_STATUS_ERROR\t{completion['error']}")
    lines.extend(
        [
            f"CANDIDATE_MAINTENANCE\t{maintenance['count']}",
            "CANDIDATE_MAINTENANCE_IS_CATALOG_FAILURE\tfalse",
            "TASK\tACTIONS",
        ]
    )
    for row in rows:
        actions = list(row.get("actions", []))
        if row.get("active_runs"):
            actions.append("active_run")
        lines.append(f"{row.get('task_id', '')}\t{','.join(dict.fromkeys(actions)) or 'none'}")
    if len(lines) == 1:
        lines.append("-\tnone")
    if refresh_result:
        errors = list((refresh_result.get("local") or {}).get("errors", []))
        errors.extend((refresh_result.get("remote") or {}).get("errors", []))
        lines.append(f"REFRESH\t{'ok' if not errors else 'partial'}")
        lines.extend(f"REFRESH_ERROR\t{error}" for error in errors)
    return "\n".join(lines) + "\n"


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="formalize state", add_help=True)
    subparsers = parser.add_subparsers(dest="command", required=True)

    status = subparsers.add_parser("status", help="Show current derived state for one task or the workspace")
    status.add_argument("task", nargs="?", default="")
    status.add_argument("--refresh", action="store_true", default=True, help=argparse.SUPPRESS)
    status.add_argument("--no-refresh", action="store_false", dest="refresh", help="Use the last recorded repository observations")
    status.add_argument("--json", action="store_true", dest="as_json")

    worklist = subparsers.add_parser(
        "worklist",
        help="Show working-tree candidate maintenance; not catalog completion failures",
    )
    worklist.add_argument("--refresh", action="store_true", default=True, help=argparse.SUPPRESS)
    worklist.add_argument("--no-refresh", action="store_false", dest="refresh", help="Use the last recorded repository observations")
    worklist.add_argument("--json", action="store_true", dest="as_json")

    state = subparsers.add_parser("state", help="Administrative workspace state operations")
    state_subparsers = state.add_subparsers(dest="state_command", required=True)
    rebuild = state_subparsers.add_parser("rebuild", help="Rebuild SQLite state from immutable evidence and repositories")
    rebuild.add_argument("--refresh-remotes", action="store_true")
    rebuild.add_argument("--root", action="append", default=[], help="Additional/override legacy evidence root")
    rebuild.add_argument(
        "--check-only",
        action="store_true",
        help="Build and validate a temporary database without replacing canonical state",
    )
    rebuild.add_argument("--json", action="store_true", dest="as_json")
    validate = state_subparsers.add_parser(
        "validate", help="Re-run catalog and coverage invariants against existing state"
    )
    validate.add_argument("--json", action="store_true", dest="as_json")
    catalog_sync = state_subparsers.add_parser(
        "catalog-sync",
        help="Activate the current non-MAT catalog without manufacturing review authority",
    )
    catalog_sync.add_argument(
        "--check-only",
        action="store_true",
        help="Report the activation delta without writing SQLite",
    )
    catalog_sync.add_argument("--json", action="store_true", dest="as_json")
    snapshot = state_subparsers.add_parser(
        "snapshot", help="Write a deterministic analysis dataset from existing state"
    )
    snapshot.add_argument("--output", type=Path, required=True)
    snapshot.add_argument(
        "--no-record",
        action="store_true",
        help="Write the payload without registering its dataset id in SQLite",
    )
    snapshot.add_argument("--json", action="store_true", dest="as_json")
    bundle_delta = state_subparsers.add_parser(
        "bundle-delta",
        help="Classify current MAT bundles against compatible authoritative reviews",
    )
    bundle_delta.add_argument("--task", action="append", default=[])
    bundle_delta.add_argument("--json", action="store_true", dest="as_json")
    transformation = state_subparsers.add_parser(
        "transformation",
        help="Inspect or emit an immutable path-only transformation receipt",
    )
    transformation_subparsers = transformation.add_subparsers(
        dest="transformation_command", required=True
    )
    transformation_inspect = transformation_subparsers.add_parser(
        "inspect", help="Check whether one current MAT task is strictly path-only"
    )
    transformation_inspect.add_argument("--task", required=True)
    transformation_inspect.add_argument("--source-review-id", default="")
    transformation_inspect.add_argument("--checkout", type=Path)
    transformation_inspect.add_argument("--json", action="store_true", dest="as_json")
    transformation_emit = transformation_subparsers.add_parser(
        "emit", help="Run focused checks and write immutable transformation evidence"
    )
    transformation_emit.add_argument("--task", required=True)
    transformation_emit.add_argument("--source-review-id", default="")
    transformation_emit.add_argument("--checkout", type=Path)
    transformation_emit.add_argument("--output-dir", type=Path, required=True)
    transformation_emit.add_argument("--timeout", type=int, default=1800)
    transformation_emit.add_argument("--json", action="store_true", dest="as_json")
    transformation_batch = transformation_subparsers.add_parser(
        "emit-batch", help="Build many path-only tasks once and emit independent receipts"
    )
    transformation_batch.add_argument("--task", action="append", default=[])
    transformation_batch.add_argument("--task-file", type=Path)
    transformation_batch.add_argument("--checkout", type=Path)
    transformation_batch.add_argument("--output-dir", type=Path, required=True)
    transformation_batch.add_argument("--timeout", type=int, default=1800)
    transformation_batch.add_argument(
        "--no-skip-existing", action="store_false", dest="skip_existing", default=True
    )
    transformation_batch.add_argument("--json", action="store_true", dest="as_json")

    pr_review = subparsers.add_parser(
        "pr-review",
        help="Prepare or apply a semantic review bound to one exact Kenneth PR head",
    )
    pr_review_subparsers = pr_review.add_subparsers(dest="pr_review_command", required=True)
    pr_prepare = pr_review_subparsers.add_parser(
        "prepare",
        help="Verify a clean exact-head checkout, build it, and write immutable review materials",
    )
    pr_prepare.add_argument("--task", required=True)
    pr_prepare.add_argument("--repo", default="wkshum/ProbabilityTheory")
    pr_prepare.add_argument("--pr", type=int, required=True, dest="pr_number")
    pr_prepare.add_argument("--checkout", type=Path, required=True)
    pr_prepare.add_argument("--timeout", type=int, default=1800)
    pr_prepare.add_argument("--json", action="store_true", dest="as_json")
    pr_apply = pr_review_subparsers.add_parser(
        "apply",
        help="Validate an independent result against the unchanged exact PR head and record coverage",
    )
    pr_apply.add_argument("--request", type=Path, required=True, dest="metadata_path")
    pr_apply.add_argument("--result", type=Path, required=True, dest="result_path")
    pr_apply.add_argument("--json", action="store_true", dest="as_json")
    pr_adopt = pr_review_subparsers.add_parser(
        "adopt",
        help="Validate and apply completed exact-head evidence created before the first-class CLI existed",
    )
    pr_adopt.add_argument("--task", required=True)
    pr_adopt.add_argument("--repo", default="wkshum/ProbabilityTheory")
    pr_adopt.add_argument("--pr", type=int, required=True, dest="pr_number")
    pr_adopt.add_argument("--review", type=Path, required=True, dest="review_path")
    pr_adopt.add_argument("--classification", type=Path, required=True, dest="classification_path")
    pr_adopt.add_argument("--builder-evidence", type=Path, required=True, dest="builder_path")
    pr_adopt.add_argument("--json", action="store_true", dest="as_json")
    return parser


def main(argv: list[str], settings) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    state_path = _state_path(settings)
    store = WorkspaceStateStore(state_path)

    if args.command == "state" and args.state_command == "rebuild":
        roots = [Path(root).expanduser().resolve() for root in args.root] or None
        def progress(phase: str, detail: dict[str, Any]) -> None:
            rendered = json.dumps(detail, ensure_ascii=False, sort_keys=True)
            print(f"REBUILD_PHASE={phase} {rendered}", file=sys.stderr, flush=True)

        report = rebuild_workspace_database(
            state_path=state_path,
            workspace_root=Path(settings.workspace_root),
            runtime_root=Path(settings.runtime_root),
            roots=roots,
            refresh_remote=args.refresh_remotes,
            replace_target=not args.check_only,
            progress=progress,
        )
        payload = report.as_dict()
        if args.as_json:
            _print_json(payload)
        else:
            for key, value in payload.items():
                if key in {"warnings", "errors"}:
                    continue
                print(f"{key.upper()}={value}")
            for warning in payload["warnings"]:
                print(f"MIGRATION_WARNING={warning}")
            for error in payload["errors"]:
                print(f"MIGRATION_ERROR={error}")
        return 0 if not report.errors else 2

    if not store.exists:
        payload = {
            "database": str(state_path),
            "database_status": "missing_not_created",
            "next_action": "formalize state rebuild",
        }
        if getattr(args, "as_json", False):
            _print_json(payload)
        else:
            print(f"STATE_DB_FILE={state_path}")
            print("STATE_DB_STATUS=missing_not_created")
            print("NEXT_ACTION=formalize state rebuild")
        return 2

    store.assert_integrity()
    if args.command == "state" and args.state_command == "catalog-sync":
        try:
            catalog = load_catalog(
                workspace_root=Path(settings.workspace_root),
                runtime_root=Path(settings.runtime_root),
            )
            payload = sync_active_catalog(
                store=store,
                catalog=catalog,
                workspace_root=Path(settings.workspace_root),
                runtime_root=Path(settings.runtime_root),
                check_only=args.check_only,
            )
        except (CatalogError, CatalogSyncError) as exc:
            payload = {"status": "error", "error": str(exc)}
            if args.as_json:
                _print_json(payload)
            else:
                print("CATALOG_SYNC_STATUS=error")
                print(f"CATALOG_SYNC_ERROR={exc}")
            return 2
        if args.as_json:
            _print_json(payload)
        else:
            for key, value in payload.items():
                if isinstance(value, (dict, list)):
                    value = json.dumps(value, ensure_ascii=False, sort_keys=True)
                print(f"{key.upper()}={value}")
        return 0

    if args.command == "state" and args.state_command == "transformation":
        try:
            if args.transformation_command == "inspect":
                payload = inspect_validated_transformation(
                    store=store,
                    workspace_root=Path(settings.workspace_root),
                    runtime_root=Path(settings.runtime_root),
                    task_id=args.task,
                    source_review_id=args.source_review_id,
                    checkout=args.checkout,
                )
            elif args.transformation_command == "emit":
                payload = emit_validated_transformation(
                    store=store,
                    workspace_root=Path(settings.workspace_root),
                    runtime_root=Path(settings.runtime_root),
                    task_id=args.task,
                    output_dir=args.output_dir,
                    source_review_id=args.source_review_id,
                    checkout=args.checkout,
                    timeout=args.timeout,
                )
            else:
                payload = emit_validated_transformations_batch(
                    store=store,
                    workspace_root=Path(settings.workspace_root),
                    runtime_root=Path(settings.runtime_root),
                    task_ids=_batch_task_ids(args.task, args.task_file),
                    output_dir=args.output_dir,
                    checkout=args.checkout,
                    timeout=args.timeout,
                    skip_existing=args.skip_existing,
                )
        except TransformationReceiptError as exc:
            payload = {"status": "error", "error": str(exc)}
            if args.as_json:
                _print_json(payload)
            else:
                print("TRANSFORMATION_STATUS=error")
                print(f"TRANSFORMATION_ERROR={exc}")
            return 2
        if args.as_json:
            _print_json(payload)
        else:
            for key, value in payload.items():
                if isinstance(value, (dict, list)):
                    value = json.dumps(value, ensure_ascii=False, sort_keys=True)
                print(f"{key.upper()}={value}")
        return 0

    if args.command == "state" and args.state_command == "validate":
        catalog = load_catalog(
            workspace_root=Path(settings.workspace_root),
            runtime_root=Path(settings.runtime_root),
        )
        try:
            payload = rebuild_invariants(store, catalog)
        except sqlite3.OperationalError as exc:
            if "no such table" not in str(exc).lower():
                raise
            payload = {
                "database": str(state_path),
                "database_status": "legacy_schema_rebuild_required",
                "error": str(exc),
                "next_action": "formalize state rebuild --check-only",
            }
            if args.as_json:
                _print_json(payload)
            else:
                print(f"STATE_DB_FILE={state_path}")
                print("STATE_DB_STATUS=legacy_schema_rebuild_required")
                print(f"STATE_DB_ERROR={exc}")
                print("NEXT_ACTION=formalize state rebuild --check-only")
            return 2
        if args.as_json:
            _print_json(payload)
        else:
            for key, value in payload.get("required", {}).items():
                print(f"INVARIANT_{key.upper()}={'pass' if value else 'fail'}")
            print(f"ALL_REQUIRED_PASS={str(bool(payload.get('all_required_pass'))).lower()}")
        return 0 if payload.get("all_required_pass") else 2

    if args.command == "state" and args.state_command == "snapshot":
        catalog = load_catalog(
            workspace_root=Path(settings.workspace_root),
            runtime_root=Path(settings.runtime_root),
        )
        invariants = rebuild_invariants(store, catalog)
        if not invariants.get("all_required_pass"):
            raise StateIntegrityError("Refusing to snapshot state that fails required invariants.")
        snapshot = create_dataset_snapshot(
            store,
            invariants=invariants,
            workspace_root=Path(settings.workspace_root),
            output_path=args.output,
            persist=not args.no_record,
        )
        payload = snapshot.as_dict()
        if args.as_json:
            _print_json(payload)
        else:
            for key, value in payload.items():
                if isinstance(value, (dict, list)):
                    value = json.dumps(value, ensure_ascii=False, sort_keys=True)
                print(f"{key.upper()}={value}")
        return 0

    if args.command == "state" and args.state_command == "bundle-delta":
        payload = analyze_current_mat_bundles(store, task_ids=args.task or None)
        if args.as_json:
            _print_json(payload)
        else:
            print(f"TASK_COUNT={payload['task_count']}")
            for status, count in payload["status_counts"].items():
                print(f"STATUS_{status.upper()}={count}")
        return 0

    if args.command == "pr-review":
        try:
            if args.pr_review_command == "prepare":
                if args.pr_number <= 0:
                    parser.error("--pr must be positive")
                if args.timeout <= 0:
                    parser.error("--timeout must be positive")
                task_id = canonicalize_block_id(args.task)
                if not task_id:
                    parser.error("--task must be a valid canonical task id")
                payload = prepare_external_pr_review(
                    settings=settings,
                    store=store,
                    repo=args.repo,
                    pr_number=args.pr_number,
                    task_id=task_id,
                    checkout=args.checkout,
                    timeout=args.timeout,
                )
            elif args.pr_review_command == "apply":
                payload = apply_external_pr_review(
                    settings=settings,
                    store=store,
                    metadata_path=args.metadata_path,
                    result_path=args.result_path,
                )
            else:
                if args.pr_number <= 0:
                    parser.error("--pr must be positive")
                task_id = canonicalize_block_id(args.task)
                if not task_id:
                    parser.error("--task must be a valid canonical task id")
                payload = adopt_external_pr_evidence(
                    settings=settings,
                    store=store,
                    repo=args.repo,
                    pr_number=args.pr_number,
                    task_id=task_id,
                    review_path=args.review_path,
                    classification_path=args.classification_path,
                    builder_path=args.builder_path,
                )
        except ExternalPrReviewError as exc:
            if args.as_json:
                _print_json({"status": "error", "error": str(exc)})
            else:
                print(f"PR_REVIEW_STATUS=error\nPR_REVIEW_ERROR={exc}")
            return 2
        if args.as_json:
            _print_json(payload)
        else:
            for key, value in payload.items():
                if isinstance(value, (dict, list)):
                    value = json.dumps(value, ensure_ascii=False, sort_keys=True)
                print(f"{key.upper()}={value}")
        return 0

    refresh_result = None
    profile = str(getattr(settings, "profile", "mat") or "mat").strip().lower()
    task_id = canonicalize_block_id(getattr(args, "task", "") or "", profile)
    if getattr(args, "task", "") and not task_id:
        parser.error("task must be a valid canonical task id")
    if getattr(args, "refresh", False):
        refresh_catalog = None
        if profile != "mat":
            refresh_catalog = load_catalog(
                workspace_root=Path(settings.workspace_root),
                runtime_root=Path(settings.runtime_root),
            )
        refresh_result = refresh_workspace_state(
            store,
            workspace_root=Path(settings.workspace_root),
            runtime_root=Path(settings.runtime_root),
            task_ids=[task_id] if task_id else None,
            chapters=(1, 2, 3, 4),
            refresh_remote=profile == "mat",
            catalog=refresh_catalog,
        )

    if args.command == "status":
        if task_id:
            report = store.task_report(task_id)
            if args.as_json:
                _print_json({"status": report, "refresh": refresh_result})
            else:
                print(
                    render_task_status(
                        report,
                        refresh_result=refresh_result,
                        profile=profile,
                    ),
                    end="",
                )
        else:
            completion = _authoritative_completion(store, settings)
            rows = store.worklist()
            payload = store.summary()
            payload["authoritative_completion"] = completion
            payload["candidate_maintenance"] = _candidate_maintenance(rows)
            payload["worklist_count"] = len(rows)
            payload["refresh"] = refresh_result
            if args.as_json:
                _print_json(payload)
            else:
                for key, value in payload.items():
                    if key != "refresh":
                        if isinstance(value, (dict, list)):
                            value = json.dumps(value, ensure_ascii=False, sort_keys=True)
                        print(f"{key.upper()}={value}")
        return 0

    rows = store.worklist()
    completion = _authoritative_completion(store, settings)
    maintenance = _candidate_maintenance(rows)
    if args.as_json:
        _print_json(
            {
                "authoritative_completion": completion,
                "candidate_maintenance": maintenance,
                "worklist": rows,
                "refresh": refresh_result,
            }
        )
    else:
        print(
            render_worklist(
                rows,
                completion=completion,
                refresh_result=refresh_result,
            ),
            end="",
        )
    return 0
