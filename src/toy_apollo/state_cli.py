from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from src.block_id_naming import canonicalize_block_id

from .state_migration import rebuild_workspace_database
from .state_pr_review import (
    ExternalPrReviewError,
    adopt_external_pr_evidence,
    apply_external_pr_review,
    prepare_external_pr_review,
)
from .state_reconcile import refresh_workspace_state
from .state_store import StateIntegrityError, WorkspaceStateStore, canonical_state_path


def _state_path(settings) -> Path:
    raw = getattr(settings, "state_db_file", None)
    path = Path(raw or canonical_state_path(settings.runtime_root))
    WorkspaceStateStore.validate_canonical_path(
        path,
        runtime_root=Path(settings.runtime_root),
        artifact_root=Path(settings.artifact_root),
    )
    return path


def _print_json(payload: Any) -> None:
    print(json.dumps(payload, indent=2, ensure_ascii=False, sort_keys=True))


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


def render_task_status(report: dict[str, Any], *, refresh_result: dict[str, Any] | None = None) -> str:
    lines = [f"TASK={report.get('task_id', '')}", f"DATABASE_STATUS={report.get('database_status', 'unknown')}"]
    if report.get("database_status") != "ok":
        for action in report.get("actions", []):
            lines.append(f"ACTION={action}")
        return "\n".join(lines) + "\n"
    heads = report.get("heads", {})
    lines.extend(
        [
            f"MAT_MAIN={_short_subject(heads.get('mat_main'))}",
            f"MAT_CANDIDATE={_short_subject(heads.get('mat_candidate'))}",
            f"TOY_CURRENT={_short_subject(heads.get('toy_current'))}",
            f"KENNETH_MAIN={_short_subject(heads.get('kenneth_main'))}",
            f"KENNETH_PR_HEAD={_short_subject(heads.get('kenneth_pr_head'))}",
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
    coverage = report.get("candidate_review_coverage")
    lines.append(
        "MAT_CANDIDATE_COVERAGE="
        + (
            f"{coverage.get('coverage_kind', 'exact')} review={str(coverage.get('review_id', ''))[:12]}"
            if coverage
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


def render_worklist(rows: list[dict[str, Any]], *, refresh_result: dict[str, Any] | None = None) -> str:
    lines = ["TASK\tACTIONS"]
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
    parser = argparse.ArgumentParser(prog="toy-apollo-state", add_help=True)
    subparsers = parser.add_subparsers(dest="command", required=True)

    status = subparsers.add_parser("status", help="Show current derived state for one task or the workspace")
    status.add_argument("task", nargs="?", default="")
    status.add_argument("--refresh", action="store_true", default=True, help=argparse.SUPPRESS)
    status.add_argument("--no-refresh", action="store_false", dest="refresh", help="Use the last recorded repository observations")
    status.add_argument("--json", action="store_true", dest="as_json")

    worklist = subparsers.add_parser("worklist", help="Show only tasks that need action")
    worklist.add_argument("--refresh", action="store_true", default=True, help=argparse.SUPPRESS)
    worklist.add_argument("--no-refresh", action="store_false", dest="refresh", help="Use the last recorded repository observations")
    worklist.add_argument("--json", action="store_true", dest="as_json")

    state = subparsers.add_parser("state", help="Administrative workspace state operations")
    state_subparsers = state.add_subparsers(dest="state_command", required=True)
    rebuild = state_subparsers.add_parser("rebuild", help="Rebuild SQLite state from immutable evidence and repositories")
    rebuild.add_argument("--refresh-remotes", action="store_true")
    rebuild.add_argument("--root", action="append", default=[], help="Additional/override legacy evidence root")
    rebuild.add_argument("--json", action="store_true", dest="as_json")

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
        report = rebuild_workspace_database(
            state_path=state_path,
            workspace_root=Path(settings.workspace_root),
            runtime_root=Path(settings.runtime_root),
            roots=roots,
            refresh_remote=args.refresh_remotes,
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
            "next_action": "python run_chapter.py state rebuild",
        }
        if getattr(args, "as_json", False):
            _print_json(payload)
        else:
            print(f"STATE_DB_FILE={state_path}")
            print("STATE_DB_STATUS=missing_not_created")
            print("NEXT_ACTION=python run_chapter.py state rebuild")
        return 2

    store.assert_integrity()
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
    task_id = canonicalize_block_id(getattr(args, "task", "") or "")
    if getattr(args, "task", "") and not task_id:
        parser.error("task must be a valid canonical task id")
    if getattr(args, "refresh", False):
        refresh_result = refresh_workspace_state(
            store,
            workspace_root=Path(settings.workspace_root),
            runtime_root=Path(settings.runtime_root),
            task_ids=[task_id] if task_id else None,
            chapters=(1, 2, 3, 4),
            refresh_remote=True,
        )

    if args.command == "status":
        if task_id:
            report = store.task_report(task_id)
            if args.as_json:
                _print_json({"status": report, "refresh": refresh_result})
            else:
                print(render_task_status(report, refresh_result=refresh_result), end="")
        else:
            payload = store.summary()
            payload["worklist_count"] = len(store.worklist())
            payload["refresh"] = refresh_result
            if args.as_json:
                _print_json(payload)
            else:
                for key, value in payload.items():
                    if key != "refresh":
                        print(f"{key.upper()}={value}")
        return 0

    rows = store.worklist()
    if args.as_json:
        _print_json({"worklist": rows, "refresh": refresh_result})
    else:
        print(render_worklist(rows, refresh_result=refresh_result), end="")
    return 0
