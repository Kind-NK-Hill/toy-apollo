from __future__ import annotations

import argparse
import asyncio
import glob
import os
import sys
from pathlib import Path

from src.ledger_manager import LedgerDangerousStateError
from src.block_id_naming import (
    canonicalize_block_id,
)
from ..core.settings import get_settings
from ..state_store import canonical_state_path
from ..phase2_failure_budget import (
    PHASE2_AUTO_LOOP_BUILD_ATTEMPTS_PER_REVIEW,
    PHASE2_AUTO_LOOP_NONPROGRESS_LIMIT,
    PHASE2_AUTO_LOOP_REVIEW_ROUNDS,
)


PHASE0_MODES = ("pack", "validate", "apply")
PHASE1_MODES = ("pack", "apply")
PHASE2_MODES = (
    "pack",
    "build-check",
    "review-pack",
    "review-existing",
    "review-now",
    "review-fix",
    "auto-loop",
    "review-existing-queue",
    "review-apply",
    "dependency-reconcile",
    "basis-rebind",
    "frozen-dependency-build-check",
    "frozen-dependency-accept",
    "frozen-dependency-revoke",
    "soft-pack",
    "soft-apply",
    "batch-plan",
    "batch-run",
)
PHASE2_SINGLE_TASK_MODES = (
    "pack",
    "build-check",
    "review-pack",
    "review-existing",
    "review-now",
    "review-fix",
    "auto-loop",
    "review-apply",
    "dependency-reconcile",
    "basis-rebind",
    "frozen-dependency-build-check",
    "frozen-dependency-accept",
    "frozen-dependency-revoke",
)
PHASE2_SOFT_MODES = ("soft-pack", "soft-apply")

RUNTIME_ROOT_ENV_VAR = "TOY_APOLLO_RUNTIME_ROOT"
ARTIFACT_ROOT_ENV_VAR = "TOY_APOLLO_ARTIFACT_ROOT"
STATUS_SCOPE = "resolved_for_this_process_not_global_authority"


def parse_task_ids(raw: str) -> list[str]:
    seen: set[str] = set()
    task_ids: list[str] = []
    for part in raw.split(","):
        tid = canonicalize_block_id(part.strip())
        if not tid:
            continue
        if tid not in seen:
            seen.add(tid)
            task_ids.append(tid)
    return task_ids


def parse_batch_task_kinds(raw: str) -> list[str]:
    aliases = {
        "theorem": "theorem",
        "thm": "theorem",
        "definition": "definition",
        "def": "definition",
        "problem": "problem",
        "prob": "problem",
        "exercise": "exercise",
        "ex": "exercise",
        "remark": "remark",
        "rem": "remark",
    }
    seen: set[str] = set()
    kinds: list[str] = []
    for part in raw.split(","):
        key = part.strip().lower().replace("_", " ").replace("-", " ")
        kind = aliases.get(key)
        if not kind or kind in seen:
            continue
        seen.add(kind)
        kinds.append(kind)
    return kinds


def parse_expected_old_dependencies(raw: str) -> list[str]:
    if not str(raw or "").strip():
        return []
    dependencies: list[str] = []
    seen: set[str] = set()
    for part in raw.split(","):
        dependency = canonicalize_block_id(part.strip())
        if not dependency:
            raise ValueError(f"invalid dependency id: {part!r}")
        if dependency in seen:
            raise ValueError(f"duplicate dependency id: {dependency}")
        seen.add(dependency)
        dependencies.append(dependency)
    return dependencies


def print_read_only_status(settings) -> None:
    runtime_env_present = RUNTIME_ROOT_ENV_VAR in os.environ
    artifact_env_present = ARTIFACT_ROOT_ENV_VAR in os.environ
    runtime_env_value = os.environ.get(RUNTIME_ROOT_ENV_VAR, "")
    artifact_env_value = os.environ.get(ARTIFACT_ROOT_ENV_VAR, "")

    resolved_roots = (
        ("STATUS_SCOPE", STATUS_SCOPE),
        ("RUNTIME_ROOT", settings.runtime_root),
        ("RUNTIME_ROOT_SOURCE", "environment" if runtime_env_value else "default"),
        ("RUNTIME_ROOT_ENV_VAR", RUNTIME_ROOT_ENV_VAR),
        ("RUNTIME_ROOT_ENV_PRESENT", str(runtime_env_present).lower()),
        ("RUNTIME_ROOT_ENV_VALUE", runtime_env_value if runtime_env_present else "<unset>"),
        ("ARTIFACT_ROOT", settings.artifact_root),
        ("ARTIFACT_ROOT_SOURCE", "environment" if artifact_env_value else "default"),
        ("ARTIFACT_ROOT_ENV_VAR", ARTIFACT_ROOT_ENV_VAR),
        ("ARTIFACT_ROOT_ENV_PRESENT", str(artifact_env_present).lower()),
        ("ARTIFACT_ROOT_ENV_VALUE", artifact_env_value if artifact_env_present else "<unset>"),
        ("WORKSPACE_ROOT", settings.workspace_root),
        ("STATE_DB_FILE", settings.state_db_file or canonical_state_path(settings.runtime_root)),
        ("PLAN_ROOT", settings.plans_dir),
        ("LEDGER_ROOT", settings.project_ledger_file.parent),
        ("LEDGER_FILE", settings.project_ledger_file),
        ("PHASE1_PROMPT_PACK_ROOT", settings.phase1_prompt_packs_dir),
        ("PHASE2_PROMPT_PACK_ROOT", settings.phase2_prompt_packs_dir),
        ("DEPENDENCY_DECISION_ROOT", settings.dependency_decisions_dir),
        ("OUTPUT_ROOT", settings.toyapollo_output_dir),
    )
    for label, value in resolved_roots:
        print(f"{label}={value if value is not None else '<unset>'}")

    from ..state_store import StateIntegrityError, WorkspaceStateStore

    state_store = WorkspaceStateStore(settings.state_db_file or canonical_state_path(settings.runtime_root))
    campaign_loaded = False
    if not state_store.exists:
        print("STATE_DB_STATUS=missing_not_created")
        print("CAMPAIGN_LEDGER_STATUS=unavailable_state_db_missing")
    else:
        try:
            summary = state_store.summary()
            print("STATE_DB_STATUS=loaded_read_only")
            print(f"STATE_DB_SCHEMA_VERSION={summary['schema_version']}")
            print(f"STATE_DB_SUBJECTS={summary['subjects']}")
            print(f"STATE_DB_REVIEWS={summary['reviews']}")
            print(f"STATE_DB_TASK_HEADS={summary['task_heads']}")
        except StateIntegrityError as exc:
            print(f"STATE_DB_STATUS=integrity_error:{exc}")
            print("CAMPAIGN_LEDGER_STATUS=unavailable_state_integrity_error")
        else:
            try:
                from ..core import open_runtime_ledger

                campaign_ledger = open_runtime_ledger(settings, read_only=True)
                campaign_tasks = campaign_ledger.ledger.get("tasks", {})
                campaign_task_count = len(campaign_tasks) if isinstance(campaign_tasks, dict) else 0
                print("CAMPAIGN_LEDGER_STATUS=loaded_read_only")
                print(f"CAMPAIGN_LEDGER_TASKS={campaign_task_count}")
                campaign_loaded = True
            except (OSError, ValueError, LedgerDangerousStateError) as exc:
                print(f"CAMPAIGN_LEDGER_STATUS=unavailable:{type(exc).__name__}")

    legacy_present = settings.project_ledger_file.is_file()
    print(
        "LEGACY_LEDGER_STATUS="
        + ("present_frozen" if legacy_present else "missing_not_created")
    )
    if campaign_loaded:
        print("LEDGER_STATUS=active_sqlite_campaign")
    elif not legacy_present:
        print("LEDGER_STATUS=missing_not_created")
    else:
        print("LEDGER_STATUS=legacy_present_frozen")


async def process_target(args):
    settings = get_settings()
    phase = args.phase
    read_only_batch_plan = phase == 2 and getattr(args, "phase2_mode", "") == "batch-plan"
    if not read_only_batch_plan and getattr(settings, "dependency_decisions_dir", None) is not None:
        settings.dependency_decisions_dir.mkdir(parents=True, exist_ok=True)
    target_path = args.input

    if phase == 0:
        from ..phase0_ingestion_pack import (
            apply_phase0_pack,
            validate_phase0_pack,
            write_phase0_pack,
        )

        if settings.phase0_ingestion_packs_dir is not None:
            settings.phase0_ingestion_packs_dir.mkdir(parents=True, exist_ok=True)
        if args.phase0_mode == "pack":
            pack_dir = write_phase0_pack(Path(target_path), args.page_range, args.phase0_output, settings)
            print(f"📦 Phase 0 ingestion pack generated: {pack_dir}")
        elif args.phase0_mode == "validate":
            success, detail, _report = validate_phase0_pack(args.phase0_output, settings)
            print(("✅ " if success else "❌ ") + detail)
        elif args.phase0_mode == "apply":
            success, detail, target_input = apply_phase0_pack(args.phase0_output, settings)
            print(("✅ " if success else "❌ ") + detail)
            if success:
                print(f"📝 Input written: {target_input}")
        return

    from ..core import open_runtime_ledger

    ledger = (
        open_runtime_ledger(settings, read_only=True)
        if read_only_batch_plan
        else open_runtime_ledger(settings)
    )
    selected_task_ids: set[str] | None = None
    if args.tasks:
        selected_task_ids = set(args.task_ids)

    if phase == 1:
        from ..phase1_prompt_pack import (
            apply_phase1_pack,
            write_phase1_pack,
        )

        settings.plans_dir.mkdir(parents=True, exist_ok=True)
        settings.phase1_prompt_packs_dir.mkdir(parents=True, exist_ok=True)
        phase1_mode = getattr(args, "phase1_mode", "pack")
        if phase1_mode == "pack":
            if os.path.isdir(target_path):
                tex_files = sorted(glob.glob(os.path.join(target_path, "*.tex")))
                for file_path in tex_files:
                    write_phase1_pack(Path(file_path), settings)
            else:
                write_phase1_pack(Path(target_path), settings)
        elif phase1_mode == "apply":
            found_ids = []
            if os.path.isdir(target_path):
                tex_files = sorted(glob.glob(os.path.join(target_path, "*.tex")))
                for file_path in tex_files:
                    success, detail, ids = apply_phase1_pack(Path(file_path), ledger, settings)
                    if success:
                        found_ids.extend(ids)
                        source_plan = os.path.splitext(os.path.basename(file_path))[0]
                        ledger.mark_orphans(ids, source_plan=source_plan)
                    else:
                        print(f"❌ {detail}")
            else:
                success, detail, ids = apply_phase1_pack(Path(target_path), ledger, settings)
                if success:
                    found_ids.extend(ids)
                    source_plan = os.path.splitext(os.path.basename(target_path))[0]
                    ledger.mark_orphans(ids, source_plan=source_plan)
                else:
                    print(f"❌ {detail}")
    elif phase == 2:
        from ..phase2_prompt_pack import (
            build_check_prompt_pack_candidate,
            ensure_task_registered,
            is_remark_task,
            mark_remark_completed_without_pack,
            repair_packed_remark_tasks,
            resolve_phase2_task,
            write_codex_review_pack,
            write_existing_output_review_queue,
            write_existing_output_review_pack,
            write_prompt_pack,
        )
        from ..phase2_batch_runner import plan_batch_from_ledger, render_batch_runner_plan, run_batch_actions
        from ..phase2_dependency_reconcile import (
            DependencyReconciliationError,
            reconcile_phase2_task_dependencies,
        )
        from ..phase2_basis_rebind import (
            AppliedReviewBasisRebindError,
            rebind_phase2_applied_review_basis,
        )
        from ..phase2_dependency_gate import (
            FrozenDependencyAuthorityError,
            accept_frozen_dependency_authority,
            build_frozen_dependency_evidence,
            revoke_frozen_dependency_authority,
        )
        from ..phase2_review_apply import apply_codex_review_result
        from ..phase2_review_loop import (
            run_codex_auto_loop,
            run_codex_review_fix,
            run_codex_review_now,
        )

        if not read_only_batch_plan:
            settings.reports_dir.mkdir(parents=True, exist_ok=True)
            settings.output_lean_files_dir.mkdir(parents=True, exist_ok=True)
            settings.phase2_prompt_packs_dir.mkdir(parents=True, exist_ok=True)
            settings.error_logs_dir.mkdir(parents=True, exist_ok=True)
            settings.formalized_chapters_dir.mkdir(parents=True, exist_ok=True)
            settings.toyapollo_output_dir.mkdir(parents=True, exist_ok=True)
            if args.phase2_mode in {"soft-pack", "soft-apply"}:
                settings.phase2_softdep_packs_dir.mkdir(parents=True, exist_ok=True)
        if not selected_task_ids and args.phase2_mode not in {"batch-plan", "batch-run", "review-existing-queue"}:
            print("❌ Phase 2 modes require task ids via --tasks.")
            return
        if args.phase2_mode in {"pack", "build-check", "review-pack", "review-existing", "review-now", "review-fix", "auto-loop", "review-apply", "dependency-reconcile", "basis-rebind", "frozen-dependency-build-check", "frozen-dependency-accept", "frozen-dependency-revoke"} and len(selected_task_ids) != 1:
            print("❌ This Phase 2 mode currently supports exactly one task at a time.")
            return
        try:
            if args.phase2_mode == "pack":
                task_id = next(iter(selected_task_ids))
                repaired_remarks = repair_packed_remark_tasks(
                    ledger,
                    settings,
                    source_plan_prefixes=("13_", "14_", "15_"),
                    delete_pack_dirs=True,
                )
                if repaired_remarks:
                    print(f"🧹 Repaired packed remark tasks: {', '.join(repaired_remarks)}")

                task = resolve_phase2_task(task_id, ledger, settings)
                task = ensure_task_registered(task, ledger)
                if is_remark_task(task):
                    mark_remark_completed_without_pack(
                        task_id,
                        ledger,
                        settings,
                        delete_pack_dir=True,
                    )
                    print(f"⏭️ Skipped Remark task {task_id}; marked COMPLETED without formalization.")
                else:
                    pack_dir = write_prompt_pack(task_id, ledger, settings, task=task)
                    print(f"📦 Prompt pack generated: {pack_dir}")
            elif args.phase2_mode == "build-check":
                task_id = next(iter(selected_task_ids))
                success, detail = await build_check_prompt_pack_candidate(task_id, ledger, settings, args.candidate)
                if success:
                    print(f"🛠️ Build check passed for {task_id}.")
                else:
                    print(f"❌ Build check failed for {task_id}.")
                print(detail)
            elif args.phase2_mode == "review-pack":
                task_id = next(iter(selected_task_ids))
                success, detail = await write_codex_review_pack(task_id, ledger, settings, args.candidate)
                if success:
                    print(f"📦 Codex semantic review pack generated for {task_id}.")
                else:
                    print(f"❌ Codex semantic review pack generation failed for {task_id}.")
                print(detail)
            elif args.phase2_mode == "review-existing":
                task_id = next(iter(selected_task_ids))
                success, detail = await write_existing_output_review_pack(task_id, ledger, settings)
                if success:
                    print(f"📦 Existing output semantic review pack generated for {task_id}.")
                else:
                    print(f"❌ Existing output semantic review pack generation failed for {task_id}.")
                print(detail)
            elif args.phase2_mode == "review-now":
                task_id = next(iter(selected_task_ids))
                success, detail = await run_codex_review_now(
                    task_id,
                    ledger,
                    settings,
                    review_subject=args.review_subject,
                    auto_apply_pass=args.auto_apply_pass,
                )
                if success:
                    print(f"🧠 Codex review request ready; reviewer step required now for {task_id}.")
                else:
                    print(f"❌ Codex review request could not be prepared for {task_id}.")
                print(detail)
                if not success:
                    raise SystemExit(1)
            elif args.phase2_mode == "review-fix":
                task_id = next(iter(selected_task_ids))
                success, detail = await run_codex_review_fix(
                    task_id,
                    ledger,
                    settings,
                    abandon_current_repair=args.abandon_current_repair,
                )
                if success:
                    print(f"🩹 Review repair loop prepared for {task_id}.")
                else:
                    print(f"❌ Review repair loop could not be prepared for {task_id}.")
                print(detail)
            elif args.phase2_mode == "auto-loop":
                task_id = next(iter(selected_task_ids))
                success, detail = await run_codex_auto_loop(
                    task_id,
                    ledger,
                    settings,
                    review_subject=args.review_subject,
                    max_auto_rounds=args.max_auto_rounds,
                    nonprogress_limit=args.nonprogress_limit,
                    max_build_attempts_per_round=args.max_build_attempts_per_round,
                )
                if success:
                    print(f"🔁 Codex auto-loop advanced for {task_id}; continue this same-session step now.")
                else:
                    print(f"❌ Codex auto-loop stopped for {task_id}.")
                print(detail)
            elif args.phase2_mode == "review-existing-queue":
                queue_task_ids = sorted(selected_task_ids) if selected_task_ids is not None else []
                success, detail = await write_existing_output_review_queue(queue_task_ids, ledger, settings)
                if success:
                    print("📚 Existing output semantic review queue prepared.")
                else:
                    print("❌ Existing output semantic review queue preparation failed.")
                print(detail)
            elif args.phase2_mode == "batch-plan":
                task_ids = sorted(selected_task_ids) if selected_task_ids is not None else sorted(
                    canonicalize_block_id(task_id)
                    for task_id in ledger.ledger.get("tasks", {})
                    if canonicalize_block_id(task_id)
                )
                plan = plan_batch_from_ledger(
                    task_ids,
                    ledger,
                    settings,
                    task_kinds=args.batch_task_kinds,
                    limit=args.batch_limit,
                    worker_slots=args.batch_workers,
                    include_legacy=args.batch_include_legacy,
                )
                print(render_batch_runner_plan(plan), end="")
            elif args.phase2_mode == "batch-run":
                task_ids = sorted(selected_task_ids) if selected_task_ids is not None else sorted(
                    canonicalize_block_id(task_id)
                    for task_id in ledger.ledger.get("tasks", {})
                    if canonicalize_block_id(task_id)
                )
                execution = await run_batch_actions(
                    task_ids,
                    ledger,
                    settings,
                    max_actions=args.batch_max_actions,
                    task_kinds=args.batch_task_kinds,
                    limit=args.batch_limit,
                    worker_slots=args.batch_workers,
                    include_legacy=args.batch_include_legacy,
                )
                print(render_batch_runner_plan(execution.plan), end="")
                print(f"\nExecuted actions: {len(execution.executed)}")
                for action, detail in zip(execution.executed, execution.details):
                    print(f"- {action.task_id}: {action.action}: {detail}")
            elif args.phase2_mode == "review-apply":
                task_id = next(iter(selected_task_ids))
                success, detail = await apply_codex_review_result(task_id, ledger, settings, args.review_result)
                if success:
                    print(f"✅ Codex semantic review applied and clean completion landed for {task_id}.")
                else:
                    print(f"❌ Codex semantic review apply did not promote {task_id}.")
                print(detail)
            elif args.phase2_mode == "dependency-reconcile":
                task_id = next(iter(selected_task_ids))
                try:
                    event = reconcile_phase2_task_dependencies(
                        task_id,
                        ledger,
                        settings,
                        expected_old_dependencies=args.expected_old_dependencies,
                    )
                except DependencyReconciliationError as exc:
                    print(f"❌ Dependency reconciliation refused for {task_id}: {exc}")
                    raise SystemExit(1) from exc
                print(
                    f"✅ Dependencies reconciled for {task_id}: "
                    f"{event['previous_dependencies']} -> {event['reconciled_dependencies']}."
                )
                print(f"AUDIT_RECONCILIATION_ID={event['reconciliation_id']}")
                print(f"AUDIT_SOURCE_FILE={event['source_file']}")
            elif args.phase2_mode == "basis-rebind":
                task_id = next(iter(selected_task_ids))
                try:
                    event = rebind_phase2_applied_review_basis(
                        task_id,
                        ledger,
                        settings,
                        expected_old_basis_hash=args.expected_old_basis,
                        expected_new_basis_hash=args.expected_new_basis,
                        expected_subject_hash=args.expected_subject_hash,
                        expected_dependencies=args.expected_dependencies,
                    )
                except AppliedReviewBasisRebindError as exc:
                    print(f"❌ Applied-review basis rebind refused for {task_id}: {exc}")
                    raise SystemExit(1) from exc
                print(
                    f"✅ Applied-review basis rebound for {task_id}: "
                    f"{event['previous_post_basis_hash']} -> {event['replacement_post_basis_hash']}."
                )
                print(f"AUDIT_REBIND_ID={event['rebind_id']}")
                print(f"AUDIT_RECEIPT_FILE={event['receipt_file']}")
                print(f"AUDIT_RECEIPT_SHA256={event['receipt_sha256']}")
            elif args.phase2_mode == "frozen-dependency-build-check":
                task_id = next(iter(selected_task_ids))
                try:
                    event = build_frozen_dependency_evidence(
                        task_id,
                        ledger,
                        settings,
                    )
                except FrozenDependencyAuthorityError as exc:
                    print(f"❌ Frozen dependency build check failed for {task_id}: {exc}")
                    raise SystemExit(1) from exc
                print(f"✅ Exact frozen dependency build check passed for {task_id}.")
                print(f"BUILD_EVIDENCE_FILE={event['evidence_file']}")
                print(f"BUILD_EVIDENCE_SHA256={event['evidence_sha256']}")
            elif args.phase2_mode == "frozen-dependency-accept":
                task_id = next(iter(selected_task_ids))
                try:
                    event = accept_frozen_dependency_authority(
                        task_id,
                        ledger,
                        settings,
                        owner_scope=args.frozen_owner_scope,
                        owner_decision_token=args.frozen_owner_decision_token,
                        owner_reason=args.frozen_owner_reason,
                        owner_decision_path=args.frozen_owner_decision,
                        expected_primary_hash=args.expected_primary_hash,
                        expected_subject_hash=args.expected_subject_hash,
                        expected_dependencies=args.expected_dependencies,
                        expected_frozen_tip=args.expected_frozen_tip,
                        build_evidence_path=args.frozen_build_evidence,
                    )
                except FrozenDependencyAuthorityError as exc:
                    print(f"❌ Frozen dependency acceptance refused for {task_id}: {exc}")
                    raise SystemExit(1) from exc
                print(
                    f"✅ Frozen owner dependency authority recorded for {task_id}; "
                    "no semantic PASS was claimed."
                )
                print(f"AUDIT_RECEIPT_FILE={event['receipt_file']}")
                print(f"AUDIT_RECEIPT_SHA256={event['receipt_sha256']}")
                print(f"AUDIT_BUILD_EVIDENCE_SHA256={event['build_evidence_sha256']}")
            elif args.phase2_mode == "frozen-dependency-revoke":
                task_id = next(iter(selected_task_ids))
                try:
                    event = revoke_frozen_dependency_authority(
                        task_id,
                        ledger,
                        settings,
                        expected_current_receipt=args.expected_current_frozen_receipt,
                        owner_scope=args.frozen_owner_scope,
                        owner_decision_token=args.frozen_owner_decision_token,
                        owner_reason=args.frozen_owner_reason,
                        owner_decision_path=args.frozen_owner_decision,
                    )
                except FrozenDependencyAuthorityError as exc:
                    print(f"❌ Frozen dependency revoke refused for {task_id}: {exc}")
                    raise SystemExit(1) from exc
                print(f"✅ Frozen dependency authority revoked for {task_id}.")
                print(f"AUDIT_REVOCATION_FILE={event['revocation_file']}")
                print(f"AUDIT_REVOCATION_SHA256={event['revocation_sha256']}")
            elif args.phase2_mode == "soft-pack":
                from ..phase2_softdep_pack import write_softdep_pack

                pack_dir = write_softdep_pack(sorted(selected_task_ids), ledger, settings)
                print(f"📦 Soft dependency pack generated: {pack_dir}")
            elif args.phase2_mode == "soft-apply":
                from ..phase2_softdep_pack import apply_softdep_selection

                success, detail, pack_dir = apply_softdep_selection(sorted(selected_task_ids), ledger, settings, args.selection)
                if success:
                    print(f"✅ Soft imports applied for batch: {pack_dir.name}")
                else:
                    print(f"❌ Soft imports apply failed for batch: {pack_dir.name}")
                print(detail)
        except FileNotFoundError as exc:
            print(f"❌ {exc}")
            return
def main() -> int:
    if len(sys.argv) > 1 and sys.argv[1] in {"status", "worklist", "state", "pr-review"}:
        from ..state_cli import main as state_main

        return state_main(sys.argv[1:], get_settings())
    parser = argparse.ArgumentParser(description="Toy Apollo Ledger-Driven Pipeline")
    parser.add_argument("--phase", type=int, choices=[0, 1, 2], required=False, help="0: Ingest, 1: Plan, 2: Local formalization and Problem soft dependency selection")
    parser.add_argument("--input", type=str, required=False, default="", help="Path for Phase 0 pack and Phase 1 inputs")
    parser.add_argument("--phase0-mode", type=str, choices=PHASE0_MODES, default="pack", dest="phase0_mode", help="Phase 0 mode: pack extracts source materials, validate checks draft_input.tex, apply writes inputs/<stem>.tex")
    parser.add_argument("--page-range", type=str, required=False, default="", dest="page_range", help="Physical PDF page range for --phase 0 --phase0-mode pack, 1-based inclusive, for example 157-160")
    parser.add_argument("--phase0-output", type=str, required=False, default="", dest="phase0_output", help="Output stem for Phase 0 packs and inputs/<stem>.tex, for example chapter9-moments-mgf")
    parser.add_argument("--phase1-mode", type=str, choices=PHASE1_MODES, default="pack", dest="phase1_mode", help="Phase 1 mode: pack generates operator prompt packs, apply validates and registers a filled draft_plan.json")
    parser.add_argument("--tasks", type=str, required=False, default="", help="Comma-separated block_id filter for Phase 2 modes")
    parser.add_argument("--phase2-mode", type=str, choices=PHASE2_MODES, default="pack", help="Phase 2 mode: default workflow is pack -> build-check -> review-now --review-subject candidate -> review-apply. review-apply is the only completion landing gate. batch-plan reports next actions from ledger state; batch-run executes a small number of selected review/auto-loop actions; review-pack/review-existing/review-existing-queue are prepare-only compatibility modes; review-fix repairs failed semantic review; soft-pack and soft-apply handle Problem soft dependency selection; auto-loop advances same-session repair/review state.")
    parser.add_argument("--candidate", type=str, required=False, default="", help="Optional external Lean file for --phase 2 --phase2-mode build-check; review-pack only accepts ToyApollo/Output/<task>.lean as a compatibility alias for review-existing")
    parser.add_argument("--review-result", type=str, required=False, default="", dest="review_result", help="Filled semantic review result JSON for --phase 2 --phase2-mode review-apply")
    parser.add_argument("--expected-old-dependencies", type=str, required=False, default=None, dest="expected_old_dependencies_raw", help="Comma-separated current hard dependencies required as a compare-and-swap precondition for --phase 2 --phase2-mode dependency-reconcile; pass an explicit empty string for an empty list")
    parser.add_argument("--expected-old-basis", type=str, required=False, default=None, dest="expected_old_basis", help="Exact current applied post-basis SHA-256 required by --phase 2 --phase2-mode basis-rebind")
    parser.add_argument("--expected-new-basis", type=str, required=False, default=None, dest="expected_new_basis", help="Exact freshly computed post-basis SHA-256 required by --phase 2 --phase2-mode basis-rebind")
    parser.add_argument("--expected-subject-hash", type=str, required=False, default=None, dest="expected_subject_hash", help="Exact unchanged official review-subject SHA-256 required by --phase 2 --phase2-mode basis-rebind")
    parser.add_argument("--expected-dependencies", type=str, required=False, default=None, dest="expected_dependencies_raw", help="Comma-separated unchanged hard dependencies required by --phase 2 --phase2-mode basis-rebind; pass an explicit empty string for an empty list")
    parser.add_argument("--expected-primary-hash", type=str, required=False, default=None, dest="expected_primary_hash", help="Exact current canonical Toy output SHA-256 required by frozen-dependency-accept")
    parser.add_argument("--frozen-owner-scope", type=str, required=False, default="", dest="frozen_owner_scope", help="Explicit owner scope token required by frozen-dependency-accept")
    parser.add_argument("--frozen-owner-decision-token", type=str, required=False, default="", dest="frozen_owner_decision_token", help="Explicit owner decision token required by frozen-dependency-accept")
    parser.add_argument("--frozen-owner-reason", type=str, required=False, default="", dest="frozen_owner_reason", help="Auditable owner reason required by frozen-dependency-accept")
    parser.add_argument("--frozen-owner-decision", type=str, required=False, default="", dest="frozen_owner_decision", help="Hash-bound owner decision JSON for frozen dependency grant/revoke")
    parser.add_argument("--frozen-build-evidence", type=str, required=False, default="", dest="frozen_build_evidence", help="Mechanical build PASS JSON bound by frozen-dependency-accept; the command never runs Lake")
    parser.add_argument("--expected-frozen-tip", type=str, required=False, default=None, dest="expected_frozen_tip", help="Current frozen receipt CAS for frozen-dependency-accept; pass an explicit empty string for an initial grant")
    parser.add_argument("--expected-current-frozen-receipt", type=str, required=False, default=None, dest="expected_current_frozen_receipt", help="Current frozen receipt CAS required by frozen-dependency-revoke")
    parser.add_argument("--review-subject", type=str, choices=["current", "existing", "candidate"], default="current", dest="review_subject", help="Review subject selector for --phase 2 --phase2-mode review-now/auto-loop")
    parser.add_argument("--auto-apply-pass", action="store_true", dest="auto_apply_pass", help="Agent-side hint for --phase 2 --phase2-mode review-now: after the Codex reviewer writes a pass result, continue with review-apply")
    parser.add_argument("--abandon-current-repair", action="store_true", dest="abandon_current_repair", help="With --phase 2 --phase2-mode review-fix, abandon the active repair cycle without changing draft.lean")
    parser.add_argument("--max-auto-rounds", type=int, default=PHASE2_AUTO_LOOP_REVIEW_ROUNDS, dest="max_auto_rounds", help="Maximum rounds for --phase 2 --phase2-mode auto-loop; default 15")
    parser.add_argument("--nonprogress-limit", type=int, default=PHASE2_AUTO_LOOP_NONPROGRESS_LIMIT, dest="nonprogress_limit", help="Stop --phase 2 --phase2-mode auto-loop after this many consecutive non-progress failures; default 15")
    parser.add_argument("--max-build-attempts-per-round", type=int, default=PHASE2_AUTO_LOOP_BUILD_ATTEMPTS_PER_REVIEW, dest="max_build_attempts_per_round", help="Maximum build-check attempts per round for --phase 2 --phase2-mode auto-loop; default 15")
    parser.add_argument("--batch-max-actions", type=int, default=1, dest="batch_max_actions", help="Maximum executable actions for --phase 2 --phase2-mode batch-run; default 1")
    parser.add_argument("--batch-task-kinds", type=str, default="", dest="batch_task_kinds_raw", help="Comma-separated task kinds for batch-plan/batch-run, for example theorem,definition")
    parser.add_argument("--batch-limit", type=int, default=0, dest="batch_limit", help="Maximum tasks to show or dispatch from batch-plan/batch-run after dependency-aware ranking; 0 means no limit")
    parser.add_argument("--batch-workers", type=int, default=0, dest="batch_workers", help="Worker slots to annotate in batch-plan/batch-run output; 0 means no worker assignment")
    parser.add_argument("--batch-include-legacy", action="store_true", dest="batch_include_legacy", help="Show quarantined legacy obligation/audit rows in batch-plan/batch-run; default hides them from the ordinary queue")
    parser.add_argument("--selection", type=str, required=False, default="", help="Selection JSON for --phase 2 --phase2-mode soft-apply")
    parser.add_argument("--status", action="store_true", help="Show process-local resolved roots and a read-only project status summary")

    args = parser.parse_args()
    if args.status:
        if any(token != "--status" for token in sys.argv[1:]):
            parser.error("--status is strictly read-only and must be used alone.")
        print_read_only_status(get_settings())
        return 0

    args.task_ids = parse_task_ids(args.tasks)
    args.batch_task_kinds = parse_batch_task_kinds(args.batch_task_kinds_raw)
    args.expected_old_dependencies = []
    args.expected_dependencies = []
    if args.tasks and not args.task_ids:
        parser.error("--tasks was provided but no valid task id was parsed.")
    if args.phase == 0:
        if args.tasks:
            parser.error("--tasks is not supported for Phase 0.")
        if not args.phase0_output:
            parser.error("--phase0-output is required with --phase 0.")
        if args.phase0_mode == "pack":
            if not args.input:
                parser.error("--input is required with --phase 0 --phase0-mode pack.")
            if not args.page_range:
                parser.error("--page-range is required with --phase 0 --phase0-mode pack.")
        elif args.input:
            parser.error("--input is only used with --phase 0 --phase0-mode pack.")
        if args.page_range and args.phase0_mode != "pack":
            parser.error("--page-range is only used with --phase 0 --phase0-mode pack.")
    if args.task_ids and args.phase == 1:
        parser.error("--tasks is not supported for Phase 1.")
    if args.phase == 2 and args.phase2_mode in PHASE2_MODES and not args.task_ids:
        if args.phase2_mode not in {"batch-plan", "batch-run", "review-existing-queue"}:
            parser.error("--phase 2 modes require task ids via --tasks.")
    if args.phase == 2 and args.phase2_mode in PHASE2_SINGLE_TASK_MODES and len(args.task_ids) > 1:
        parser.error("This --phase 2 mode supports exactly one task at a time.")
    if args.phase == 2 and args.phase2_mode == "dependency-reconcile":
        if args.expected_old_dependencies_raw is None:
            parser.error("--expected-old-dependencies is required with --phase 2 --phase2-mode dependency-reconcile.")
        try:
            args.expected_old_dependencies = parse_expected_old_dependencies(args.expected_old_dependencies_raw)
        except ValueError as exc:
            parser.error(f"--expected-old-dependencies {exc}")
    elif args.expected_old_dependencies_raw is not None:
        parser.error("--expected-old-dependencies is only supported with --phase 2 --phase2-mode dependency-reconcile.")
    basis_rebind_values = (
        args.expected_old_basis,
        args.expected_new_basis,
    )
    frozen_owner_values = (
        args.frozen_owner_scope,
        args.frozen_owner_decision_token,
        args.frozen_owner_reason,
        args.frozen_owner_decision,
    )
    if args.phase == 2 and args.phase2_mode == "basis-rebind":
        if (
            args.expected_primary_hash is not None
            or any(frozen_owner_values)
            or args.frozen_build_evidence
            or args.expected_frozen_tip is not None
            or args.expected_current_frozen_receipt is not None
        ):
            parser.error("Dependency-authority arguments are not supported with basis-rebind.")
        if any(value is None for value in basis_rebind_values) or args.expected_subject_hash is None or args.expected_dependencies_raw is None:
            parser.error(
                "--expected-old-basis, --expected-new-basis, --expected-subject-hash, and "
                "--expected-dependencies are required with --phase 2 --phase2-mode basis-rebind."
            )
        try:
            args.expected_dependencies = parse_expected_old_dependencies(args.expected_dependencies_raw)
        except ValueError as exc:
            parser.error(f"--expected-dependencies {exc}")
    elif args.phase == 2 and args.phase2_mode == "frozen-dependency-accept":
        if any(value is not None for value in basis_rebind_values):
            parser.error("Basis-rebind arguments are not supported with frozen-dependency-accept.")
        required_nonempty = (
            args.expected_primary_hash,
            args.expected_subject_hash,
            *frozen_owner_values,
            args.frozen_build_evidence,
        )
        if any(value is None or not str(value).strip() for value in required_nonempty):
            parser.error(
                "--expected-primary-hash, --expected-subject-hash, --expected-dependencies, "
                "--expected-frozen-tip, --frozen-owner-scope, --frozen-owner-decision-token, "
                "--frozen-owner-reason, --frozen-owner-decision, and --frozen-build-evidence "
                "are required with frozen-dependency-accept."
            )
        if args.expected_dependencies_raw is None or args.expected_frozen_tip is None:
            parser.error(
                "--expected-dependencies and --expected-frozen-tip are required with "
                "frozen-dependency-accept; either may be passed as an explicit empty string."
            )
        if args.expected_current_frozen_receipt is not None:
            parser.error("--expected-current-frozen-receipt is only used by frozen-dependency-revoke.")
        try:
            args.expected_dependencies = parse_expected_old_dependencies(args.expected_dependencies_raw)
        except ValueError as exc:
            parser.error(f"--expected-dependencies {exc}")
    elif args.phase == 2 and args.phase2_mode == "frozen-dependency-revoke":
        if (
            any(value is not None for value in basis_rebind_values)
            or args.expected_primary_hash is not None
            or args.expected_subject_hash is not None
            or args.expected_dependencies_raw is not None
            or args.frozen_build_evidence
            or args.expected_frozen_tip is not None
        ):
            parser.error("Grant/build/basis arguments are not supported with frozen-dependency-revoke.")
        if (
            any(not str(value or "").strip() for value in frozen_owner_values)
            or not str(args.expected_current_frozen_receipt or "").strip()
        ):
            parser.error(
                "--expected-current-frozen-receipt and all frozen owner decision fields "
                "are required with frozen-dependency-revoke."
            )
    elif (
        any(value is not None for value in basis_rebind_values)
        or args.expected_subject_hash is not None
        or args.expected_dependencies_raw is not None
        or args.expected_primary_hash is not None
        or any(frozen_owner_values)
        or args.frozen_build_evidence
        or args.expected_frozen_tip is not None
        or args.expected_current_frozen_receipt is not None
    ):
        parser.error(
            "Dependency-authority/basis compare-and-swap arguments are only "
            "supported with their matching Phase 2 mode."
        )
    if args.phase == 2 and args.phase2_mode in PHASE2_SOFT_MODES:
        invalid = [task_id for task_id in args.task_ids if not task_id.startswith("prob_")]
        if invalid:
            parser.error(f"--phase 2 --phase2-mode {args.phase2_mode} only supports problem tasks: {', '.join(invalid)}")
    if args.phase == 2 and args.phase2_mode == "auto-loop":
        if args.max_auto_rounds < PHASE2_AUTO_LOOP_REVIEW_ROUNDS:
            parser.error("--max-auto-rounds cannot be below the hard-coded Phase 2 repair budget of 15.")
        if args.nonprogress_limit < PHASE2_AUTO_LOOP_NONPROGRESS_LIMIT:
            parser.error("--nonprogress-limit cannot be below the hard-coded Phase 2 repair budget of 15.")
        if args.max_build_attempts_per_round < PHASE2_AUTO_LOOP_BUILD_ATTEMPTS_PER_REVIEW:
            parser.error("--max-build-attempts-per-round cannot be below the hard-coded Phase 2 repair budget of 15.")
    if args.phase == 2 and args.input:
        parser.error("--input is not used with --phase 2.")
    if args.candidate and not (args.phase == 2 and args.phase2_mode in ("build-check", "review-pack")):
        parser.error("--candidate is only supported with --phase 2 --phase2-mode build-check/review-pack.")
    if args.phase == 2 and args.phase2_mode == "review-apply" and not args.review_result:
        parser.error("--review-result is required with --phase 2 --phase2-mode review-apply.")
    if args.review_result and not (args.phase == 2 and args.phase2_mode == "review-apply"):
        parser.error("--review-result is only supported with --phase 2 --phase2-mode review-apply.")
    if args.review_subject != "current" and not (args.phase == 2 and args.phase2_mode in ("review-now", "auto-loop")):
        parser.error("--review-subject is only supported with --phase 2 --phase2-mode review-now/auto-loop.")
    if args.auto_apply_pass and not (args.phase == 2 and args.phase2_mode == "review-now"):
        parser.error("--auto-apply-pass is only supported with --phase 2 --phase2-mode review-now.")
    if args.abandon_current_repair and not (args.phase == 2 and args.phase2_mode == "review-fix"):
        parser.error("--abandon-current-repair is only supported with --phase 2 --phase2-mode review-fix.")
    if (
        args.phase2_mode != "auto-loop"
        and (
            args.max_auto_rounds != PHASE2_AUTO_LOOP_REVIEW_ROUNDS
            or args.nonprogress_limit != PHASE2_AUTO_LOOP_NONPROGRESS_LIMIT
            or args.max_build_attempts_per_round != PHASE2_AUTO_LOOP_BUILD_ATTEMPTS_PER_REVIEW
        )
    ):
        parser.error("--max-auto-rounds/--nonprogress-limit/--max-build-attempts-per-round are only supported with --phase 2 --phase2-mode auto-loop.")
    if args.phase == 2 and args.phase2_mode == "batch-run" and args.batch_max_actions < 1:
        parser.error("--batch-max-actions must be at least 1.")
    if args.phase2_mode != "batch-run" and args.batch_max_actions != 1:
        parser.error("--batch-max-actions is only supported with --phase 2 --phase2-mode batch-run.")
    if args.phase == 2 and args.phase2_mode in {"batch-plan", "batch-run"}:
        if args.batch_task_kinds_raw and not args.batch_task_kinds:
            parser.error("--batch-task-kinds must contain at least one known kind.")
        if args.batch_limit < 0:
            parser.error("--batch-limit must be non-negative.")
        if args.batch_workers < 0:
            parser.error("--batch-workers must be non-negative.")
    elif args.batch_task_kinds_raw or args.batch_limit or args.batch_workers or args.batch_include_legacy:
        parser.error("--batch-task-kinds/--batch-limit/--batch-workers/--batch-include-legacy are only supported with --phase 2 --phase2-mode batch-plan/batch-run.")
    if args.phase == 2 and args.phase2_mode == "soft-apply" and not args.selection:
        parser.error("--selection is required with --phase 2 --phase2-mode soft-apply.")
    if args.selection and not (args.phase == 2 and args.phase2_mode == "soft-apply"):
        parser.error("--selection is only supported with --phase 2 --phase2-mode soft-apply.")
    if args.phase is None:
        parser.print_help()
        return 0

    asyncio.run(process_target(args))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
