import argparse
import asyncio
import glob
import json
import os
import shutil
import subprocess
from pathlib import Path

from ..core import LedgerManager, TaskStatus, get_settings
from ..integrations import AristotleDirectOffloader, AristotlePhase3Manager
from ..pipeline import (
    AutoFormalizationPipeline,
    TextbookOrchestrator,
    TextbookParser,
)


def get_task_content(task_id: str, plans_dir: Path) -> str:
    for plan_file in plans_dir.glob("*.json"):
        try:
            with open(plan_file, "r", encoding="utf-8") as f:
                tasks = json.load(f)
            for task in tasks:
                if task.get("block_id") == task_id:
                    return task.get("content", "No content found.")
        except Exception:
            continue
    return "Task statement not found."


def step1_generate_plan(input_file, current_idx, total_files, ledger: LedgerManager, plans_dir: Path):
    print(f"🚀 [Phase 1] Generating plan for File {current_idx}/{total_files}: '{os.path.basename(input_file)}'...")
    if not os.path.exists(input_file):
        print(f"❌ Input file '{input_file}' not found.")
        return []

    with open(input_file, "r", encoding="utf-8") as f:
        latex_source = f.read()

    base_name = os.path.splitext(os.path.basename(input_file))[0]
    plans_dir.mkdir(parents=True, exist_ok=True)
    plan_file = plans_dir / f"{base_name}_plan.json"

    parser = TextbookParser()
    task_queue = parser.parse_chapter(latex_source)
    if not task_queue:
        print(f"❌ Failed to parse textbook: {input_file}")
        return []

    for task in task_queue:
        task["source_plan"] = base_name
        ledger.add_or_update_task(task)

    with open(plan_file, "w", encoding="utf-8") as f:
        json.dump(task_queue, f, indent=4, ensure_ascii=False)

    print(f"✅ Plan successfully saved to '{plan_file}'.")
    return [task["block_id"] for task in task_queue]


async def step2_execute_plan(plan_file, current_idx, total_files, ledger: LedgerManager, reports_dir: Path, output_dir: Path, error_logs_dir: Path, formalized_dir: Path):
    print(f"🚀 [Phase 2] Executing Plan {current_idx}/{total_files}: '{os.path.basename(plan_file)}'...")
    if not os.path.exists(plan_file):
        print(f"❌ Plan file '{plan_file}' not found.")
        return

    with open(plan_file, "r", encoding="utf-8") as f:
        task_queue = json.load(f)

    base_name = os.path.splitext(os.path.basename(plan_file))[0].replace("_plan", "")
    reports_dir.mkdir(parents=True, exist_ok=True)
    report_name = reports_dir / f"{base_name}_report.md"

    orchestrator = TextbookOrchestrator(
        report_filename=str(report_name),
        output_dir=str(output_dir),
        error_logs_dir=str(error_logs_dir),
        max_depth=2,
        ledger=ledger,
    )

    final_document = await orchestrator.process_task_queue(task_queue)
    if final_document:
        formalized_dir.mkdir(parents=True, exist_ok=True)
        output_file = formalized_dir / f"{base_name}_Formalized.lean"
        with open(output_file, "w", encoding="utf-8") as f:
            f.write(final_document)
        print(f"\n🎉 Finished processing {base_name}! Document saved to {output_file}")


async def step3_aristotle_offload(ledger: LedgerManager):
    failed_tasks = ledger.get_tasks_by_status([TaskStatus.FAILED_LOCAL])
    if not failed_tasks:
        print("✅ No tasks marked as FAILED_LOCAL in ledger. Nothing to offload.")
        return

    print(f"🚀 [Phase 3] Initiating Aristotle Offload for {len(failed_tasks)} tasks...")
    offloader = AristotleDirectOffloader()
    manager = AristotlePhase3Manager()

    for task in failed_tasks:
        task_id = task["block_id"]
        print(f"\n📦 Offloading: {task_id}")
        await offloader.prepare_package(task_id)
        staging_dir = offloader.outbox_root / task_id
        if staging_dir.exists():
            ledger.update_status(task_id, TaskStatus.OFFLOADED)
            success = await manager.run_offload(task_id, str(staging_dir))
            if success:
                print(f"   ✅ Task {task_id} successfully solved and harvested.")
                ledger.update_status(task_id, TaskStatus.HARVESTED)
            else:
                print(f"   ❌ Task {task_id} failed in Aristotle cloud.")
                ledger.update_status(task_id, TaskStatus.FAILED_LOCAL, error="Aristotle Cloud Failure")
        else:
            print(f"   ⚠️ Staging directory not found for {task_id}.")


async def step4_align_results(ledger: LedgerManager, error_logs_dir: Path, output_dir: Path, toyapollo_output: Path, plans_dir: Path):
    harvested_tasks = ledger.get_tasks_by_status([TaskStatus.HARVESTED, TaskStatus.ALIGNING])
    if not harvested_tasks:
        print("✅ No tasks in HARVESTED state to align.")
        return

    print(f"🚀 [Phase 4] Aligning {len(harvested_tasks)} Aristotle results...")
    alignment_logs = error_logs_dir / "alignment"
    pipeline = AutoFormalizationPipeline(error_logs_dir=str(alignment_logs))

    for task in harvested_tasks:
        task_id = task["block_id"]
        ledger.update_status(task_id, TaskStatus.ALIGNING)

        local_path = toyapollo_output / f"{task_id}.lean"
        if not local_path.exists():
            local_path = output_dir / "general" / f"{task_id}.lean"

        if local_path.exists():
            print(f"\n🔧 Aligning {task_id}...")
            with open(local_path, "r", encoding="utf-8") as f:
                raw_code = f.read()

            task_content = get_task_content(task_id, plans_dir=plans_dir)
            fixed_code = await pipeline.align_aristotle_result(task_id, raw_code, task_content)

            with open(local_path, "w", encoding="utf-8") as f:
                f.write(fixed_code)

            toy_path = toyapollo_output / f"{task_id}.lean"
            toy_path.parent.mkdir(parents=True, exist_ok=True)
            if str(local_path) != str(toy_path):
                shutil.copy(local_path, toy_path)

            print(f"   ⚙️ Final verification for {task_id}...")
            module_name = f"ToyApollo.Output.{task_id}"
            proc = subprocess.run(f"lake build {module_name}", shell=True, capture_output=True, text=True)
            if proc.returncode == 0:
                print(f"   ✨ {task_id} is now COMPLETED.")
                ledger.register_success(task_id, fixed_code, ledger._hash_text(fixed_code))
            else:
                print(f"   ⚠️ {task_id} still has compilation errors.")
                ledger.update_status(task_id, TaskStatus.ALIGNING, error=proc.stderr)
        else:
            print(f"   ❓ Local file for {task_id} not found.")


async def process_target(args):
    settings = get_settings()
    settings.project_ledger_file.parent.mkdir(parents=True, exist_ok=True)

    ledger = LedgerManager(ledger_path=str(settings.project_ledger_file))
    phase = args.phase
    target_path = args.input

    if phase == 1:
        settings.plans_dir.mkdir(parents=True, exist_ok=True)
        found_ids = []
        if os.path.isdir(target_path):
            tex_files = sorted(glob.glob(os.path.join(target_path, "*.tex")))
            for idx, file_path in enumerate(tex_files, 1):
                found_ids.extend(
                    step1_generate_plan(file_path, idx, len(tex_files), ledger, plans_dir=settings.plans_dir)
                )
        else:
            found_ids.extend(step1_generate_plan(target_path, 1, 1, ledger, plans_dir=settings.plans_dir))
        ledger.mark_orphans(found_ids)
    elif phase == 2:
        settings.reports_dir.mkdir(parents=True, exist_ok=True)
        settings.output_lean_files_dir.mkdir(parents=True, exist_ok=True)
        settings.error_logs_dir.mkdir(parents=True, exist_ok=True)
        settings.formalized_chapters_dir.mkdir(parents=True, exist_ok=True)
        settings.toyapollo_output_dir.mkdir(parents=True, exist_ok=True)
        if os.path.isdir(target_path):
            json_files = sorted(glob.glob(os.path.join(target_path, "*.json")))
            for idx, file_path in enumerate(json_files, 1):
                await step2_execute_plan(
                    file_path,
                    idx,
                    len(json_files),
                    ledger,
                    reports_dir=settings.reports_dir,
                    output_dir=settings.output_lean_files_dir,
                    error_logs_dir=settings.error_logs_dir,
                    formalized_dir=settings.formalized_chapters_dir,
                )
        else:
            await step2_execute_plan(
                target_path,
                1,
                1,
                ledger,
                reports_dir=settings.reports_dir,
                output_dir=settings.output_lean_files_dir,
                error_logs_dir=settings.error_logs_dir,
                formalized_dir=settings.formalized_chapters_dir,
            )
    elif phase == 3:
        await step3_aristotle_offload(ledger)
    elif phase == 4:
        settings.error_logs_dir.mkdir(parents=True, exist_ok=True)
        settings.output_lean_files_dir.mkdir(parents=True, exist_ok=True)
        settings.toyapollo_output_dir.mkdir(parents=True, exist_ok=True)
        await step4_align_results(
            ledger,
            error_logs_dir=settings.error_logs_dir,
            output_dir=settings.output_lean_files_dir,
            toyapollo_output=settings.toyapollo_output_dir,
            plans_dir=settings.plans_dir,
        )
    elif args.status:
        ledger.print_status_summary()

    ledger.save()


def main() -> int:
    parser = argparse.ArgumentParser(description="Toy Apollo Ledger-Driven Pipeline")
    parser.add_argument("--phase", type=int, choices=[1, 2, 3, 4], required=False, help="1: Plan, 2: Local, 3: Aristotle, 4: Align")
    parser.add_argument("--input", type=str, required=False, default="", help="Path for Phase 1 & 2")
    parser.add_argument("--status", action="store_true", help="Show project status summary")

    args = parser.parse_args()
    if not args.phase and not args.status:
        parser.print_help()
        return 0
    asyncio.run(process_target(args))
    return 0
