import os
import glob
import json
import asyncio
import argparse
import shutil
import re
from pathlib import Path
from src.textbook_parser import TextbookParser
from src.orchestrator import TextbookOrchestrator
from src.architect import ProofArchitect
from src.aristotle_offloader import AristotleDirectOffloader
from src.aristotle_phase3 import AristotlePhase3Manager
from src.pipeline import AutoFormalizationPipeline
from src.ledger_manager import LedgerManager, TaskStatus

def get_task_content(task_id: str) -> str:
    """Finds the original LaTeX content for the task in plans."""
    for plan_file in Path("plans").glob("*.json"):
        try:
            with open(plan_file, "r", encoding="utf-8") as f:
                tasks = json.load(f)
                for t in tasks:
                    if t.get('block_id') == task_id:
                        return t.get('content', "No content found.")
        except:
            continue
    return "Task statement not found."

def step1_generate_plan(input_file, current_idx, total_files, ledger: LedgerManager):
    """阶段 1：读取指定的 .tex 文件并生成计划"""
    print(f"🚀 [Phase 1] Generating plan for File {current_idx}/{total_files}: '{os.path.basename(input_file)}'...")
    
    if not os.path.exists(input_file):
        print(f"❌ Input file '{input_file}' not found.")
        return []

    with open(input_file, "r", encoding="utf-8") as f:
        latex_source = f.read()

    base_name = os.path.splitext(os.path.basename(input_file))[0]
    os.makedirs("plans", exist_ok=True)
    plan_file = os.path.join("plans", f"{base_name}_plan.json")

    parser = TextbookParser()
    task_queue = parser.parse_chapter(latex_source)
    
    if not task_queue:
        print(f"❌ Failed to parse textbook: {input_file}")
        return []

    for task in task_queue:
        task['source_plan'] = base_name
        ledger.add_or_update_task(task) # [LEDGER] Register task

    with open(plan_file, "w", encoding="utf-8") as f:
        json.dump(task_queue, f, indent=4, ensure_ascii=False)
        
    print(f"✅ Plan successfully saved to '{plan_file}'.")
    return [t['block_id'] for t in task_queue]

async def step2_execute_plan(plan_file, current_idx, total_files, ledger: LedgerManager):
    """阶段 2：读取指定的 .json 计划并执行"""
    print(f"🚀 [Phase 2] Executing Plan {current_idx}/{total_files}: '{os.path.basename(plan_file)}'...")
    
    if not os.path.exists(plan_file):
        print(f"❌ Plan file '{plan_file}' not found.")
        return
        
    with open(plan_file, "r", encoding="utf-8") as f:
        task_queue = json.load(f)
        
    base_name = os.path.splitext(os.path.basename(plan_file))[0].replace("_plan", "")
    os.makedirs("reports", exist_ok=True)
    report_name = os.path.join("reports", f"{base_name}_report.md")
    
    orchestrator = TextbookOrchestrator(
        report_filename=report_name, 
        output_dir="output_lean_files",
        error_logs_dir="error_logs",
        max_depth=2,
        ledger=ledger # [LEDGER] Pass to orchestrator
    )
    
    final_document = await orchestrator.process_task_queue(task_queue)
    
    if final_document:
        os.makedirs("formalized_chapters", exist_ok=True)
        output_file = os.path.join("formalized_chapters", f"{base_name}_Formalized.lean")
        with open(output_file, "w", encoding="utf-8") as f:
            f.write(final_document)
        print(f"\n🎉 Finished processing {base_name}! Document saved to {output_file}")

async def step3_aristotle_offload(ledger: LedgerManager):
    """阶段 3：Aristotle 云端卸载 (针对账本中失败的任务)"""
    # [LEDGER] Query tasks that failed locally
    failed_tasks = ledger.get_tasks_by_status([TaskStatus.FAILED_LOCAL])
    
    if not failed_tasks:
        print("✅ No tasks marked as FAILED_LOCAL in ledger. Nothing to offload.")
        return

    print(f"🚀 [Phase 3] Initiating Aristotle Offload for {len(failed_tasks)} tasks...")
    offloader = AristotleDirectOffloader()
    manager = AristotlePhase3Manager()
    
    for task in failed_tasks:
        tid = task['block_id']
        print(f"\n📦 Offloading: {tid}")
        
        # 1. 打包
        await offloader.prepare_package(tid)
        staging_dir = offloader.outbox_root / tid
        
        # 2. 提交
        if staging_dir.exists():
            ledger.update_status(tid, TaskStatus.OFFLOADED) # [LEDGER] Update status
            success = await manager.run_offload(tid, str(staging_dir))
            if success:
                print(f"   ✅ Task {tid} successfully solved and harvested.")
                ledger.update_status(tid, TaskStatus.HARVESTED) # [LEDGER] Success
            else:
                print(f"   ❌ Task {tid} failed in Aristotle cloud.")
                ledger.update_status(tid, TaskStatus.FAILED_LOCAL, error="Aristotle Cloud Failure")
        else:
            print(f"   ⚠️ Staging directory not found for {tid}.")

async def step4_align_results(ledger: LedgerManager):
    """阶段 4：结果对齐与本地集成 (针对已收割任务)"""
    harvested_tasks = ledger.get_tasks_by_status([TaskStatus.HARVESTED, TaskStatus.ALIGNING])
    
    if not harvested_tasks:
        print("✅ No tasks in HARVESTED state to align.")
        return

    print(f"🚀 [Phase 4] Aligning {len(harvested_tasks)} Aristotle results...")
    pipeline = AutoFormalizationPipeline(error_logs_dir="error_logs/alignment")
    
    for task in harvested_tasks:
        tid = task['block_id']
        ledger.update_status(tid, TaskStatus.ALIGNING)
        
        local_path = Path("ToyApollo/Output") / f"{tid}.lean"
        if not local_path.exists():
            local_path = Path("output_lean_files/general") / f"{tid}.lean"
            
        if local_path.exists():
            print(f"\n🔧 Aligning {tid}...")
            with open(local_path, "r", encoding="utf-8") as f:
                raw_code = f.read()
            
            task_content = get_task_content(tid)
            fixed_code = await pipeline.align_aristotle_result(tid, raw_code, task_content)
            
            with open(local_path, "w", encoding="utf-8") as f: f.write(fixed_code)
            toy_path = Path("ToyApollo/Output") / f"{tid}.lean"
            if str(local_path) != str(toy_path): shutil.copy(local_path, toy_path)
            
            print(f"   ⚙️ Final verification for {tid}...")
            module_name = f"ToyApollo.Output.{tid}"
            proc = subprocess.run(f"lake build {module_name}", shell=True, capture_output=True, text=True)
            if proc.returncode == 0:
                print(f"   ✨ {tid} is now COMPLETED.")
                ledger.register_success(tid, fixed_code, ledger._hash_text(fixed_code))
            else:
                print(f"   ⚠️ {tid} still has compilation errors.")
                ledger.update_status(tid, TaskStatus.ALIGNING, error=proc.stderr)
        else:
            print(f"   ❓ Local file for {tid} not found.")

import subprocess

async def process_target(args):
    ledger = LedgerManager()
    phase = args.phase
    target_path = args.input

    if phase == 1:
        found_ids = []
        if os.path.isdir(target_path):
            tex_files = sorted(glob.glob(os.path.join(target_path, "*.tex")))
            for idx, file_path in enumerate(tex_files, 1):
                found_ids.extend(step1_generate_plan(file_path, idx, len(tex_files), ledger))
        else:
            found_ids.extend(step1_generate_plan(target_path, 1, 1, ledger))
        ledger.mark_orphans(found_ids) # [LEDGER] Mark removed tasks
        
    elif phase == 2:
        if os.path.isdir(target_path):
            json_files = sorted(glob.glob(os.path.join(target_path, "*.json")))
            for idx, file_path in enumerate(json_files, 1):
                await step2_execute_plan(file_path, idx, len(json_files), ledger)
        else:
            await step2_execute_plan(target_path, 1, 1, ledger)
            
    elif phase == 3:
        await step3_aristotle_offload(ledger)
        
    elif phase == 4:
        await step4_align_results(ledger)
        
    elif args.status:
        ledger.print_status_summary()

    ledger.save()

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Toy Apollo Ledger-Driven Pipeline")
    parser.add_argument('--phase', type=int, choices=[1, 2, 3, 4], required=False, 
                        help="1: Plan, 2: Local, 3: Aristotle, 4: Align")
    parser.add_argument('--input', type=str, required=False, default="", help="Path for Phase 1 & 2")
    parser.add_argument('--status', action='store_true', help="Show project status summary")
    
    args = parser.parse_args()
    if not args.phase and not args.status:
        parser.print_help()
    else:
        asyncio.run(process_target(args))
