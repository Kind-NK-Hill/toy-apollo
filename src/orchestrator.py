import os
import time
import datetime
import json
import asyncio
import subprocess
import glob
import re
from src.pipeline import AutoFormalizationPipeline
from src.context_manager import ContextManager
from src.architect import ProofArchitect
from src.ledger_manager import LedgerManager, TaskStatus

class TextbookOrchestrator:
    def __init__(self, report_filename="orchestrator_report.md", max_depth=2, output_dir="output_lean_files", error_logs_dir="error_logs", ledger=None):
        self.base_output_dir = output_dir
        self.base_error_dir = error_logs_dir
        self.context_mgr = ContextManager(output_dir=self.base_output_dir)
        self.pipeline = AutoFormalizationPipeline(error_logs_dir=error_logs_dir, context_mgr=self.context_mgr)
        self.architect = ProofArchitect()
        self.max_depth = max_depth 
        self.unsolved_tasks = []
        self.stats = {"success": 0, "failed": 0, "skipped": 0, "decomposed": 0, "main_success": 0, "main_failed": 0, "main_skipped": 0, "main_decomposed": 0, "start_time": None, "end_time": None}
        self.report_file = report_filename
        self.ledger = ledger or LedgerManager()
        self._init_report()

    def _init_report(self):
        report_dir = os.path.dirname(self.report_file)
        if report_dir: os.makedirs(report_dir, exist_ok=True)
        with open(self.report_file, "w", encoding="utf-8") as f:
            f.write("# 📚 Auto-Formalization Orchestrator Report\n\n")
            f.write(f"**Date Started:** {datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n")
            f.write("## Execution Log\n\n| Task ID | Type | Title | Status | Time Taken |\n| :--- | :--- | :--- | :--- | :--- |\n")

    def _log_task_to_report(self, task_id, task_type, title, status, duration):
        icon = {"Success": "✅ Pass", "Cached": "📦 Cached", "Failed": "❌ Fail", "Decomposed": "🔄 Decomp"}.get(status, "⏭️ Skip")
        with open(self.report_file, "a", encoding="utf-8") as f:
            f.write(f"| `{task_id}` | {task_type} | {title} | {icon} | {duration:.1f}s |\n")

    def _finalize_report(self):
        total_time = self.stats["end_time"] - self.stats["start_time"]
        def rate(s, t): return (s/t)*100 if t > 0 else 0
        tot = self.stats["success"] + self.stats["failed"] + self.stats["skipped"] + self.stats["decomposed"]
        main = self.stats["main_success"] + self.stats["main_failed"] + self.stats["main_skipped"] + self.stats["main_decomposed"]
        with open(self.report_file, "a", encoding="utf-8") as f:
            f.write(f"\n## 📊 Summary\n- Total: {tot} (Rate: {rate(self.stats['success'], tot):.1f}%)\n")
            f.write(f"- Main: {main} (Rate: {rate(self.stats['main_success'], main):.1f}%)\n")

    async def _check_cache(self, task, target_dir, task_queue):
        block_id = task['block_id']
        
        # [LEDGER INTEGRATION]
        # If ledger says it's COMPLETED, we check the physical file and its hash
        task_record = self.ledger.ledger["tasks"].get(block_id)
        cache_file = os.path.join(target_dir, f"{block_id}.lean")
        
        if task_record and task_record["status"] == TaskStatus.COMPLETED.value:
            if os.path.exists(cache_file):
                current_hash = self.ledger.reconcile_file(block_id, cache_file)
                if current_hash == task_record["output_hash"]:
                    print(f"   💎 [Ledger] {block_id} is verified and unchanged. Skipping.")
                    with open(cache_file, "r", encoding="utf-8") as f: return f.read()
                elif task_record["status"] == TaskStatus.USER_MODIFIED.value:
                    print(f"   ⚠️ [Ledger] {block_id} has been manualy modified. Keeping user version.")
                    with open(cache_file, "r", encoding="utf-8") as f: return f.read()

        # Fallback to old cache logic if ledger is missing or mismatch
        if not os.path.exists(cache_file): return None
        try:
            with open(cache_file, "r", encoding="utf-8") as f: cached_code = f.read()
            if not cached_code.strip(): return None 
        except: return None
        
        all_blocks = {t['block_id']: t for t in task_queue}
        deps = self.context_mgr._get_transitive_dependencies(block_id, all_blocks)
        
        is_renowned = task.get("is_renowned", False)
        if is_renowned:
            self.pipeline.compiler.write_file(cached_code)
            success, _ = await self.pipeline.compiler.build_async()
            return cached_code if success else None

        missing = [d for d in deps if f"import ToyApollo.Output.{d}" not in cached_code]
        if missing and [d for d in missing if d in self.context_mgr.code_store]:
            retrofitted = await self.pipeline.retrofit_code(block_id, cached_code, [d for d in missing if d in self.context_mgr.code_store], task['content'])
            if retrofitted != cached_code:
                with open(cache_file, "w", encoding="utf-8") as f: f.write(retrofitted)
                return retrofitted
        
        self.pipeline.compiler.write_file(cached_code)
        success, _ = await self.pipeline.compiler.build_async()
        return cached_code if success else None

    async def process_task_queue(self, task_queue):
        self.stats["start_time"] = time.time()
        final_doc = ""
        for task in task_queue:
            if 'depth' not in task: task['depth'] = 0
            if 'root_task' not in task: task['root_task'] = task 
            self.ledger.add_or_update_task(task) # Ensure task is in ledger

        i = 0
        while i < len(task_queue):
            task = task_queue[i]
            task_start_time = time.time()
            block_id, task_type, title, content, depth, root_task = task['block_id'], task['type'], task['title'], task['content'], task['depth'], task['root_task']
            source_plan = task.get('source_plan', 'general')
            folder = source_plan.split('/')[-1].split('\\')[-1]
            out_dir = self.base_output_dir if folder in self.base_output_dir else os.path.join(self.base_output_dir, folder)
            err_dir = self.base_error_dir if folder in self.base_error_dir else os.path.join(self.base_error_dir, folder)
            os.makedirs(out_dir, exist_ok=True); os.makedirs(err_dir, exist_ok=True)
            self.pipeline.error_logs_dir = err_dir

            print(f"\n▶️ Task {i+1}/{len(task_queue)}: [{task_type}] {title} ({block_id})")

            if task_type == "Remark":
                final_doc += f"\n/- Remark: {title}\n{content}\n-/\n"
                self._log_task_to_report(block_id, task_type, title, "Skipped", 0); i += 1; continue

            cached = await self._check_cache(task, out_dir, task_queue)
            if cached:
                # Update ledger if not already set
                current_hash = self.ledger._hash_text(cached)
                self.ledger.register_success(block_id, cached, current_hash)
                
                self.context_mgr.add_success(block_id, cached)
                toy_out = os.path.join("ToyApollo", "Output")
                os.makedirs(toy_out, exist_ok=True)
                with open(os.path.join(toy_out, f"{block_id}.lean"), "w", encoding="utf-8") as f: f.write(cached)
                self.stats["success"] += 1
                if depth == 0: self.stats["main_success"] += 1
                final_doc += f"\n-- Block: {title}\n{cached}\n"
                self._log_task_to_report(block_id, task_type, title, "Cached", time.time()-task_start_time)
                i += 1; continue
            
            # Start actual fixing
            self.ledger.update_status(block_id, TaskStatus.LOCAL_FIXING)
            
            existing_sub = glob.glob(os.path.join(out_dir, f"{block_id}_lemma_*.lean"))
            if existing_sub and depth == 0:
                print(f"   🔄 [Decomp-Aware] Found {len(existing_sub)} sub-lemmas. Skipping parent task '{block_id}'.")
                self.stats["decomposed"] += 1
                if depth == 0: self.stats["main_decomposed"] += 1
                self._log_task_to_report(block_id, task_type, title, "Decomposed", time.time()-task_start_time)
                i += 1; continue
                
            all_blocks = {t['block_id']: t for t in task_queue}
            deps = self.context_mgr._get_transitive_dependencies(block_id, all_blocks)
            im_block, hy_block = "-- [DEPENDENCY INSTRUCTIONS]\n", ""
            for dep_id in deps:
                if dep_id in self.context_mgr.code_store: im_block += f"import ToyApollo.Output.{dep_id}\n"
                elif dep_id in self.context_mgr.failed_statements:
                    hy_block += f"\n-- Hypothesis from {dep_id}:\n{self.context_mgr.failed_statements[dep_id]}\n"
            self.pipeline.agent.inject_context(f"{im_block}\n{hy_block}\n\nReference:\n{self.context_mgr.get_context_for(task, task_queue)}")
            
            prmpt = f"Formalize: {content}"
            if task_type == "Definition": prmpt = f"Translate to Lean 4: {content}"
            elif task_type == "Theorem_Statement": prmpt = f"Map to Mathlib: {content}"
            
            kws = ["tsum", "algebra", "measure", "indicator", "pairwise"]
            if (any(kw in content.lower() for kw in kws) or len(content) > 800) and depth < self.max_depth:
                sub_tasks = self.architect.generate_plan(content, parent_block_id=block_id)
                if sub_tasks:
                    for st in sub_tasks: 
                        st['depth'], st['root_task'], st['source_plan'] = depth+1, root_task, source_plan
                        if "{parent_block_id}" in st['block_id']: st['block_id'] = st['block_id'].replace("{parent_block_id}", block_id)
                        else:
                            suffix_match = re.search(r'(lemma_\d+|main|step_\d+)', st['block_id'])
                            suffix = suffix_match.group(1) if suffix_match else st['block_id'].split('_')[-1]
                            st['block_id'] = f"{block_id}_{suffix}"
                        if 'title' in st: st['title'] = st['title'].replace("{parent_block_id}", block_id)
                        if 'dependencies' in st:
                            new_deps = []
                            for d in st['dependencies']:
                                d_clean = d.replace("{parent_block_id}", block_id)
                                if not d_clean.startswith(block_id) and any(s['block_id'].endswith(d_clean) for s in sub_tasks):
                                    d_clean = f"{block_id}_{d_clean.split('_')[-1]}"
                                new_deps.append(d_clean)
                            st['dependencies'] = new_deps
                    task_queue[i+1:i+1] = sub_tasks
                    self.stats["decomposed"] += 1
                    if depth == 0: self.stats["main_decomposed"] += 1
                    self._log_task_to_report(block_id, task_type, title, "Decomposed", time.time()-task_start_time)
                    i += 1; continue
                else:
                    print(f"   ❌ [Architect Failure] Aborting '{block_id}'.")
                    result_code = None
            else:
                result_code, _, _ = await self.pipeline.run_phase(f"Task: {title}", prmpt, f"Solve: {title}", block_id)
            
            if result_code:
                is_comp, repl_res = await self.pipeline.validate_with_repl_async(result_code)
                
                if is_comp and (isinstance(repl_res, dict) and not repl_res.get('sorries')):
                    self.stats["success"] += 1
                    if depth == 0: self.stats["main_success"] += 1
                    
                    # [LEDGER REGISTRATION]
                    current_hash = self.ledger._hash_text(result_code)
                    self.ledger.register_success(block_id, result_code, current_hash)
                    
                    self.context_mgr.add_success(block_id, result_code)
                    toy_out = os.path.join("ToyApollo", "Output")
                    os.makedirs(toy_out, exist_ok=True)
                    for p in [os.path.join(toy_out, f"{block_id}.lean"), os.path.join(out_dir, f"{block_id}.lean")]:
                        with open(p, "w", encoding="utf-8") as f: f.write(result_code)
                    
                    print(f"   ⚙️ Compiling ToyApollo.Output.{block_id}...")
                    subprocess.run(f"lake build ToyApollo.Output.{block_id}", shell=True)
                    final_doc += f"\n-- Block: {title}\n{result_code}\n"
                    self._log_task_to_report(block_id, task_type, title, "Success", time.time()-task_start_time)
                else:
                    print(f"   ❌ [Integration Failure] Task '{block_id}' failed.")
                    self.stats["failed"] += 1
                    if depth == 0: self.stats["main_failed"] += 1
                    
                    # [LEDGER FAILURE]
                    err_msg = str(repl_res) if not is_comp else "Contains sorries"
                    self.ledger.update_status(block_id, TaskStatus.FAILED_LOCAL, error=err_msg)
                    
                    sorry_stub = f"import Mathlib\n\ntheorem {block_id} : sorry := by sorry"
                    toy_out = os.path.join("ToyApollo", "Output")
                    os.makedirs(toy_out, exist_ok=True)
                    with open(os.path.join(toy_out, f"{block_id}.lean"), "w", encoding="utf-8") as f: f.write(sorry_stub)
                    with open(os.path.join(out_dir, f"{block_id}.lean"), "w", encoding="utf-8") as f: f.write(sorry_stub)
                    
                    self.context_mgr.add_failed_statement(block_id, result_code if result_code else "sorry")
                    self._log_task_to_report(block_id, task_type, title, "Failed", time.time()-task_start_time)
                    if root_task not in self.unsolved_tasks: self.unsolved_tasks.append(root_task)
            else:
                self.stats["failed"] += 1
                if depth == 0: self.stats["main_failed"] += 1
                self.ledger.update_status(block_id, TaskStatus.FAILED_LOCAL, error="No code produced")
                
                sorry_stub = f"import Mathlib\n\ntheorem {block_id} : sorry := by sorry"
                for p in [os.path.join("ToyApollo", "Output", f"{block_id}.lean"), os.path.join(out_dir, f"{block_id}.lean")]:
                    with open(p, "w", encoding="utf-8") as f: f.write(sorry_stub)
                
                self._log_task_to_report(block_id, task_type, title, "Failed", time.time()-task_start_time)
                if root_task not in self.unsolved_tasks: self.unsolved_tasks.append(root_task)
            i += 1 

        self.stats["end_time"] = time.time(); self._finalize_report()
        self.ledger.save()
        return final_doc
