import os
import asyncio
import re
import json
import difflib
from src.agent import GeminiAgent
from src.compiler import LeanCompiler
from src.searcher import MathlibSearcher
from src.reflection import ReflectionManager
from src.config import *

class AutoFormalizationPipeline:
    def __init__(self, error_logs_dir="error_logs", context_mgr=None):
        self.agent = GeminiAgent()
        self.compiler = LeanCompiler()
        self.searcher = MathlibSearcher(MATHLIB_PATH, GOOGLE_API_KEY)
        self.reflection_mgr = ReflectionManager()
        self.context_mgr = context_mgr
        self.error_logs_dir = error_logs_dir
        os.makedirs(self.error_logs_dir, exist_ok=True)

    def log_error(self, task_id, phase, attempt, error_msg, code=None):
        log_file = os.path.join(self.error_logs_dir, f"{task_id}_error.log")
        with open(log_file, "a", encoding="utf-8") as f:
            f.write(f"--- [{phase}] Attempt {attempt} ---\n")
            if code: f.write(f"[CODE]:\n{code}\n{'-'*20}\n")
            f.write(f"[ERROR]:\n{error_msg}\n\n")

    def _sanitize_code(self, raw_code):
        if not raw_code: return ""
        clean = re.sub(r"```json\s*", "", raw_code)
        clean = re.sub(r"```lean\s*", "", clean)
        clean = re.sub(r"```\s*", "", clean)
        if clean.strip().startswith("{") and "code" in clean:
            try: return json.loads(clean)["code"].strip()
            except: pass
        if "--- ANALYSIS END ---" in clean: clean = clean.split("--- ANALYSIS END ---")[1]
        return clean.strip()

    async def validate_with_repl_async(self, code: str):
        """Returns (success, result_dict_or_error_msg)"""
        return await self.compiler.validate_with_repl_async(code)

    async def align_aristotle_result(self, task_id, raw_code, task_description):
        """
        [PHASE 4] Aligns Aristotle's result with local environment using a Build-Fix loop.
        """
        print(f"   🔧 [Phase 4] Aligning Aristotle result for {task_id}...")
        current_code = self._sanitize_code(raw_code)
        
        for attempt in range(1, 6):
            print(f"      [Align] Attempt {attempt}...", end="", flush=True)
            success, repl_res = await self.validate_with_repl_async(current_code)
            
            # Handle different return types from validate_with_repl_async
            is_complete = False
            error_msg = ""
            
            if isinstance(repl_res, dict):
                is_complete = success and not repl_res.get('sorries')
                error_msg = "\n".join(repl_res.get('errors', []))
            else:
                # If it's a string, it's likely an error message
                is_complete = success
                error_msg = str(repl_res)
            
            if is_complete:
                print(" ✅ SUCCESS"); return current_code
            
            if not error_msg:
                error_msg = "Result contains 'sorry' placeholders."
            
            print(" ❌ FAIL")
            
            adaptation_prompt = f"""
            You are a Lean 4 Version Adapter. Your task is to fix local compilation errors in this Aristotle-generated proof.
            
            [CRITICAL]: DO NOT change the proof logic or strategy. Aristotle's logic is verified. 
            ONLY fix imports, resolve naming conflicts with Mathlib, and update syntax for the current Mathlib version.
            
            [TASK]: {task_description}
            [ERRORS]: {error_msg}
            [CODE]:
            {current_code}
            """
            
            response = await self.agent.generate_one_off_async(adaptation_prompt, temperature=0.0)
            if not response: break
            current_code = self._sanitize_code(response)
            
        return current_code

    async def retrofit_code(self, task_id, legacy_code, required_imports, task_description):
        """
        [NEW] Robust Retrofitting: Upgrades legacy code with reference context and retries.
        """
        print(f"   🔧 [Retrofit] Upgrading legacy code for {task_id} (up to 5 attempts)...")
        reference_context = ""
        for dep in required_imports:
            if dep in self.context_mgr.code_store:
                reference_context += f"\n--- Reference Content for {dep} ---\n{self.context_mgr.code_store[dep]}\n"

        import_stmt = "\n".join([f"import ToyApollo.Output.{dep}" for dep in required_imports])
        current_feedback = f"TASK: Inject imports and remove redundancy.\nREQUIRED IMPORTS:\n{import_stmt}\nREFERENCE:\n{reference_context}\nORIGINAL:\n{legacy_code}\nCRITICAL: DO NOT remove open/universe statements."

        for attempt in range(1, 6):
            print(f"      [Retrofit] Attempt {attempt}...", end="", flush=True)
            refactored = await self.agent.generate_one_off_async(current_feedback, temperature=0.0)
            if not refactored: break
            clean = self._sanitize_code(refactored)
            success, msg = await self.validate_with_repl_async(clean)
            if success:
                print(" ✅ SUCCESS"); return clean
            else:
                print(" ❌ FAIL")
                current_feedback = f"Refactoring failed: {msg}\nFix while keeping imports.\nCODE:\n{clean}"
        
        print(f"   ⚠️ [Retrofit] All 5 attempts failed for {task_id}. Reverting to original.")
        return legacy_code

    async def run_phase(self, phase_name, initial_prompt, task_description, task_id="unknown_task", domain=None):
        print(f"\n🚀 Starting {phase_name}...")
        self.agent.reset_history()
        
        tq = self.agent.generate_technical_queries("No error yet.", task_description)
        results = await self.searcher.verify_candidates(self.searcher.search(tq, task_description), self.compiler)
        self.agent.inject_context(self.searcher.format_rag_context(results))

        lessons = self.reflection_mgr.get_lessons_prompt(task_id)
        if lessons: initial_prompt = lessons + "\n" + initial_prompt

        code = await self.agent.generate_async(initial_prompt)
        last_error, last_code, stuck_counter = "", "", 0
        loop = asyncio.get_running_loop()

        try:
            for i in range(1, MAX_FAST_RETRIES + 1):
                print(f"   [Guided] Attempt {i}...", end="", flush=True)
                clean = self._sanitize_code(code)
                self.compiler.write_file(clean)
                
                repl_res = await loop.run_in_executor(None, self.compiler.get_repl().validate_code, clean)
                
                if repl_res['success'] and not repl_res['sorries']:
                    print(" ✅ PASS"); return clean, None, clean
                
                if not repl_res['success']:
                    print(" ❌ FAIL (REPL Error)")
                    output = "[REPL ERROR]:\n" + "\n".join(repl_res['errors'])
                else:
                    print(" ❌ FAIL (Incomplete: Contains sorry)")
                    output = "[LOGIC ERROR]: The proof is syntactically correct but contains 'sorry' placeholders. You MUST provide a complete proof without any 'sorry'."

                self.log_error(task_id, phase_name, i, output, clean)
                
                norm_err = re.sub(r'Line \d+, Col \d+:', '', output)[:100].strip()
                sim = difflib.SequenceMatcher(None, clean, last_code).ratio() if last_code else 0
                if norm_err == re.sub(r'Line \d+, Col \d+:', '', last_error)[:100].strip() and sim > 0.8:
                    stuck_counter += 1
                    if stuck_counter >= 3:
                        print(f"   💡 [Strategy Shift] Stuck. Broadening search...")
                        new_tq = self.agent.generate_technical_queries(output, f"Alternative for {task_description}")
                        new_res = await self.searcher.verify_candidates(self.searcher.search(new_tq, "Alternative"), self.compiler)
                        self.agent.inject_context(self.searcher.format_rag_context(new_res))
                    if stuck_counter >= 5: break
                else: stuck_counter = 0
                
                last_error, last_code = output, clean
                feedback = f"Your last attempt failed with the following error:\n{output}\n\nPlease fix the error and provide the complete Lean 4 code. No sorry."
                await asyncio.sleep(15)
                code = await self.agent.generate_async(feedback)

            print(f"   ⚠️ Rescue mode...")
            code = await self.agent.generate_async("Rewrite from scratch. No sorry.")
            for i in range(1, MAX_DEEP_RETRIES + 1):
                print(f"   [Rescue] Attempt {i}...", end="", flush=True)
                clean = self._sanitize_code(code)
                self.compiler.write_file(clean)
                
                success, out = await self.compiler.build_async()
                repl_res = await loop.run_in_executor(None, self.compiler.get_repl().validate_code, clean)
                
                if success and repl_res['success']: 
                    print(" ✅ PASS"); return clean, None, clean
                
                print(" ❌ FAIL")
                err_msg = out if not success else "Incomplete proof (contains sorry)"
                await asyncio.sleep(15)
                code = await self.agent.generate_async(f"Fix this error: {err_msg}")
                
            return None, "FAILED", clean
        finally:
            self.compiler.delete_validation_file()
