import os
import json
import time
import subprocess
import uuid
from typing import Dict, Any, Optional, List, Tuple
from pathlib import Path
from src.config import PROJECT_ROOT

DEFAULT_REPL_TIMEOUT_SECONDS = 300

class LeanREPL:
    """
    Windows-compatible Lean 4 REPL interface.
    Uses file redirection (oneshot mode) to avoid hanging pipes.
    """
    def __init__(self, project_dir: str = PROJECT_ROOT):
        self.project_dir = Path(project_dir).resolve()
        self.temp_dir = self.project_dir / ".repl_tmp"
        self.temp_dir.mkdir(exist_ok=True)
        self.timeout_seconds = self._load_timeout_seconds()

    @staticmethod
    def _load_timeout_seconds() -> int:
        raw = os.getenv("TOY_APOLLO_REPL_TIMEOUT_SECONDS", "").strip()
        if not raw:
            return DEFAULT_REPL_TIMEOUT_SECONDS
        try:
            timeout = int(raw)
        except ValueError:
            return DEFAULT_REPL_TIMEOUT_SECONDS
        return timeout if timeout > 0 else DEFAULT_REPL_TIMEOUT_SECONDS

    def _cleanup_process_tree(self, process: subprocess.Popen[str]) -> str:
        if os.name == "nt":
            result = subprocess.run(
                ["taskkill", "/T", "/F", "/PID", str(process.pid)],
                capture_output=True,
                text=True,
                timeout=30,
            )
            if result.returncode == 0:
                return "terminated process tree via taskkill."
            cleanup_detail = (result.stderr or result.stdout or "").strip()
            if cleanup_detail:
                return f"taskkill reported exit code {result.returncode}: {cleanup_detail}"
            return f"taskkill reported exit code {result.returncode}."

        process.kill()
        return "terminated process via kill()."

    def _run_oneshot(self, query: Dict[str, Any]) -> Dict[str, Any]:
        """Runs a single REPL query via file redirection."""
        query_id = str(uuid.uuid4())[:8]
        input_filename = f"repl_input_{query_id}.json"
        input_file = self.project_dir / input_filename
        
        with open(input_file, "w", encoding="utf-8") as f:
            json.dump(query, f)
            
        stdout = ""
        stderr = ""
        try:
            # Command: lake exe repl < input.json
            # IMPORTANT: Must run from project root so lake can find lakefile.toml
            command = ["lake", "exe", "repl"]
            input_handle = open(input_file, "r", encoding="utf-8")
            try:
                process = subprocess.Popen(
                    command,
                    stdin=input_handle,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                    cwd=str(self.project_dir),
                )
            finally:
                input_handle.close()

            try:
                stdout, stderr = process.communicate(timeout=self.timeout_seconds)
            except subprocess.TimeoutExpired:
                cleanup_detail = self._cleanup_process_tree(process)
                try:
                    stdout, stderr = process.communicate(timeout=10)
                except subprocess.TimeoutExpired:
                    process.kill()
                    stdout, stderr = process.communicate()
                    cleanup_detail = cleanup_detail.rstrip(".") + "; forced final process kill()."
                return {
                    "error": (
                        f"Command '{' '.join(command)}' timed out after {self.timeout_seconds} seconds; "
                        f"cleanup: {cleanup_detail}"
                    ),
                    "stdout": stdout,
                    "stderr": stderr,
                }

            if stdout:
                # REPL may output multiple JSON objects if there are multiple commands
                # We take the last one or combine them. 
                # For a single "cmd" query, it should be one object.
                try:
                    return json.loads(stdout)
                except json.JSONDecodeError:
                    # Fallback: maybe multiple JSONs?
                    lines = stdout.strip().split('\n')
                    return json.loads(lines[-1])
            else:
                return {"error": "REPL produced no output", "stderr": stderr}
        except json.JSONDecodeError:
            return {"error": "Failed to parse REPL output", "raw": stdout}
        except Exception as e:
            return {"error": str(e)}
        finally:
            if input_file.exists():
                input_file.unlink()

    def validate_code(self, code: str) -> Dict[str, Any]:
        """
        Validates code by sending it to REPL and checking for messages/sorries.
        Returns a dictionary with:
        - 'success': bool
        - 'errors': List[str]
        - 'sorries': List[Dict]
        - 'messages': List[Dict]
        """
        query = {"cmd": code}
        response = self._run_oneshot(query)
        
        if "error" in response:
            return {
                "success": False,
                "errors": [f"REPL System Error: {response['error']}"],
                "sorries": [],
                "messages": []
            }

        errors = []
        messages = response.get("messages", [])
        sorries = response.get("sorries", [])

        # Extract explicit error messages
        for msg in messages:
            if msg.get("severity") == "error":
                pos = msg.get('pos', {})
                errors.append(f"Line {pos.get('line')}, Col {pos.get('column')}: {msg.get('data')}")
        
        # Incomplete proofs are treated as failure in our pipeline
        for s in sorries:
            pos = s.get('pos', {})
            errors.append(f"Incomplete proof (sorry) at Line {pos.get('line')}, Col {pos.get('column')}")
            
        return {
            "success": len(errors) == 0,
            "errors": errors,
            "sorries": sorries,
            "messages": messages
        }

    def run_command(self, code: str) -> Dict[str, Any]:
        """Runs an arbitrary REPL command and returns the raw response payload."""
        return self._run_oneshot({"cmd": code})

class LeanCompiler:
    """
    Updated Compiler that uses both 'lake build' and REPL feedback.
    Isolated Validation: Uses a temporary file in ToyApollo/Output to avoid poisoning the main project.
    """
    def __init__(self, root_dir=PROJECT_ROOT):
        self.root_dir = root_dir
        # Physical Isolation: Write to a specific submodule instead of the root ToyApollo.lean
        self.validation_dir = os.path.join(self.root_dir, "ToyApollo", "Output")
        self.validation_file = os.path.join(self.validation_dir, "Temp_Validation.lean")
        self.validation_target = "ToyApollo.Output.Temp_Validation"
        
        # Legacy support/compatibility (can be removed later if ToyApollo.lean is no longer needed)
        self.target_file = os.path.join(self.root_dir, "ToyApollo.lean")
        
        self._repl = LeanREPL(self.root_dir)
        os.makedirs(self.validation_dir, exist_ok=True)

    def get_repl(self) -> LeanREPL:
        return self._repl

    def run_repl_command(self, code: str) -> Dict[str, Any]:
        return self._repl.run_command(code)

    def reset_workspace(self):
        """Removes temporary validation file and legacy target file."""
        for f in [self.validation_file, self.target_file]:
            if os.path.exists(f):
                try:
                    os.remove(f)
                except Exception as e:
                    print(f"   ⚠️ [Compiler] Failed to delete {f}: {e}")

    def delete_validation_file(self):
        """Cleans up the isolated validation file."""
        if os.path.exists(self.validation_file):
            try:
                os.remove(self.validation_file)
            except: pass

    def write_file(self, content: str):
        """Writes content to the isolated validation file."""
        # Ensure directory exists
        os.makedirs(self.validation_dir, exist_ok=True)
        with open(self.validation_file, "w", encoding="utf-8") as f:
            f.write(content)

    def build(self) -> Tuple[bool, str]:
        """
        Perform targeted lake build on the validation module.
        This ensures we only check the current task and its dependencies.
        """
        result = subprocess.run(
            ["lake", "build", self.validation_target], 
            capture_output=True, 
            text=True, 
            cwd=self.root_dir 
        )
        full_output = (result.stdout or "") + "\n" + (result.stderr or "")
        return result.returncode == 0, full_output

    async def build_async(self) -> Tuple[bool, str]:
        import asyncio
        loop = asyncio.get_event_loop()
        success, output = await loop.run_in_executor(None, self.build)
        return success, output

    async def validate_with_repl_async(self, code: str) -> Tuple[bool, str]:
        """New method to perform deep validation via REPL."""
        import asyncio
        loop = asyncio.get_event_loop()
        result = await loop.run_in_executor(None, self._repl.validate_code, code)
        
        if result['success']:
            return True, "Code is valid and complete."
        else:
            # Return actual error messages joined by newlines
            error_msg = "\n".join(result['errors'])
            return False, error_msg

    def build_module(self, module_name: str) -> Tuple[bool, str]:
        result = subprocess.run(
            ["lake", "build", module_name],
            capture_output=True,
            text=True,
            cwd=self.root_dir
        )
        full_output = (result.stdout or "") + "\n" + (result.stderr or "")
        return result.returncode == 0, full_output

    async def build_module_async(self, module_name: str) -> Tuple[bool, str]:
        import asyncio
        loop = asyncio.get_event_loop()
        return await loop.run_in_executor(None, self.build_module, module_name)
