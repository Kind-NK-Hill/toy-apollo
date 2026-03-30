import os
import re
import shutil
import asyncio
from pathlib import Path
from typing import Set
from src.config import PROJECT_ROOT
from src.agent import GeminiAgent

class AristotleBridge:
    def __init__(self, staging_root="plans/aristotle_staging"):
        self.staging_root = Path(staging_root)
        self.agent = GeminiAgent()
        
    def get_library_catalog(self) -> str:
        """[NEW] Scans ToyApollo/Output to build a semantic catalog for the LLM."""
        catalog = []
        output_path = Path("ToyApollo/Output")
        if not output_path.exists(): return "No local library found."
        
        for lean_file in output_path.glob("*.lean"):
            block_id = lean_file.stem
            try:
                with open(lean_file, "r", encoding="utf-8") as f:
                    content = f.read()
                    # Extract the first doc-string or comment as summary
                    doc_match = re.search(r"\/--\s*(.*?)\*\/", content, re.DOTALL)
                    summary = doc_match.group(1).strip() if doc_match else "No description available."
                    # Keep only the first 2 lines of summary for brevity
                    summary = "\n".join(summary.split("\n")[:2])
                    catalog.append(f"- {block_id}: {summary}")
            except:
                continue
        return "\n".join(catalog)

    async def select_local_imports(self, task_content: str, task_id: str) -> list:
        """[NEW] Uses LLM mathematical skill to select which local files to import."""
        catalog = self.get_library_catalog()
        prompt = f"""
        You are a Lean 4 Mathematical Architect. Your task is to decide which LOCAL theorems or definitions 
        should be imported to solve the given [TASK]. 

        [LOCAL LIBRARY CATALOG]:
        {catalog}

        [TASK TO SOLVE]:
        {task_content}

        [INSTRUCTIONS]:
        1. Think like a mathematician: 
           - If it's a THEOREM, what DEFINITIONS are needed to state it?
           - If it's a PROBLEM, what prior THEOREMS are needed as tools?
        2. Select only the MOST ESSENTIAL block_ids from the catalog.
        3. Do NOT import the task itself ({task_id}).
        4. Output ONLY a comma-separated list of block_ids. If none are needed, output 'NONE'.
        """
        response = await self.agent.generate_async(prompt)
        cleaned = response.strip().upper()
        if "NONE" in cleaned or not cleaned: return []
        # Extract block_ids using regex to be safe
        ids = re.findall(r"(\w+_\d+_\d+|\w+_\d+)", response)
        return list(set(ids))

    def get_local_imports(self, content: str) -> Set[str]:
        """Finds all 'import ToyApollo.Output.xxx' statements."""
        return set(re.findall(r"import\s+ToyApollo\.Output\.(\w+)", content))

    def trace_local_dependencies(self, start_file: Path, found_files: Set[Path] = None) -> Set[Path]:
        """Recursively traces local imports under ToyApollo.Output."""
        if found_files is None: found_files = set()
        if not start_file.exists(): return found_files

        try:
            with open(start_file, "r", encoding="utf-8") as f:
                content = f.read()
        except Exception as e:
            print(f"   ⚠️ Error reading {start_file}: {e}")
            return found_files

        local_mods = self.get_local_imports(content)
        for mod in local_mods:
            # Check multiple potential locations
            search_paths = [
                Path("ToyApollo/Output") / f"{mod}.lean",
                Path("output_lean_files/general") / f"{mod}.lean"
            ]
            # Recursively check chapters if needed
            chapter_dirs = [d for d in Path("output_lean_files").iterdir() if d.is_dir()]
            for d in chapter_dirs:
                search_paths.append(d / f"{mod}.lean")

            for dep_path in search_paths:
                if dep_path.exists() and dep_path not in found_files:
                    found_files.add(dep_path)
                    self.trace_local_dependencies(dep_path, found_files)
                    break
        
        return found_files

    async def generate_sorry_stub(self, task_id: str, task_content: str) -> str:
        """Generates a syntax-perfect Lean 4 skeleton with 'sorry'."""
        prompt = f"""
        Extract the Lean 4 theorem signature for the following task and provide a syntax-perfect skeleton with 'sorry'.
        Include all necessary imports based on the description.
        
        [TASK]: {task_content}
        [THEOREM NAME]: {task_id}
        
        [REQUIREMENTS]:
        - NO natural language.
        - Theorem proof MUST be 'sorry'.
        - Use standard Mathlib 4 imports.
        """
        code = await self.agent.generate_async(prompt)
        # Surgical cleaning
        clean = re.sub(r"```lean|```", "", code).strip()
        # Ensure the theorem name matches exactly
        if f"theorem {task_id}" not in clean and f"lemma {task_id}" not in clean:
             # Fallback: find the first theorem/lemma and rename it
             clean = re.sub(r"(theorem|lemma)\s+\w+", f"\\1 {task_id}", clean)
        return clean

    def create_staging_area(self, task_id: str, main_code: str, dependencies: Set[Path], original_latex: str, hint: str):
        """Assembles a v4.28.0 compatible Lean project for Aristotle."""
        task_dir = self.staging_root / task_id
        output_dir = task_dir / "ToyApollo" / "Output"
        os.makedirs(output_dir, exist_ok=True)

        # 1. Environment: Pin to v4.28.0 as per research
        with open(task_dir / "lean-toolchain", "w") as f:
            f.write("leanprover/lean4:v4.28.0")
            
        with open(task_dir / "lakefile.toml", "w") as f:
            f.write('name = "aristotle_staging"\n\n')
            f.write('[[require]]\nname = "mathlib"\n')
            f.write('git = "https://github.com/leanprover-community/mathlib4.git"\n')
            f.write('rev = "v4.28.0"\n')

        # 2. Files: Copy recursive dependencies
        for dep in dependencies:
            target = task_dir / "ToyApollo" / "Output" / dep.name
            shutil.copy(dep, target)

        # 3. Hybrid Mode: Inject PROBLEM and PROVIDED SOLUTION tags
        hybrid_content = f"""/--
PROBLEM
{original_latex}

PROVIDED SOLUTION
{hint}
-/
{main_code}
"""
        with open(output_dir / f"{task_id}.lean", "w", encoding="utf-8") as f:
            f.write(hybrid_content)

        print(f"   ✨ Staging area ready: {task_dir} ({len(dependencies)} dependencies copied)")
        return task_dir
