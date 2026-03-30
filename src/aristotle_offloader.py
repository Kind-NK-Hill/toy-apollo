import os
import json
import shutil
import time
import re
import asyncio
import argparse
from pathlib import Path
from src.aristotle_bridge import AristotleBridge

class AristotleDirectOffloader:
    def __init__(self):
        self.bridge = AristotleBridge()
        self.timestamp = int(time.time())
        self.outbox_root = Path("aristotle_outbox") / f"direct_{self.timestamp}"

    def get_full_dependency_closure(self, initial_deps):
        """[CORE] 递归寻找整个本地依赖链条"""
        closure = set()
        queue = list(initial_deps)
        
        while queue:
            dep_id = queue.pop(0)
            if dep_id in closure: continue
            
            # 查找物理文件
            found_path = None
            search_locations = [
                Path("ToyApollo/Output") / f"{dep_id}.lean",
                Path("output_lean_files/general") / f"{dep_id}.lean"
            ]
            # 搜索章节目录
            if Path("output_lean_files").exists():
                for d in Path("output_lean_files").iterdir():
                    if d.is_dir(): search_locations.append(d / f"{dep_id}.lean")

            for loc in search_locations:
                if loc.exists():
                    found_path = loc
                    break
            
            if found_path:
                closure.add(found_path)
                # 读取文件内容，寻找下一层依赖
                with open(found_path, "r", encoding="utf-8") as f:
                    content = f.read()
                    sub_deps = re.findall(r"import\s+ToyApollo\.Output\.(\w+)", content)
                    for sd in sub_deps:
                        if sd not in closure:
                            queue.append(sd)
            else:
                print(f"   ⚠️ Warning: Could not find physical file for dependency: {dep_id}")
        
        return closure

    def _get_all_preceding_local_files(self):
        """扫描整个本地产物库，提取所有 Definition 和 Theorem 供 Problem 使用"""
        all_local = set()
        search_roots = [Path("output_lean_files"), Path("ToyApollo/Output")]
        
        for root in search_roots:
            if not root.exists(): continue
            for lean_file in root.rglob("*.lean"):
                if re.match(r"(def|thm|ex|lemma)_", lean_file.name.lower()):
                    all_local.add(lean_file)
        return all_local

    async def prepare_package(self, task_id, unsolved_file="plans/unsolved_tasks.json"):
        with open(unsolved_file, "r", encoding="utf-8") as f:
            tasks = json.load(f)
        
        task = next((t for t in tasks if t['block_id'] == task_id), None)
        if not task:
            print(f"❌ Task {task_id} not found in unsolved_tasks.json")
            return

        print(f"🚀 [Direct-Offload] Packaging {task_id} with Mathematical Architect...")

        # 1. 组装 Staging 目录结构
        staging_dir = self.outbox_root / task_id
        output_dir = staging_dir / "ToyApollo" / "Output"
        os.makedirs(output_dir, exist_ok=True)

        # 2. 架构决策：挑选必要的本地依赖
        print(f"   🧠 [Architect] Deciding which local files to import...")
        selected_ids = await self.bridge.select_local_imports(task['content'], task_id)
        print(f"   ✅ Selected local imports: {selected_ids}")

        # 3. 递归寻找整个本地依赖链条
        closure_files = self.get_full_dependency_closure(selected_ids)
        
        # [NEW] 如果是 Problem，且决策结果较少，尝试补充背景
        if task['type'] == "Problem" and len(closure_files) < 3:
            print(f"   📘 Task is a Problem but few deps selected. Injecting core defs...")
            codebase_files = self._get_all_preceding_local_files()
            core_defs = [f for f in codebase_files if "def_" in f.name.lower()]
            closure_files.update(core_defs)
        
        print(f"   🔗 Total of {len(closure_files)} local files in the project mirror.")

        # 4. 复制闭包文件
        unique_files = {f.name: f for f in closure_files}
        for f_name, f_path in unique_files.items():
            shutil.copy(f_path, output_dir / f_name)

        # 5. 生成干净的主文件签名
        print(f"   🧠 Extracting clean theorem signature...")
        
        # 物理注入：生成手动 import 块
        importable_stems = [sid for sid in selected_ids if any(f.stem == sid for f in closure_files)]
        # 补充：如果有 def_xxx 在 closure 中但没被 explicit selected，也 import 它们以防万一
        for f in closure_files:
            if "def_" in f.name.lower() and f.stem not in importable_stems:
                importable_stems.append(f.stem)
        
        local_import_lines = "\n".join([f"import ToyApollo.Output.{stem}" for stem in importable_stems if stem != task_id])

        signature_prompt = f"""
        Extract the Lean 4 theorem signature for the following task.

        [TASK]: {task['content']}
        [THEOREM NAME]: {task_id}

        [INSTRUCTIONS]:
        1. Only output the theorem statement ending with ':= by sorry'.
        2. DO NOT include the proof.
        3. Include standard Mathlib imports (e.g., import Mathlib.MeasureTheory.Measure.MeasureSpace).
        """
        try:
            raw_signature = await self.bridge.agent.generate_async(signature_prompt)
            clean_sig = re.sub(r"```lean|```", "", raw_signature).strip()
        except Exception as e:
            print(f"   ⚠️ LLM signature extraction failed: {e}. Using regex fallback.")
            clean_sig = f"theorem {task_id} : sorry := by sorry"

        # 6. 组装最终 Hybrid 代码 (手动物理注入)
        hybrid_content = f"""{local_import_lines}

/--
PROBLEM
{task['content']}

PROVIDED SOLUTION
This is a whole-task formalization. 
Please construct the Lean 4 proof.
Use the imported local dependencies where applicable.
-/
{clean_sig}
"""
        with open(output_dir / f"{task_id}.lean", "w", encoding="utf-8") as f:
            f.write(hybrid_content)

        # 7. 环境配置文件 (v4.28.0)
        with open(staging_dir / "lean-toolchain", "w") as f: f.write("leanprover/lean4:v4.28.0")
        with open(staging_dir / "lakefile.toml", "w") as f:
            f.write(f'name = "{task_id}_project"\n\n[[lean_lib]]\nname = "ToyApollo"\n\n[[require]]\nname = "mathlib"\ngit = "https://github.com/leanprover-community/mathlib4.git"\nrev = "v4.28.0"\n')
        
        # 复制 manifest 如果存在
        if os.path.exists("lake-manifest.json"):
            shutil.copy("lake-manifest.json", staging_dir / "lake-manifest.json")

        print(f"   ✨ Success! Aristotle bundle ready at: {staging_dir}")

async def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--task_id", type=str, required=True)
    parser.add_argument("--unsolved_file", type=str, default="plans/unsolved_tasks.json")
    args = parser.parse_args()

    offloader = AristotleDirectOffloader()
    await offloader.prepare_package(args.task_id, unsolved_file=args.unsolved_file)

if __name__ == "__main__":
    asyncio.run(main())
