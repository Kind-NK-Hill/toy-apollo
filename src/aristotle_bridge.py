import os
import re
import shutil
import json
from pathlib import Path
from typing import Set
from src.block_id_naming import (
    canonicalize_block_id,
    canonicalize_id_list,
)

class AristotleBridge:
    def __init__(self, staging_root="plans/aristotle_staging"):
        self.staging_root = Path(staging_root)
        self.plan_task_index = self._build_phase1_plan_task_index(Path("plans"))

    @staticmethod
    def _normalize_summary_text(text: str, max_chars: int = 240) -> str:
        cleaned = re.sub(r"\s+", " ", text or "").strip()
        if not cleaned:
            return ""
        if len(cleaned) <= max_chars:
            return cleaned
        return cleaned[: max_chars - 3].rstrip() + "..."

    def _build_phase1_plan_task_index(self, plans_dir: Path) -> dict[str, dict]:
        index: dict[str, dict] = {}
        if not plans_dir.exists():
            return index

        for plan_file in sorted(plans_dir.glob("*_plan.json")):
            try:
                with open(plan_file, "r", encoding="utf-8") as f:
                    payload = json.load(f)
            except Exception:
                continue

            if isinstance(payload, dict):
                records = [payload]
            elif isinstance(payload, list):
                records = [row for row in payload if isinstance(row, dict)]
            else:
                records = []

            for row in records:
                row = dict(row)
                block_id = canonicalize_block_id(row.get("block_id", ""))
                if not isinstance(block_id, str) or not block_id.strip():
                    continue
                row["block_id"] = block_id
                row["dependencies"] = canonicalize_id_list(row.get("dependencies", []))
                if "soft_imports" in row:
                    row["soft_imports"] = canonicalize_id_list(row.get("soft_imports", []))
                if block_id in index:
                    continue
                index[block_id] = row
        return index

    def _summary_from_phase1_plan(self, block_id: str) -> str:
        task = self.plan_task_index.get(canonicalize_block_id(block_id))
        if not isinstance(task, dict):
            return ""
        title = task.get("title", "")
        content = task.get("content", "")
        parts: list[str] = []
        if isinstance(title, str) and title.strip():
            parts.append(title.strip())
        if isinstance(content, str) and content.strip():
            parts.append(content.strip())
        return self._normalize_summary_text(" | ".join(parts))

    def _phase1_task_payload(self, block_id: str, max_chars: int = 1200) -> dict[str, str] | None:
        canonical_id = canonicalize_block_id(block_id)
        task = self.plan_task_index.get(canonical_id)
        if not isinstance(task, dict):
            return None
        title = task.get("title", "")
        content = task.get("content", "")
        task_type = task.get("type", "")
        source_plan = task.get("source_plan", "")
        return {
            "block_id": canonical_id,
            "type": str(task_type or "").strip(),
            "title": self._normalize_summary_text(str(title or ""), max_chars=160),
            "content": self._normalize_summary_text(str(content or ""), max_chars=max_chars),
            "source_plan": str(source_plan or "").strip(),
        }

    def _summary_from_lean_source(self, source: str) -> str:
        # Match Lean block comments: /- ... -/, /-! ... -/, or /-- ... -/
        doc_match = re.search(r"/-(?:!|--)?\s*(.*?)\s*-/", source, re.DOTALL)
        if not doc_match:
            return ""
        raw_summary = doc_match.group(1).strip()
        if not raw_summary:
            return ""
        # Keep first two lines before normalization for concise context.
        first_two = "\n".join(raw_summary.splitlines()[:2])
        return self._normalize_summary_text(first_two)
        
    def get_library_catalog(self) -> str:
        """Scans ToyApollo/Output and builds a catalog (Phase1 plan summary preferred)."""
        catalog = []
        output_path = Path("ToyApollo/Output")
        if not output_path.exists(): return "No local library found."
        
        for lean_file in sorted(output_path.glob("*.lean")):
            block_id = canonicalize_block_id(lean_file.stem)
            try:
                summary = self._summary_from_phase1_plan(block_id)
                if not summary:
                    with open(lean_file, "r", encoding="utf-8") as f:
                        content = f.read()
                    summary = self._summary_from_lean_source(content)
                if not summary:
                    summary = "No description available."
                catalog.append(f"- {block_id}: {summary}")
            except Exception:
                continue
        return "\n".join(catalog)

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
