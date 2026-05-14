import os
import json
import shutil
import time
import re
import asyncio
import argparse
from pathlib import Path
from typing import Any, TypedDict

from src.aristotle_bridge import AristotleBridge
from src.aristotle_prompt import build_aristotle_prompt
from src.block_id_naming import (
    alias_map,
    canonicalize_block_id,
    canonicalize_id_list,
    canonicalize_task_dict,
    legacy_ids_for,
)
from src.toy_apollo.core.settings import get_settings
from src.toy_apollo.dependency_decisions import DependencyDecision, record_dependency_decision


class OffloadCandidate(TypedDict):
    block_id: str
    type: str
    title: str
    content: str
    source_plan: str
    dependencies: list[str]
    soft_imports: list[str]
    soft_imports_confirmed_at: str
    depth: int
    status: str


class AristotleDirectOffloader:
    def __init__(self):
        self.bridge = AristotleBridge()
        self.timestamp = int(time.time())
        self.outbox_root = Path("aristotle_outbox") / f"direct_{self.timestamp}"
        self.settings = get_settings()

    @staticmethod
    def _dedupe_keep_order(ids: list[str]) -> list[str]:
        return canonicalize_id_list(ids)

    def _candidate_lookup_ids(self, dep_id: str) -> list[str]:
        canonical = canonicalize_block_id(dep_id)
        if not canonical:
            return []
        lookup_ids = [canonical]
        lookup_ids.extend([legacy for legacy in legacy_ids_for(canonical) if legacy != canonical])
        return lookup_ids

    def _resolve_dependency_path(self, dep_id: str) -> Path | None:
        for lookup_id in self._candidate_lookup_ids(dep_id):
            search_locations = [
                Path("ToyApollo/Output") / f"{lookup_id}.lean",
                Path("output_lean_files/general") / f"{lookup_id}.lean",
            ]
            if Path("output_lean_files").exists():
                for d in Path("output_lean_files").iterdir():
                    if d.is_dir():
                        search_locations.append(d / f"{lookup_id}.lean")

            for loc in search_locations:
                if loc.exists():
                    return loc
        return None

    def _rewrite_copied_file_content(self, content: str, source_stem: str, target_stem: str) -> str:
        rewritten = re.sub(
            r"import\s+ToyApollo\.Output\.(\w+)",
            lambda m: f"import ToyApollo.Output.{canonicalize_block_id(m.group(1)) or m.group(1)}",
            content,
        )
        if source_stem != target_stem:
            rewritten = re.sub(
                rf"^((?:noncomputable\s+)?(?:def|theorem|lemma)\s+){re.escape(source_stem)}\b",
                rf"\1{target_stem}",
                rewritten,
                flags=re.MULTILINE,
            )
        for legacy, canonical in alias_map().items():
            rewritten = re.sub(
                rf"(?<![A-Za-z0-9_]){re.escape(legacy)}(?![A-Za-z0-9_])",
                canonical,
                rewritten,
            )
        return rewritten

    def _record_offload_dependency_decisions(
        self,
        *,
        task: dict[str, Any],
        hard_deps: list[str],
        soft_imports: list[str],
        selected_ids: list[str],
        soft_import_source: str,
        manifest_path: Path,
    ) -> None:
        task_id = canonicalize_block_id(str(task.get("block_id", "")))
        if not task_id:
            return
        source_plan = str(task.get("source_plan", "") or "")
        for dep_id in selected_ids:
            record_dependency_decision(
                self.settings,
                DependencyDecision(
                    task_id=task_id,
                    dep_id=dep_id,
                    kind="materialized",
                    phase="phase3_offload",
                    criterion="final_union_materialized",
                    evidence="Materialized in Aristotle dependency manifest",
                    source_plan=source_plan,
                    source_file=str(manifest_path),
                ),
            )

    def _copy_dependency_file(self, source_path: Path, target_path: Path) -> None:
        with open(source_path, "r", encoding="utf-8") as f:
            content = f.read()
        rewritten = self._rewrite_copied_file_content(content, source_path.stem, target_path.stem)
        with open(target_path, "w", encoding="utf-8") as f:
            f.write(rewritten)

    def _dependency_manifest_entry(self, dep_id: str) -> dict[str, str]:
        dep_id = canonicalize_block_id(dep_id) or str(dep_id).strip()
        payload = self.bridge._phase1_task_payload(dep_id, max_chars=800)
        if payload is not None:
            return payload
        return {
            "block_id": dep_id,
            "type": "",
            "title": "",
            "content": "",
            "source_plan": "",
        }

    def get_full_dependency_closure(self, initial_deps: list[str]) -> dict[str, Path]:
        closure: dict[str, Path] = {}
        queue = list(self._dedupe_keep_order(initial_deps))
        visited: set[str] = set()

        while queue:
            dep_id = canonicalize_block_id(queue.pop(0))
            if not dep_id or dep_id in visited:
                continue
            visited.add(dep_id)

            found_path = self._resolve_dependency_path(dep_id)
            if found_path is None:
                print(f"   ⚠️ Warning: Could not find physical file for dependency: {dep_id}")
                continue

            canonical_stem = canonicalize_block_id(found_path.stem) or dep_id
            closure[canonical_stem] = found_path

            with open(found_path, "r", encoding="utf-8") as f:
                content = self._rewrite_copied_file_content(f.read(), found_path.stem, canonical_stem)
            sub_deps = re.findall(r"import\s+ToyApollo\.Output\.(\w+)", content)
            for sub_dep in canonicalize_id_list(sub_deps):
                if sub_dep not in visited:
                    queue.append(sub_dep)

        return closure

    def _load_legacy_task(self, task_id: str, unsolved_file: str) -> OffloadCandidate | None:
        if not os.path.exists(unsolved_file):
            print(f"❌ Legacy unsolved file not found: {unsolved_file}")
            return None
        with open(unsolved_file, "r", encoding="utf-8") as f:
            tasks = json.load(f)
        task = next((t for t in tasks if canonicalize_block_id(t.get("block_id")) == task_id), None)
        if not task:
            print(f"❌ Task {task_id} not found in legacy file: {unsolved_file}")
            return None
        task.setdefault("type", "Problem")
        task.setdefault("title", task_id)
        task.setdefault("content", "")
        task.setdefault("source_plan", "legacy_unsolved")
        task.setdefault("dependencies", [])
        task.setdefault("soft_imports", [])
        task.setdefault("soft_imports_confirmed_at", "")
        task.setdefault("depth", 0)
        task.setdefault("status", "FAILED_LOCAL")
        return canonicalize_task_dict(task)

    async def prepare_package(self, candidate_or_task_id: OffloadCandidate | str, unsolved_file="plans/unsolved_tasks.json"):
        task: dict[str, Any] | None = None
        if isinstance(candidate_or_task_id, dict):
            task = canonicalize_task_dict(candidate_or_task_id)
            task_id = task.get("block_id", "")
        else:
            task_id = canonicalize_block_id(candidate_or_task_id)
            print("⚠️ [Deprecated] prepare_package(task_id, unsolved_file=...) is legacy. Use OffloadCandidate input instead.")
            task = self._load_legacy_task(task_id, unsolved_file)
            if not task:
                return

        if not task_id:
            print("❌ Invalid offload candidate: missing block_id")
            return

        print(f"🚀 [Direct-Offload] Packaging {task_id} with Mathematical Architect...")

        staging_dir = self.outbox_root / task_id
        output_dir = staging_dir / "ToyApollo" / "Output"
        os.makedirs(output_dir, exist_ok=True)

        task_type = str(task.get("type", "")).strip()
        task_type_norm = task_type.lower()
        soft_imports_confirmed_at = str(task.get("soft_imports_confirmed_at", "") or "").strip()
        if task_type_norm == "problem" and not soft_imports_confirmed_at:
            raise RuntimeError(
                "missing_soft_imports_selection: run --phase 3 --phase3-mode soft-pack/soft-apply before offload"
            )

        deps = task.get("dependencies", [])
        if deps is None:
            deps = []
        if not isinstance(deps, list):
            raise RuntimeError(f"invalid_hard_dependencies_type:{type(deps).__name__}")

        hard_deps = self._dedupe_keep_order([str(d).strip() for d in deps if str(d).strip()])
        for dep_id in hard_deps:
            if self._resolve_dependency_path(dep_id) is None:
                print(f"   ⚠️ Planned hard dependency missing locally: {dep_id}")

        soft_imports: list[str] = []
        soft_import_source = "none"
        if task_type_norm == "problem":
            stored_soft_imports = self._dedupe_keep_order(
                [str(s).strip() for s in task.get("soft_imports", []) if str(s).strip()]
            )
            soft_imports = stored_soft_imports
            soft_import_source = "operator_confirmed"
            print(f"   💾 Using operator-confirmed soft imports for {task_id}: {soft_imports or '(none)'}")

            selected_ids = self._dedupe_keep_order(hard_deps + soft_imports)
            print(f"   📊 Hard deps count: {len(hard_deps)}")
            print(f"   📊 Soft imports count: {len(soft_imports)}")
            print(f"   📊 Final union count: {len(selected_ids)}")
        else:
            selected_ids = hard_deps
            print(f"   📌 Using hard dependencies for non-Problem task ({task_type}): {selected_ids}")
            print(f"   📊 Hard deps count: {len(hard_deps)}")
            print(f"   📊 Soft imports count: 0")
            print(f"   📊 Final union count: {len(selected_ids)}")

        closure_files = self.get_full_dependency_closure(selected_ids)
        print(f"   🔗 Total of {len(closure_files)} local files in the project mirror.")

        for canonical_stem, source_path in closure_files.items():
            self._copy_dependency_file(source_path, output_dir / f"{canonical_stem}.lean")

        dependency_manifest = {
            "task_id": task_id,
            "task_type": task_type,
            "hard_dependencies": [self._dependency_manifest_entry(dep_id) for dep_id in hard_deps],
            "soft_imports": [self._dependency_manifest_entry(dep_id) for dep_id in soft_imports],
            "soft_import_source": soft_import_source,
            "final_import_union": [self._dependency_manifest_entry(dep_id) for dep_id in selected_ids],
        }
        dependency_manifest_path = staging_dir / "dependency_manifest.json"
        with open(dependency_manifest_path, "w", encoding="utf-8") as f:
            json.dump(dependency_manifest, f, indent=2, ensure_ascii=False)
        self._record_offload_dependency_decisions(
            task=task,
            hard_deps=hard_deps,
            soft_imports=soft_imports,
            selected_ids=selected_ids,
            soft_import_source=soft_import_source,
            manifest_path=dependency_manifest_path,
        )

        upload_manifest = {
            "task_id": task_id,
            "task_type": task_type,
            "prompt": build_aristotle_prompt(task_id),
            "main_task_file": f"ToyApollo/Output/{task_id}.lean",
            "hard_dependencies": dependency_manifest["hard_dependencies"],
            "soft_imports": dependency_manifest["soft_imports"],
            "final_import_union": dependency_manifest["final_import_union"],
            "uploaded_files": [],
        }

        print(f"   🧩 Writing minimal Aristotle target skeleton...")

        importable_stems = [sid for sid in selected_ids if sid in closure_files]
        if task_type_norm != "problem":
            for stem in closure_files.keys():
                if stem.startswith("def_") and stem not in importable_stems:
                    importable_stems.append(stem)

        local_import_lines = "\n".join([f"import ToyApollo.Output.{stem}" for stem in importable_stems if stem != task_id])

        target_skeleton = f"theorem {task_id} : sorry := by sorry"

        def _format_manifest_lines(entries: list[dict[str, str]]) -> str:
            if not entries:
                return "- (none)"
            lines: list[str] = []
            for entry in entries:
                dep_id = entry.get("block_id", "")
                dep_type = entry.get("type", "")
                title = entry.get("title", "")
                source_plan = entry.get("source_plan", "")
                content = entry.get("content", "")
                lines.append(
                    f"- {dep_id} | type={dep_type} | title={title} | source_plan={source_plan}"
                )
                if content:
                    lines.append(f"  latex={content}")
            return "\n".join(lines)

        hard_dep_lines = _format_manifest_lines(dependency_manifest["hard_dependencies"])
        soft_import_lines = _format_manifest_lines(dependency_manifest["soft_imports"])
        final_union_lines = _format_manifest_lines(dependency_manifest["final_import_union"])
        hybrid_content = f"""{local_import_lines}

/--
PROBLEM
{task['content']}

HARD DEPENDENCIES (plan-derived and mandatory imports already uploaded as local Lean files)
{hard_dep_lines}

SOFT IMPORTS (externally selected but mandatory imports already uploaded as local Lean files)
{soft_import_lines}

FINAL IMPORT UNION (all listed files are mandatory imports and physically included in this package)
{final_union_lines}

PROVIDED SOLUTION
This is a whole-task formalization. 
Please construct the Lean 4 proof.
The hard dependencies and soft imports above are all mandatory imports once selected.
The imported local dependencies above are physically present in ToyApollo/Output and must be reused when applicable.
Do not redefine concepts or theorems that are already provided by imported local dependencies.
For chapter-local limsup/liminf sequence problems, prefer the textbook semantics already provided by imported local dependencies such as `seqLimsup` / `seqLiminf` instead of defaulting to `Filter.limsup` on `ℝ`.
-/
{target_skeleton}
"""
        with open(output_dir / f"{task_id}.lean", "w", encoding="utf-8") as f:
            f.write(hybrid_content)

        with open(staging_dir / "lean-toolchain", "w") as f:
            f.write("leanprover/lean4:v4.28.0")
        with open(staging_dir / "lakefile.toml", "w") as f:
            f.write(f'name = "{task_id}_project"\n\n[[lean_lib]]\nname = "ToyApollo"\n\n[[require]]\nname = "mathlib"\ngit = "https://github.com/leanprover-community/mathlib4.git"\nrev = "v4.28.0"\n')

        if os.path.exists("lake-manifest.json"):
            shutil.copy("lake-manifest.json", staging_dir / "lake-manifest.json")

        upload_manifest["uploaded_files"] = sorted(
            str(path.relative_to(staging_dir)).replace("\\", "/")
            for path in staging_dir.rglob("*")
            if path.is_file()
        ) + ["upload_manifest.json"]
        with open(staging_dir / "upload_manifest.json", "w", encoding="utf-8") as f:
            json.dump(upload_manifest, f, indent=2, ensure_ascii=False)

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
