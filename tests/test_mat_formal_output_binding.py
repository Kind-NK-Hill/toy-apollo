from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from src.compiler import LeanCompiler
from src.toy_apollo.core.formal_output import (
    formal_build_root,
    formal_scratch_binding,
    formal_task_module,
    formal_task_path,
    official_output_targets,
)
from src.toy_apollo.phase2_output_binding import resolve_phase2_output_binding
from src.toy_apollo.phase2_prompt_pack import (
    _candidate_local_imports,
    _formal_lean_compiler,
    _iter_review_existing_queue_outputs,
    _run_official_module_build,
    _run_staged_official_build,
    build_import_lines,
)
from src.toy_apollo.phase2_semantic_review import build_semantic_review_input
from src.toy_apollo.state_reconcile import discover_formal_support_files


class MatFormalOutputBindingTests(unittest.TestCase):
    def make_settings(self, root: Path) -> SimpleNamespace:
        mat_repo = root / "MAT3280-formalization-output"
        return SimpleNamespace(
            runtime_root=root / "toy-apollo",
            mat_repo_dir=mat_repo,
            lean_scratch_dir=mat_repo / "ProbabilityTheory" / "Scratch",
            toyapollo_output_dir=root / "toy-apollo" / "ToyApollo" / "Output",
            output_lean_files_dir=root / "artifacts" / "output_lean_files",
            phase2_prompt_packs_dir=root / "artifacts" / "phase2_prompt_packs",
            plans_dir=root / "toy-apollo" / "plans",
        )

    def test_mat_is_the_single_formal_owner(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            settings = self.make_settings(Path(raw))

            self.assertEqual(formal_build_root(settings), settings.mat_repo_dir)
            self.assertEqual(
                formal_task_path("prob_13_11", settings),
                settings.mat_repo_dir
                / "ProbabilityTheory"
                / "chapter_13"
                / "prob_13_11.lean",
            )
            self.assertEqual(
                formal_task_module("prob_13_11", settings),
                "ProbabilityTheory.chapter_13.prob_13_11",
            )
            self.assertEqual(
                official_output_targets("prob_13_11", "chapter13-problems", settings),
                [formal_task_path("prob_13_11", settings)],
            )

    def test_output_binding_and_generated_imports_use_probability_theory(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            settings = self.make_settings(Path(raw))
            ledger = SimpleNamespace(ledger={"tasks": {"thm_7_8": {}}})
            task = {
                "block_id": "thm_7_8",
                "source_plan": "chapter7",
                "dependencies": ["def_7_1", "thm_1_2"],
            }

            binding = resolve_phase2_output_binding(task, ledger, settings)
            self.assertEqual(binding.output_module, "ProbabilityTheory.chapter_07.thm_7_8")
            self.assertEqual(binding.official_targets, [formal_task_path("thm_7_8", settings)])
            self.assertEqual(
                build_import_lines(task, settings),
                [
                    "import Mathlib",
                    "import ProbabilityTheory.chapter_07.def_7_1",
                    "import ProbabilityTheory.chapter_01.thm_1_2",
                ],
            )

    def test_probability_theory_imports_participate_in_self_import_checks(self) -> None:
        code = "\n".join(
            [
                "import Mathlib",
                "import ProbabilityTheory.chapter_07.thm_7_8",
                "import ProbabilityTheory.chapter_01.thm_1_2",
            ]
        )
        self.assertEqual(_candidate_local_imports(code), ["thm_7_8", "thm_1_2"])

    def test_existing_kenneth_filename_case_is_preserved(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            settings = self.make_settings(Path(raw))
            chapter = settings.mat_repo_dir / "ProbabilityTheory" / "chapter_01"
            chapter.mkdir(parents=True)
            existing = chapter / "Ex_1_3_1.lean"
            existing.write_text("import Mathlib\n", encoding="utf-8")

            self.assertEqual(formal_task_path("ex_1_3_1", settings), existing)
            self.assertEqual(
                formal_task_module("ex_1_3_1", settings),
                "ProbabilityTheory.chapter_01.Ex_1_3_1",
            )
            self.assertEqual(
                discover_formal_support_files(
                    settings.mat_repo_dir / "ProbabilityTheory",
                    "ex_1_3_1",
                    formal_task_ids={"ex_1_3_1"},
                ),
                {},
            )

    def test_scratch_modules_live_in_mat_and_not_toyapollo_output(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            settings = self.make_settings(Path(raw))
            path, module = formal_scratch_binding("PackBuildCheck_demo_1", settings)
            self.assertEqual(
                path,
                settings.mat_repo_dir
                / "ProbabilityTheory"
                / "Scratch"
                / "PackBuildCheck_demo_1.lean",
            )
            self.assertEqual(module, "ProbabilityTheory.Scratch.PackBuildCheck_demo_1")
            self.assertFalse(str(path).startswith(str(settings.toyapollo_output_dir)))

    def test_compiler_validation_scratch_is_configurable_for_mat(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            settings = self.make_settings(Path(raw))
            settings.mat_repo_dir.mkdir(parents=True)

            compiler = _formal_lean_compiler(settings)

            self.assertIsInstance(compiler, LeanCompiler)
            self.assertEqual(
                Path(compiler.validation_file),
                settings.mat_repo_dir
                / "ProbabilityTheory"
                / "Scratch"
                / "Temp_Validation.lean",
            )
            self.assertEqual(
                compiler.validation_target,
                "ProbabilityTheory.Scratch.Temp_Validation",
            )
            self.assertFalse(settings.toyapollo_output_dir.exists())

    def test_missing_mat_root_fails_without_creating_a_ghost_repository(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            settings = self.make_settings(Path(raw))

            success, detail = _run_official_module_build("prob_13_11", settings)

            self.assertFalse(success)
            self.assertIn("Configured formal build root does not exist", detail)
            self.assertFalse(settings.mat_repo_dir.exists())

    def test_review_queue_keeps_kenneth_case_and_skips_support_modules(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            settings = self.make_settings(Path(raw))
            settings.plans_dir.mkdir(parents=True)
            (settings.plans_dir / "chapter1_plan.json").write_text(
                json.dumps(
                    [
                        {
                            "block_id": "ex_1_3_1",
                            "type": "Example_Proof",
                            "content": "Example",
                            "dependencies": [],
                        }
                    ]
                ),
                encoding="utf-8",
            )
            chapter = settings.mat_repo_dir / "ProbabilityTheory" / "chapter_01"
            chapter.mkdir(parents=True)
            task_path = chapter / "Ex_1_3_1.lean"
            support_path = chapter / "ex_1_3_1_support.lean"
            task_path.write_text("import Mathlib\n", encoding="utf-8")
            support_path.write_text("import Mathlib\n", encoding="utf-8")

            outputs, skipped = _iter_review_existing_queue_outputs(settings)

            self.assertEqual(outputs, [task_path])
            self.assertIn(str(support_path), skipped)

    def test_staged_build_restores_only_the_mat_owner(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            settings = self.make_settings(Path(raw))
            task_id = "prob_13_11"
            pack_dir = settings.phase2_prompt_packs_dir / task_id
            pack_dir.mkdir(parents=True)
            target = formal_task_path(task_id, settings)
            target.parent.mkdir(parents=True)
            target.write_text("old\n", encoding="utf-8")

            with patch(
                "src.toy_apollo.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = _run_staged_official_build(
                    task_id,
                    "chapter13-problems",
                    settings,
                    pack_dir,
                    "new\n",
                    attempt=1,
                    mode="build-check",
                    restore_on_success=True,
                )

            self.assertTrue(success, detail)
            self.assertEqual(target.read_text(encoding="utf-8"), "old\n")
            self.assertFalse(settings.toyapollo_output_dir.exists())
            self.assertFalse((pack_dir / ".staging" / "build-check-1").exists())

    def test_review_apply_lands_only_the_mat_owner(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            settings = self.make_settings(Path(raw))
            task_id = "prob_13_11"
            pack_dir = settings.phase2_prompt_packs_dir / task_id
            pack_dir.mkdir(parents=True)
            target = formal_task_path(task_id, settings)

            with patch(
                "src.toy_apollo.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = _run_staged_official_build(
                    task_id,
                    "chapter13-problems",
                    settings,
                    pack_dir,
                    "landed\n",
                    attempt=2,
                    mode="review-apply",
                    restore_on_success=False,
                )

            self.assertTrue(success, detail)
            self.assertEqual(target.read_text(encoding="utf-8"), "landed\n")
            self.assertFalse(settings.toyapollo_output_dir.exists())
            self.assertFalse((pack_dir / ".staging" / "review-apply-2").exists())

    def test_review_bundle_discovers_mat_task_owned_support(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            settings = self.make_settings(Path(raw))
            chapter = settings.mat_repo_dir / "ProbabilityTheory" / "chapter_07"
            chapter.mkdir(parents=True)
            (chapter / "thm_7_8.lean").write_text("import Mathlib\n", encoding="utf-8")
            (chapter / "thm_7_8_sandwich_support.lean").write_text(
                "import Mathlib\n", encoding="utf-8"
            )
            (chapter / "thm_7_9.lean").write_text("import Mathlib\n", encoding="utf-8")

            support = discover_formal_support_files(
                settings.mat_repo_dir / "ProbabilityTheory",
                "thm_7_8",
                formal_task_ids={"thm_7_8", "thm_7_9"},
            )
            self.assertEqual(
                set(support),
                {"ProbabilityTheory/chapter_07/thm_7_8_sandwich_support.lean"},
            )

    def test_official_review_bundle_records_mat_owner_and_support(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            settings = self.make_settings(Path(raw))
            settings.plans_dir.mkdir(parents=True)
            (settings.plans_dir / "chapter13_plan.json").write_text(
                json.dumps(
                    [
                        {
                            "block_id": "prob_13_11",
                            "type": "Problem",
                            "content": "Problem",
                            "dependencies": [],
                        }
                    ]
                ),
                encoding="utf-8",
            )
            chapter = settings.mat_repo_dir / "ProbabilityTheory" / "chapter_13"
            chapter.mkdir(parents=True)
            primary = chapter / "prob_13_11.lean"
            support = chapter / "prob_13_11_support.lean"
            code = "import Mathlib\n"
            primary.write_text(code, encoding="utf-8")
            support.write_text("import Mathlib\n", encoding="utf-8")

            review_input = build_semantic_review_input(
                task={
                    "block_id": "prob_13_11",
                    "type": "Problem",
                    "content": "Problem",
                    "source_plan": "chapter13",
                    "dependencies": [],
                },
                mode="review-existing",
                attempt=1,
                candidate_path=primary,
                candidate_code=code,
                import_lines=["import Mathlib"],
                dependency_summary=[],
                search_summary={},
                build_summary={"success": True},
                backend_id="test",
                reviewer_argv_hash="test",
                review_subject_kind="official_output",
                runtime_root=settings.runtime_root,
                formal_source_root=settings.mat_repo_dir / "ProbabilityTheory",
            )

            bundle = review_input["subject_bundle"]
            self.assertEqual(bundle["source_repo"], "MAT3280-formalization-output")
            self.assertEqual(bundle["layout"], "mat_bound_review_official_output")
            self.assertEqual(
                {item["path"] for item in bundle["files"]},
                {
                    str(primary).replace("\\", "/"),
                    "ProbabilityTheory/chapter_13/prob_13_11_support.lean",
                },
            )


if __name__ == "__main__":
    unittest.main()
