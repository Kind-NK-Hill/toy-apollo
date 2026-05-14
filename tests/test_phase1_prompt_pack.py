import json
import shutil
import subprocess
import sys
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.ledger_manager import LedgerManager  # noqa: E402
from src.toy_apollo.core.settings import Settings  # noqa: E402
from src.toy_apollo.dependency_decisions import load_dependency_decisions  # noqa: E402
from src.toy_apollo.phase1_prompt_pack import apply_phase1_pack, write_phase1_pack  # noqa: E402
from src.toy_apollo.phase1_plan_audit import audit_phase1_plans  # noqa: E402


def make_settings(root: Path) -> Settings:
    return Settings(
        runtime_root=root,
        artifact_root=root,
        plans_dir=root / "plans",
        reports_dir=root / "reports",
        formalized_chapters_dir=root / "formalized_chapters",
        output_lean_files_dir=root / "output_lean_files",
        phase2_prompt_packs_dir=root / "phase2_prompt_packs",
        phase2_softdep_packs_dir=root / "phase2_softdep_packs",
        error_logs_dir=root / "error_logs",
        toyapollo_output_dir=root / "ToyApollo" / "Output",
        aristotle_outbox_dir=root / "aristotle_outbox",
        aristotle_archives_dir=root / "aristotle_archives",
        mathlib_index_file=root / "mathlib_index.faiss",
        mathlib_corpus_file=root / "mathlib_corpus.json",
        project_ledger_file=root / "project_ledger.json",
        lab_notebook_file=root / "lab_notebook.json",
        mathlib_path=root / ".lake" / "packages" / "mathlib" / "Mathlib",
        phase1_prompt_packs_dir=root / "phase1_prompt_packs",
        dependency_decisions_dir=root / "dependency_decisions",
    )


class Phase1PromptPackTests(unittest.TestCase):
    def _write_pack(self, root: Path, stem: str, tex: str) -> tuple[Path, Settings]:
        settings = make_settings(root)
        tex_file = root / "inputs" / f"{stem}.tex"
        tex_file.parent.mkdir(parents=True, exist_ok=True)
        tex_file.write_text(tex, encoding="utf-8")
        pack_dir = write_phase1_pack(tex_file, settings)
        return pack_dir, settings

    def _write_draft(self, pack_dir: Path, payload: list[dict]) -> None:
        (pack_dir / "draft_plan.json").write_text(
            json.dumps(payload, indent=2, ensure_ascii=False),
            encoding="utf-8",
        )

    def test_write_phase1_pack_names_agent_decomposition_step(self):
        root = REPO_ROOT / "tests" / "_tmp_phase1_agent_decompose_prompt"
        try:
            shutil.rmtree(root, ignore_errors=True)
            pack_dir, _settings = self._write_pack(
                root,
                "chapter9_moments_mgf",
                "\\subsection*{9.1 Moments and Moment Generating Functions}\nText.",
            )

            prompt = (pack_dir / "operator_prompt.md").read_text(encoding="utf-8")

            self.assertIn("Phase 1 pack", prompt)
            self.assertIn("agent decompose", prompt)
            self.assertIn("Phase 1 apply", prompt)
            self.assertIn("draft_plan.json", prompt)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_write_phase1_pack_rejects_multiple_source_units(self):
        root = REPO_ROOT / "tests" / "_tmp_phase1_multi_subsection_rejected"
        try:
            shutil.rmtree(root, ignore_errors=True)
            settings = make_settings(root)
            tex_file = root / "inputs" / "chapter9-full.tex"
            tex_file.parent.mkdir(parents=True, exist_ok=True)
            tex_file.write_text(
                (
                    "\\section*{Moment Generating Functions and Characteristic Functions}\n"
                    "\\subsection*{9.1 Moments and Moment Generating Functions}\n"
                    "Text.\n"
                    "\\subsection*{9.2 Characteristic Functions}\n"
                    "Text.\n"
                ),
                encoding="utf-8",
            )

            with self.assertRaisesRegex(ValueError, "one subsection per Phase 1 input"):
                write_phase1_pack(tex_file, settings)

            self.assertFalse((settings.phase1_prompt_packs_dir / "chapter9-full").exists())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_apply_phase1_pack_rejects_theorem_section_collapsed_to_remark(self):
        root = REPO_ROOT / "tests" / "_tmp_phase1_theorem_rejected"
        try:
            shutil.rmtree(root, ignore_errors=True)
            pack_dir, settings = self._write_pack(
                root,
                "17_chap5_model_kolmogorov",
                (
                    "\\section{A Model for a Sequence of Independent Random Variables}\n\n"
                    "\\begin{theorem}[Kolmogorov's Zero--One Law]\n"
                    "Statement.\n"
                    "\\end{theorem}\n\n"
                    "\\begin{proof}\n"
                    "Proof text.\n"
                    "\\end{proof}\n"
                ),
            )
            self._write_draft(
                pack_dir,
                [
                    {
                        "block_id": "rem_5_5_kolmogorov_model",
                        "type": "Remark",
                        "title": "Text",
                        "content": "all collapsed",
                        "dependencies": [],
                    }
                ],
            )
            ledger = LedgerManager(ledger_path=str(settings.project_ledger_file))

            success, detail, found_ids = apply_phase1_pack(
                root / "inputs" / "17_chap5_model_kolmogorov.tex",
                ledger,
                settings,
            )

            self.assertFalse(success)
            self.assertEqual(found_ids, [])
            self.assertIn("17_chap5_model_kolmogorov", detail)
            self.assertIn("theorem", detail.lower())
            self.assertFalse((settings.plans_dir / "17_chap5_model_kolmogorov_plan.json").exists())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_apply_phase1_pack_rejects_problem_section_without_problem_tasks(self):
        root = REPO_ROOT / "tests" / "_tmp_phase1_problems_rejected"
        try:
            shutil.rmtree(root, ignore_errors=True)
            pack_dir, settings = self._write_pack(
                root,
                "18_chap5_problems",
                (
                    "\\subsection*{Problems}\n"
                    "\\begin{enumerate}\n"
                    "\\item First problem.\n"
                    "\\item Second problem.\n"
                    "\\item Third problem.\n"
                    "\\end{enumerate}\n"
                ),
            )
            self._write_draft(
                pack_dir,
                [
                    {
                        "block_id": "rem_5_0_problems_header",
                        "type": "Remark",
                        "title": "Section Header",
                        "content": "all collapsed",
                        "dependencies": [],
                    }
                ],
            )
            ledger = LedgerManager(ledger_path=str(settings.project_ledger_file))

            success, detail, found_ids = apply_phase1_pack(
                root / "inputs" / "18_chap5_problems.tex",
                ledger,
                settings,
            )

            self.assertFalse(success)
            self.assertEqual(found_ids, [])
            self.assertIn("18_chap5_problems", detail)
            self.assertIn("problem", detail.lower())
            self.assertFalse((settings.plans_dir / "18_chap5_problems_plan.json").exists())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_apply_phase1_pack_normalizes_exercise_to_problem(self):
        root = REPO_ROOT / "tests" / "_tmp_phase1_exercise_normalized"
        try:
            shutil.rmtree(root, ignore_errors=True)
            pack_dir, settings = self._write_pack(
                root,
                "24_chap6_problems",
                (
                    "\\subsection*{Problems}\n"
                    "\\begin{enumerate}\n"
                    "\\item First problem.\n"
                    "\\end{enumerate}\n"
                ),
            )
            self._write_draft(
                pack_dir,
                [
                    {
                        "block_id": "prob_6_1",
                        "type": "Exercise",
                        "title": "Exercise",
                        "content": "First problem.",
                        "dependencies": [],
                    }
                ],
            )
            ledger = LedgerManager(ledger_path=str(settings.project_ledger_file))

            success, detail, found_ids = apply_phase1_pack(
                root / "inputs" / "24_chap6_problems.tex",
                ledger,
                settings,
            )

            self.assertTrue(success)
            self.assertEqual(found_ids, ["prob_6_1"])
            self.assertIn("validated", detail.lower())
            plan_payload = json.loads(
                (settings.plans_dir / "24_chap6_problems_plan.json").read_text(encoding="utf-8")
            )
            self.assertEqual(plan_payload[0]["type"], "Problem")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_apply_phase1_pack_rejects_unknown_task_type(self):
        root = REPO_ROOT / "tests" / "_tmp_phase1_bad_type"
        try:
            shutil.rmtree(root, ignore_errors=True)
            pack_dir, settings = self._write_pack(
                root,
                "08_chap4_misc",
                "Plain prose without formal environments.\n",
            )
            self._write_draft(
                pack_dir,
                [
                    {
                        "block_id": "chunk_0",
                        "type": "Exercise_Proof",
                        "title": "Bad Type",
                        "content": "Plain prose.",
                        "dependencies": [],
                    }
                ],
            )
            ledger = LedgerManager(ledger_path=str(settings.project_ledger_file))

            success, detail, found_ids = apply_phase1_pack(
                root / "inputs" / "08_chap4_misc.tex",
                ledger,
                settings,
            )

            self.assertFalse(success)
            self.assertEqual(found_ids, [])
            self.assertIn("invalid", detail.lower())
            self.assertIn("Exercise_Proof", detail)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_apply_phase1_pack_injects_references_for_theorem_statements(self):
        root = REPO_ROOT / "tests" / "_tmp_phase1_theorem_statement_refs"
        try:
            shutil.rmtree(root, ignore_errors=True)
            pack_dir, settings = self._write_pack(
                root,
                "28_chap7_pushforward_change_of_variable",
                (
                    "\\begin{thmbox}{7.12}\n"
                    "By Theorem 6.6, this theorem has a cross-chapter dependency.\n"
                    "\\end{thmbox}\n"
                ),
            )
            self._write_draft(
                pack_dir,
                [
                    {
                        "block_id": "thm_7_12",
                        "type": "Theorem_Statement",
                        "title": "Change of Variable",
                        "content": "By Theorem 6.6, this theorem has a cross-chapter dependency.",
                        "dependencies": ["def_7_1"],
                    }
                ],
            )
            ledger = LedgerManager(ledger_path=str(settings.project_ledger_file))

            success, _detail, _found_ids = apply_phase1_pack(
                root / "inputs" / "28_chap7_pushforward_change_of_variable.tex",
                ledger,
                settings,
            )

            self.assertTrue(success)
            plan_payload = json.loads(
                (settings.plans_dir / "28_chap7_pushforward_change_of_variable_plan.json").read_text(encoding="utf-8")
            )
            self.assertIn("thm_6_6", plan_payload[0]["dependencies"])
            decisions = load_dependency_decisions(settings, "thm_7_12")
            by_dep = {decision["dep_id"]: decision for decision in decisions}
            self.assertEqual(by_dep["thm_6_6"]["criterion"], "explicit_text_reference")
            self.assertEqual(by_dep["thm_6_6"]["evidence"], "Theorem 6.6")
            self.assertEqual(by_dep["def_7_1"]["criterion"], "operator_declared_reliance")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_apply_phase1_pack_accepts_healthy_theorem_with_proof_plan(self):
        root = REPO_ROOT / "tests" / "_tmp_phase1_healthy_theorem"
        try:
            shutil.rmtree(root, ignore_errors=True)
            pack_dir, settings = self._write_pack(
                root,
                "17_chap5_model_kolmogorov",
                (
                    "\\section{A Model for a Sequence of Independent Random Variables}\n\n"
                    "\\begin{theorem}[Kolmogorov's Zero--One Law]\n"
                    "Statement.\n"
                    "\\end{theorem}\n\n"
                    "\\begin{proof}\n"
                    "Proof text.\n"
                    "\\end{proof}\n"
                ),
            )
            self._write_draft(
                pack_dir,
                [
                    {
                        "block_id": "thm_5_11",
                        "type": "Theorem_with_Proof",
                        "title": "Kolmogorov's Zero--One Law",
                        "content": "theorem plus proof",
                        "dependencies": [],
                    }
                ],
            )
            ledger = LedgerManager(ledger_path=str(settings.project_ledger_file))

            success, detail, found_ids = apply_phase1_pack(
                root / "inputs" / "17_chap5_model_kolmogorov.tex",
                ledger,
                settings,
            )

            self.assertTrue(success)
            self.assertEqual(found_ids, ["thm_5_11"])
            self.assertIn("validated", detail.lower())
            self.assertTrue((settings.plans_dir / "17_chap5_model_kolmogorov_plan.json").exists())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_audit_phase1_plans_classifies_known_failure_patterns(self):
        root = REPO_ROOT / "tests" / "_tmp_phase1_audit"
        try:
            shutil.rmtree(root, ignore_errors=True)
            settings = make_settings(root)
            settings.plans_dir.mkdir(parents=True, exist_ok=True)
            inputs_dir = root / "inputs"
            inputs_dir.mkdir(parents=True, exist_ok=True)

            (inputs_dir / "17_chap5_model_kolmogorov.tex").write_text(
                "\\begin{theorem}Statement.\\end{theorem}\\begin{proof}Proof.\\end{proof}",
                encoding="utf-8",
            )
            (settings.plans_dir / "17_chap5_model_kolmogorov_plan.json").write_text(
                json.dumps(
                    [
                        {
                            "block_id": "rem_5_5_kolmogorov_model",
                            "type": "Remark",
                            "title": "Text",
                            "content": "collapsed",
                            "dependencies": [],
                            "source_plan": "17_chap5_model_kolmogorov",
                        }
                    ],
                    indent=2,
                    ensure_ascii=False,
                ),
                encoding="utf-8",
            )

            (inputs_dir / "18_chap5_problems.tex").write_text(
                "\\subsection*{Problems}\\begin{enumerate}\\item A\\item B\\item C\\end{enumerate}",
                encoding="utf-8",
            )
            (settings.plans_dir / "18_chap5_problems_plan.json").write_text(
                json.dumps(
                    [
                        {
                            "block_id": "rem_5_0_problems_header",
                            "type": "Remark",
                            "title": "Section Header",
                            "content": "collapsed",
                            "dependencies": [],
                            "source_plan": "18_chap5_problems",
                        }
                    ],
                    indent=2,
                    ensure_ascii=False,
                ),
                encoding="utf-8",
            )

            (inputs_dir / "24_chap6_problems.tex").write_text(
                "\\subsection*{Problems}\\textbf{6.1.} Problem one.\\textbf{6.2.} Problem two.",
                encoding="utf-8",
            )
            (settings.plans_dir / "24_chap6_problems_plan.json").write_text(
                json.dumps(
                    [
                        {
                            "block_id": "prob_6_1",
                            "type": "Exercise",
                            "title": "Exercise",
                            "content": "Problem one.",
                            "dependencies": [],
                            "source_plan": "24_chap6_problems",
                        },
                        {
                            "block_id": "prob_6_2",
                            "type": "Exercise",
                            "title": "Exercise",
                            "content": "Problem two.",
                            "dependencies": [],
                            "source_plan": "24_chap6_problems",
                        },
                    ],
                    indent=2,
                    ensure_ascii=False,
                ),
                encoding="utf-8",
            )

            (inputs_dir / "13_chap5_independence_two_rv.tex").write_text(
                "Plain prose for a definition section.",
                encoding="utf-8",
            )
            (settings.plans_dir / "13_chap5_independence_two_rv_plan.json").write_text(
                json.dumps(
                    [
                        {
                            "block_id": "def_5_1",
                            "type": "Definition",
                            "title": "Independence",
                            "content": "Definition text.",
                            "dependencies": [],
                            "source_plan": "13_chap5_independence_two_rv",
                        }
                    ],
                    indent=2,
                    ensure_ascii=False,
                ),
                encoding="utf-8",
            )

            reports = audit_phase1_plans(
                plans_dir=settings.plans_dir,
                inputs_dir=inputs_dir,
                ledger_path=settings.project_ledger_file,
                stems=[
                    "13_chap5_independence_two_rv",
                    "17_chap5_model_kolmogorov",
                    "18_chap5_problems",
                    "24_chap6_problems",
                ],
            )
            by_plan = {report["source_plan"]: report for report in reports}

            self.assertEqual(by_plan["17_chap5_model_kolmogorov"]["status"], "error")
            self.assertEqual(by_plan["18_chap5_problems"]["status"], "error")
            self.assertEqual(by_plan["24_chap6_problems"]["status"], "warning")
            self.assertEqual(by_plan["13_chap5_independence_two_rv"]["status"], "ok")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_audit_phase1_script_emits_json_report(self):
        root = REPO_ROOT / "tests" / "_tmp_phase1_audit_script"
        try:
            shutil.rmtree(root, ignore_errors=True)
            plans_dir = root / "plans"
            inputs_dir = root / "inputs"
            plans_dir.mkdir(parents=True, exist_ok=True)
            inputs_dir.mkdir(parents=True, exist_ok=True)

            (inputs_dir / "17_chap5_model_kolmogorov.tex").write_text(
                "\\begin{theorem}Statement.\\end{theorem}\\begin{proof}Proof.\\end{proof}",
                encoding="utf-8",
            )
            (plans_dir / "17_chap5_model_kolmogorov_plan.json").write_text(
                json.dumps(
                    [
                        {
                            "block_id": "rem_5_5_kolmogorov_model",
                            "type": "Remark",
                            "title": "Text",
                            "content": "collapsed",
                            "dependencies": [],
                            "source_plan": "17_chap5_model_kolmogorov",
                        }
                    ],
                    indent=2,
                    ensure_ascii=False,
                ),
                encoding="utf-8",
            )
            ledger_path = root / "project_ledger.json"
            ledger_path.write_text(json.dumps({"tasks": {}, "symbols": {}}, indent=2), encoding="utf-8")

            result = subprocess.run(
                [
                    sys.executable,
                    str(REPO_ROOT / "tools" / "audit_phase1_plans.py"),
                    "--plans-dir",
                    str(plans_dir),
                    "--inputs-dir",
                    str(inputs_dir),
                    "--ledger",
                    str(ledger_path),
                    "--stems",
                    "17_chap5_model_kolmogorov",
                ],
                capture_output=True,
                text=True,
                cwd=str(REPO_ROOT),
                check=False,
            )

            self.assertEqual(result.returncode, 0, msg=result.stderr)
            payload = json.loads(result.stdout)
            self.assertEqual(len(payload["reports"]), 1)
            self.assertEqual(payload["reports"][0]["source_plan"], "17_chap5_model_kolmogorov")
            self.assertEqual(payload["reports"][0]["status"], "error")
        finally:
            shutil.rmtree(root, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
