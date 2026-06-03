import asyncio
import json
import sys
import shutil
import unittest
from argparse import Namespace
from pathlib import Path
from unittest.mock import patch

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.ledger_manager import LedgerManager, TaskStatus  # noqa: E402
from src.toy_apollo.cli import app as cli_app  # noqa: E402
from src.toy_apollo.core.settings import Settings  # noqa: E402
from src.toy_apollo.dependency_decisions import load_dependency_decisions  # noqa: E402
from src.toy_apollo.phase2_softdep_pack import apply_softdep_selection, write_softdep_pack  # noqa: E402


def removed_provider_module_names() -> tuple[str, str]:
    return (
        "src.toy_apollo.phase3_" + "execution_batches",
        "src.toy_apollo.integrations." + "offload" + "_" + "queue",
    )


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
        dependency_decisions_dir=root / "dependency_decisions",
    )


class Phase2SoftdepPackTests(unittest.TestCase):
    def test_phase2_cli_soft_pack_does_not_import_provider_modules(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_softdep_cli_import_boundary"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            settings = make_settings(root)
            settings.plans_dir.mkdir(parents=True, exist_ok=True)
            plan_payload = [
                {
                    "block_id": "def_4_3_sup_inf",
                    "type": "Definition",
                    "title": "sup and inf",
                    "content": "Define supremum and infimum notions.",
                },
                {
                    "block_id": "prob_4_2",
                    "type": "Problem",
                    "title": "abs measurable",
                    "content": "Show |f| is measurable.",
                    "dependencies": [],
                },
            ]
            (settings.plans_dir / "12_chap4_problems_plan.json").write_text(
                json.dumps(plan_payload, indent=2, ensure_ascii=False),
                encoding="utf-8",
            )
            ledger = LedgerManager(ledger_path=str(settings.project_ledger_file))
            for task in plan_payload:
                task = dict(task)
                task["source_plan"] = "12_chap4_problems"
                ledger.add_or_update_task(task)

            removed_modules = removed_provider_module_names()
            for module_name in list(sys.modules):
                if module_name in removed_modules or module_name.startswith("src.aristotle_"):
                    sys.modules.pop(module_name, None)

            args = Namespace(
                phase=2,
                input="",
                tasks="prob_4_2",
                task_ids=["prob_4_2"],
                phase2_mode="soft-pack",
                selection="",
                batch="",
                candidate="",
            )
            with patch.object(cli_app, "get_settings", return_value=settings):
                asyncio.run(cli_app.process_target(args))

            banned = [
                module_name
                for module_name in sys.modules
                if module_name in removed_modules or module_name.startswith("src.aristotle_")
            ]
            self.assertEqual([], banned)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_soft_imports_are_not_confirmed_without_soft_apply(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_softdep_no_auto_confirm"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            settings = make_settings(root)
            ledger = LedgerManager(ledger_path=str(settings.project_ledger_file))
            ledger.add_or_update_task(
                {
                    "block_id": "prob_4_2",
                    "type": "Problem",
                    "title": "abs measurable",
                    "content": "Show |f| is measurable.",
                    "source_plan": "test",
                    "dependencies": [],
                }
            )
            ledger.update_candidate_soft_imports("prob_4_2", ["def_4_3_sup_inf"])

            reloaded = LedgerManager(ledger_path=str(settings.project_ledger_file))

            self.assertFalse(reloaded.has_confirmed_soft_imports("prob_4_2"))
            self.assertEqual(
                reloaded.ledger["tasks"]["prob_4_2"]["candidate_snapshot"]["soft_imports"],
                ["def_4_3_sup_inf"],
            )
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_write_softdep_pack_and_apply_updates_ledger(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_softdep_pack"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            settings = make_settings(root)
            settings.plans_dir.mkdir(parents=True, exist_ok=True)
            plan_payload = [
                {
                    "block_id": "def_4_3_sup_inf",
                    "type": "Definition",
                    "title": "sup and inf",
                    "content": "Define supremum and infimum notions.",
                },
                {
                    "block_id": "thm_4_7",
                    "type": "Theorem",
                    "title": "measurable limsup liminf",
                    "content": "Measurability of sup and inf constructions.",
                },
                {
                    "block_id": "prob_4_2",
                    "type": "Problem",
                    "title": "abs measurable",
                    "content": "Show |f|, max(f,g), min(f,g) are measurable.",
                    "dependencies": [],
                },
                {
                    "block_id": "prob_4_4",
                    "type": "Problem",
                    "title": "complex scalar multiple",
                    "content": "Complex scalar multiple of a complex random variable.",
                    "dependencies": [],
                },
            ]
            (settings.plans_dir / "12_chap4_problems_plan.json").write_text(
                json.dumps(plan_payload, indent=2, ensure_ascii=False),
                encoding="utf-8",
            )
            ledger = LedgerManager(ledger_path=str(settings.project_ledger_file))
            for task in plan_payload:
                task = dict(task)
                task["source_plan"] = "12_chap4_problems"
                ledger.add_or_update_task(task)

            pack_dir = write_softdep_pack(["prob_4_2", "prob_4_4"], ledger, settings)
            self.assertTrue((pack_dir / "batch.json").exists())
            self.assertTrue((pack_dir / "chapter_materials.md").exists())
            self.assertTrue((pack_dir / "selection_hints.md").exists())
            allowed = json.loads((pack_dir / "allowed_material_ids.json").read_text(encoding="utf-8"))
            self.assertIn("def_4_3_sup_inf", allowed)
            self.assertIn("thm_4_7", allowed)
            hints = (pack_dir / "selection_hints.md").read_text(encoding="utf-8")
            self.assertIn("minimal but sufficient", hints.lower())
            self.assertIn("prob_4_2", hints)

            selection_path = root / "selection.json"
            selection_path.write_text(
                json.dumps(
                    {
                        "prob_4_2": ["def_4_3_sup_inf"],
                        "prob_4_4": ["thm_4_7", "def_4_3_sup_inf"],
                    },
                    indent=2,
                    ensure_ascii=False,
                ),
                encoding="utf-8",
            )
            rationale_path = pack_dir / "soft_imports_rationale.json"
            rationale_path.write_text(
                json.dumps(
                    {
                        "prob_4_2": {
                            "def_4_3_sup_inf": "Problem uses the limsup/liminf definition directly."
                        }
                    },
                    indent=2,
                    ensure_ascii=False,
                ),
                encoding="utf-8",
            )
            success, _, _ = apply_softdep_selection(["prob_4_2", "prob_4_4"], ledger, settings, str(selection_path))
            self.assertTrue(success)
            self.assertEqual(
                ledger.ledger["tasks"]["prob_4_2"]["candidate_snapshot"]["soft_imports"],
                ["def_4_3_sup_inf"],
            )
            self.assertEqual(
                ledger.ledger["tasks"]["prob_4_4"]["candidate_snapshot"]["soft_imports"],
                ["thm_4_7", "def_4_3_sup_inf"],
            )
            self.assertTrue(ledger.ledger["tasks"]["prob_4_2"]["soft_imports_confirmed_at"])
            self.assertTrue(ledger.ledger["tasks"]["prob_4_4"]["soft_imports_confirmed_at"])
            prob_4_2_decisions = load_dependency_decisions(settings, "prob_4_2")
            self.assertEqual(prob_4_2_decisions[0]["kind"], "soft")
            self.assertEqual(prob_4_2_decisions[0]["phase"], "phase2_soft_apply")
            self.assertEqual(prob_4_2_decisions[0]["criterion"], "soft_minimal_sufficient")
            self.assertEqual(
                prob_4_2_decisions[0]["evidence"],
                "Problem uses the limsup/liminf definition directly.",
            )
            prob_4_4_decisions = load_dependency_decisions(settings, "prob_4_4")
            self.assertIn("Selected in soft_imports_selection.json", {d["evidence"] for d in prob_4_4_decisions})
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_soft_apply_registers_unseen_problem_from_plan_before_confirming_selection(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_softdep_apply_registers_problem"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            settings = make_settings(root)
            settings.plans_dir.mkdir(parents=True, exist_ok=True)
            plan_payload = [
                {
                    "block_id": "def_4_3_sup_inf",
                    "type": "Definition",
                    "title": "sup and inf",
                    "content": "Define supremum and infimum notions.",
                },
                {
                    "block_id": "prob_4_2",
                    "type": "Problem",
                    "title": "abs measurable",
                    "content": "Show |f| is measurable.",
                    "dependencies": [],
                },
            ]
            (settings.plans_dir / "12_chap4_problems_plan.json").write_text(
                json.dumps(plan_payload, indent=2, ensure_ascii=False),
                encoding="utf-8",
            )
            ledger = LedgerManager(ledger_path=str(settings.project_ledger_file))

            pack_dir = write_softdep_pack(["prob_4_2"], ledger, settings)
            selection_path = pack_dir / "soft_imports_selection.json"
            success, _, _ = apply_softdep_selection(["prob_4_2"], ledger, settings, str(selection_path))

            self.assertTrue(success)
            self.assertIn("prob_4_2", ledger.ledger["tasks"])
            task = ledger.ledger["tasks"]["prob_4_2"]
            self.assertEqual(task["candidate_snapshot"]["soft_imports"], [])
            self.assertTrue(task["soft_imports_confirmed_at"])
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_write_softdep_pack_excludes_material_with_proof_debt(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_softdep_excludes_proof_debt"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            settings = make_settings(root)
            settings.plans_dir.mkdir(parents=True, exist_ok=True)
            plan_payload = [
                {
                    "block_id": "thm_4_7",
                    "type": "Theorem",
                    "title": "Debt-bearing theorem",
                    "content": "Theorem with accepted proof debt.",
                },
                {
                    "block_id": "def_4_3_sup_inf",
                    "type": "Definition",
                    "title": "sup and inf",
                    "content": "Clean definition.",
                },
                {
                    "block_id": "prob_4_2",
                    "type": "Problem",
                    "title": "abs measurable",
                    "content": "Show |f| is measurable.",
                    "dependencies": [],
                },
            ]
            (settings.plans_dir / "12_chap4_problems_plan.json").write_text(
                json.dumps(plan_payload, indent=2, ensure_ascii=False),
                encoding="utf-8",
            )
            ledger = LedgerManager(ledger_path=str(settings.project_ledger_file))
            for task in plan_payload:
                task = dict(task)
                task["source_plan"] = "12_chap4_problems"
                ledger.add_or_update_task(task)
            ledger.update_status("thm_4_7", TaskStatus.COMPLETED_WITH_PROOF_DEBT)
            ledger.update_runtime_metadata(
                "thm_4_7",
                proof_obligation_summary={"status_counts": {"proved": 2, "accepted_as_proof_debt": 1}},
            )

            pack_dir = write_softdep_pack(["prob_4_2"], ledger, settings)

            allowed = json.loads((pack_dir / "allowed_material_ids.json").read_text(encoding="utf-8"))
            blocked = json.loads((pack_dir / "blocked_material_ids.json").read_text(encoding="utf-8"))
            self.assertNotIn("thm_4_7", allowed)
            self.assertIn("def_4_3_sup_inf", allowed)
            self.assertIn("thm_4_7", blocked)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_soft_apply_rejects_selection_when_material_became_proof_debt(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_softdep_rejects_stale_proof_debt"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            settings = make_settings(root)
            settings.plans_dir.mkdir(parents=True, exist_ok=True)
            plan_payload = [
                {
                    "block_id": "thm_4_7",
                    "type": "Theorem",
                    "title": "measurable limsup liminf",
                    "content": "Measurability theorem.",
                },
                {
                    "block_id": "prob_4_2",
                    "type": "Problem",
                    "title": "abs measurable",
                    "content": "Show |f| is measurable.",
                    "dependencies": [],
                },
            ]
            (settings.plans_dir / "12_chap4_problems_plan.json").write_text(
                json.dumps(plan_payload, indent=2, ensure_ascii=False),
                encoding="utf-8",
            )
            ledger = LedgerManager(ledger_path=str(settings.project_ledger_file))
            for task in plan_payload:
                task = dict(task)
                task["source_plan"] = "12_chap4_problems"
                ledger.add_or_update_task(task)
            pack_dir = write_softdep_pack(["prob_4_2"], ledger, settings)
            ledger.update_status("thm_4_7", TaskStatus.COMPLETED_WITH_PROOF_DEBT)
            ledger.update_runtime_metadata(
                "thm_4_7",
                proof_obligation_summary={"status_counts": {"proved": 2, "accepted_as_proof_debt": 1}},
            )
            selection_path = root / "selection.json"
            selection_path.write_text(json.dumps({"prob_4_2": ["thm_4_7"]}, indent=2), encoding="utf-8")

            with self.assertRaisesRegex(ValueError, "thm_4_7.*proof debt"):
                apply_softdep_selection(["prob_4_2"], ledger, settings, str(selection_path))
            self.assertTrue((pack_dir / "allowed_material_ids.json").exists())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_write_softdep_pack_includes_theorem_statement_and_with_proof_materials(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_softdep_theorem_family"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            settings = make_settings(root)
            settings.plans_dir.mkdir(parents=True, exist_ok=True)
            plan_payload = [
                {
                    "block_id": "thm_3_2",
                    "type": "Theorem_with_Proof",
                    "title": "Properties of distribution function",
                    "content": "The theorem has a proof in the textbook.",
                },
                {
                    "block_id": "thm_3_3",
                    "type": "Theorem_Statement",
                    "title": "Lebesgue-Stieltjes measure",
                    "content": "The theorem is stated without proof in the textbook section.",
                },
                {
                    "block_id": "def_3_5",
                    "type": "Definition",
                    "title": "Stieltjes measure function",
                    "content": "Definition 3.5.",
                },
                {
                    "block_id": "prob_3_1",
                    "type": "Problem",
                    "title": "Problem 3.1",
                    "content": "Use chapter 3 materials.",
                    "dependencies": [],
                },
            ]
            (settings.plans_dir / "07_chap3_problems_plan.json").write_text(
                json.dumps(plan_payload, indent=2, ensure_ascii=False),
                encoding="utf-8",
            )
            ledger = LedgerManager(ledger_path=str(settings.project_ledger_file))
            for task in plan_payload:
                task = dict(task)
                task["source_plan"] = "07_chap3_problems"
                ledger.add_or_update_task(task)

            pack_dir = write_softdep_pack(["prob_3_1"], ledger, settings)
            allowed = json.loads((pack_dir / "allowed_material_ids.json").read_text(encoding="utf-8"))
            self.assertIn("def_3_5", allowed)
            self.assertIn("thm_3_2", allowed)
            self.assertIn("thm_3_3", allowed)
        finally:
            shutil.rmtree(root, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
