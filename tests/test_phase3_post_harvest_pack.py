import asyncio
import json
import shutil
import sys
import unittest
from pathlib import Path
from unittest.mock import AsyncMock, patch

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.ledger_manager import LedgerManager, TaskStatus  # noqa: E402
from src.toy_apollo.core.settings import Settings  # noqa: E402
from src.toy_apollo.phase3_post_harvest_pack import (  # noqa: E402
    classify_post_harvest_failure,
    verify_repair_candidate,
    write_repair_pack,
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
        phase3_softdep_packs_dir=root / "phase3_softdep_packs",
        phase3_execution_batches_dir=root / "phase3_execution_batches",
        phase3_post_harvest_packs_dir=root / "phase3_post_harvest_packs",
        error_logs_dir=root / "error_logs",
        toyapollo_output_dir=root / "ToyApollo" / "Output",
        aristotle_outbox_dir=root / "aristotle_outbox",
        aristotle_archives_dir=root / "aristotle_archives",
        mathlib_index_file=root / "mathlib_index.faiss",
        mathlib_corpus_file=root / "mathlib_corpus.json",
        project_ledger_file=root / "project_ledger.json",
        lab_notebook_file=root / "lab_notebook.json",
        mathlib_path=root / ".lake" / "packages" / "mathlib" / "Mathlib",
    )


class Phase3PostHarvestPackTests(unittest.TestCase):
    def _setup_task(
        self,
        root: Path,
        *,
        task_id: str,
        staged_code: str,
        raw_code: str,
        status: TaskStatus = TaskStatus.FAILED_LOCAL,
    ) -> tuple[Settings, LedgerManager]:
        settings = make_settings(root)
        settings.plans_dir.mkdir(parents=True, exist_ok=True)
        settings.toyapollo_output_dir.mkdir(parents=True, exist_ok=True)
        (settings.plans_dir / "12_chap4_problems_plan.json").write_text(
            json.dumps(
                [
                    {
                        "block_id": task_id,
                        "type": "Problem",
                        "title": task_id,
                        "content": f"Content for {task_id}.",
                        "dependencies": ["def_4_3_limsup_liminf"],
                    },
                    {
                        "block_id": "def_4_3_limsup_liminf",
                        "type": "Definition",
                        "title": "seq limsup",
                        "content": "Definition.",
                    },
                ],
                indent=2,
                ensure_ascii=False,
            ),
            encoding="utf-8",
        )
        ledger = LedgerManager(ledger_path=str(settings.project_ledger_file))
        ledger.add_or_update_task(
            {
                "block_id": task_id,
                "type": "Problem",
                "title": task_id,
                "content": f"Content for {task_id}.",
                "source_plan": "12_chap4_problems",
                "dependencies": ["def_4_3_limsup_liminf"],
            }
        )
        ledger.add_or_update_task(
            {
                "block_id": "def_4_3_limsup_liminf",
                "type": "Definition",
                "title": "seq limsup",
                "content": "Definition.",
                "source_plan": "10_chap4_operations",
                "dependencies": [],
            }
        )
        ledger.update_status("def_4_3_limsup_liminf", TaskStatus.COMPLETED)
        ledger.mark_soft_imports_confirmed(task_id, ["def_4_3_limsup_liminf"])
        ledger.update_status(task_id, status)

        staged_path = settings.aristotle_outbox_dir / "direct_123" / task_id / "ToyApollo" / "Output"
        staged_path.mkdir(parents=True, exist_ok=True)
        (staged_path / f"{task_id}.lean").write_text(staged_code, encoding="utf-8")

        raw_path = settings.aristotle_archives_dir / task_id / "raw"
        raw_path.mkdir(parents=True, exist_ok=True)
        (raw_path / f"{task_id}.lean").write_text(raw_code, encoding="utf-8")

        verify_dir = settings.aristotle_archives_dir / task_id / "verification"
        verify_dir.mkdir(parents=True, exist_ok=True)
        (verify_dir / f"{task_id}_phase3_lake_build.log").write_text(
            "unsolved goals remain",
            encoding="utf-8",
        )

        summary_dir = settings.aristotle_archives_dir / task_id / "extracted" / f"{task_id}_aristotle"
        summary_dir.mkdir(parents=True, exist_ok=True)
        (summary_dir / "ARISTOTLE_SUMMARY_demo.md").write_text(
            "Summary content.",
            encoding="utf-8",
        )
        return settings, ledger

    def test_classify_statement_drift_when_theorem_header_changes(self):
        root = REPO_ROOT / "tests" / "_tmp_phase3_post_harvest_statement_drift"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            settings, _ = self._setup_task(
                root,
                task_id="prob_4_11",
                staged_code=(
                    "import Mathlib\n\n"
                    "theorem prob_4_11 (a : ℕ → ℝ) (h_nonneg : ∀ k, 0 <= a k) "
                    "(h_limsup : seqLimsup a = 0) : True := by\n  sorry\n"
                ),
                raw_code=(
                    "import Mathlib\n\n"
                    "theorem prob_4_11 (a : ℕ → ℝ) (h_nonneg : ∀ k, 0 <= a k) "
                    "(hb : IsBoundedUnder (· ≤ ·) atTop a) (h_limsup : Filter.limsup a atTop = 0) : True := by\n"
                    "  trivial\n"
                ),
            )
            classification = classify_post_harvest_failure("prob_4_11", settings)
            self.assertEqual(classification["failure_type"], "statement_drift")
            self.assertIn("IsBoundedUnder", classification["raw_header"])
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_write_repair_pack_for_proof_incomplete_task(self):
        root = REPO_ROOT / "tests" / "_tmp_phase3_post_harvest_proof_incomplete"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            settings, ledger = self._setup_task(
                root,
                task_id="prob_4_8",
                staged_code=(
                    "import Mathlib\n\n"
                    "theorem prob_4_8 : True := by\n  sorry\n"
                ),
                raw_code=(
                    "import Mathlib\n\n"
                    "theorem prob_4_8 : True := by\n"
                    "  have h : True := by trivial\n"
                    "  exact h\n"
                ),
            )
            pack_dir = write_repair_pack("prob_4_8", ledger, settings)
            self.assertTrue((pack_dir / "task.json").exists())
            self.assertTrue((pack_dir / "metadata.json").exists())
            self.assertTrue((pack_dir / "operator_prompt.md").exists())
            self.assertTrue((pack_dir / "context.md").exists())
            self.assertTrue((pack_dir / "raw_candidate.lean").exists())
            context = (pack_dir / "context.md").read_text(encoding="utf-8")
            self.assertIn("proof_incomplete", context)
            self.assertIn("def_4_3_limsup_liminf", context)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_classify_ignores_cosmetic_namespace_qualification_drift(self):
        root = REPO_ROOT / "tests" / "_tmp_phase3_post_harvest_cosmetic_header_drift"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            settings, _ = self._setup_task(
                root,
                task_id="prob_4_8",
                staged_code=(
                    "import Mathlib\n\n"
                    "theorem prob_4_8 : limsup (fun n => (seq1 n : EReal)) atTop = (Real.sin (π / 3) : EReal) := by\n"
                    "  sorry\n"
                ),
                raw_code=(
                    "import Mathlib\n\n"
                    "theorem prob_4_8 : limsup (fun n => (seq1 n : EReal)) atTop = (sin (π / 3) : EReal) := by\n"
                    "  trivial\n"
                ),
            )
            classification = classify_post_harvest_failure("prob_4_8", settings)
            self.assertEqual(classification["failure_type"], "proof_incomplete")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_repair_verify_blocks_statement_drift(self):
        root = REPO_ROOT / "tests" / "_tmp_phase3_post_harvest_verify_blocks_drift"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            settings, ledger = self._setup_task(
                root,
                task_id="prob_4_11",
                staged_code="import Mathlib\n\ntheorem prob_4_11 : True := by\n  sorry\n",
                raw_code="import Mathlib\n\ntheorem prob_4_11 (hb : True) : True := by\n  trivial\n",
            )
            write_repair_pack("prob_4_11", ledger, settings)
            success, detail = asyncio.run(verify_repair_candidate("prob_4_11", ledger, settings))
            self.assertFalse(success)
            self.assertIn("statement_drift", detail)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_repair_verify_allows_reconciled_statement_drift(self):
        root = REPO_ROOT / "tests" / "_tmp_phase3_post_harvest_verify_reconciled_drift"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            settings, ledger = self._setup_task(
                root,
                task_id="prob_4_11",
                staged_code="import Mathlib\n\ntheorem prob_4_11 : True := by\n  sorry\n",
                raw_code="import Mathlib\n\ntheorem prob_4_11 (hb : True) : True := by\n  trivial\n",
            )
            pack_dir = write_repair_pack("prob_4_11", ledger, settings)
            chosen_header = "theorem prob_4_11 : True"
            metadata_path = pack_dir / "metadata.json"
            metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
            metadata["chosen_reconciled_header"] = chosen_header
            metadata["statement_reconciled_at"] = "2026-04-06T00:00:00Z"
            metadata_path.write_text(json.dumps(metadata, indent=2, ensure_ascii=False), encoding="utf-8")
            (pack_dir / "draft.lean").write_text(
                "import Mathlib\n\ntheorem prob_4_11 : True := by\n  trivial\n",
                encoding="utf-8",
            )

            with patch(
                "src.toy_apollo.phase3_post_harvest_pack.LeanCompiler.validate_with_repl_async",
                new=AsyncMock(return_value=(True, "ok")),
            ), patch(
                "src.toy_apollo.phase3_post_harvest_pack.LeanCompiler.build_module_async",
                new=AsyncMock(side_effect=[(True, "temp ok"), (True, "final ok")]),
            ):
                success, _ = asyncio.run(verify_repair_candidate("prob_4_11", ledger, settings))

            self.assertTrue(success)
            self.assertEqual(ledger.ledger["tasks"]["prob_4_11"]["status"], TaskStatus.COMPLETED.value)
            self.assertTrue((pack_dir / "candidate_v1.lean").exists())
            self.assertTrue((pack_dir / "verify_result_v1.json").exists())
            context = (pack_dir / "context.md").read_text(encoding="utf-8")
            self.assertIn("Chosen reconciled header", context)
            self.assertIn(chosen_header, context)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_repair_verify_promotes_successful_candidate(self):
        root = REPO_ROOT / "tests" / "_tmp_phase3_post_harvest_verify_success"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            settings, ledger = self._setup_task(
                root,
                task_id="prob_4_8",
                staged_code="import Mathlib\n\ntheorem prob_4_8 : True := by\n  sorry\n",
                raw_code="import Mathlib\n\ntheorem prob_4_8 : True := by\n  trivial\n",
            )
            pack_dir = write_repair_pack("prob_4_8", ledger, settings)
            (pack_dir / "draft.lean").write_text(
                "import Mathlib\n\ntheorem prob_4_8 : True := by\n  trivial\n",
                encoding="utf-8",
            )

            with patch(
                "src.toy_apollo.phase3_post_harvest_pack.LeanCompiler.validate_with_repl_async",
                new=AsyncMock(return_value=(True, "ok")),
            ), patch(
                "src.toy_apollo.phase3_post_harvest_pack.LeanCompiler.build_module_async",
                new=AsyncMock(side_effect=[(True, "temp ok"), (True, "final ok")]),
            ):
                success, _ = asyncio.run(verify_repair_candidate("prob_4_8", ledger, settings))

            self.assertTrue(success)
            self.assertEqual(ledger.ledger["tasks"]["prob_4_8"]["status"], TaskStatus.COMPLETED.value)
            self.assertTrue((pack_dir / "candidate_v1.lean").exists())
            self.assertTrue((pack_dir / "verify_result_v1.json").exists())
            self.assertTrue((settings.toyapollo_output_dir / "prob_4_8.lean").exists())
        finally:
            shutil.rmtree(root, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
