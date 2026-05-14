import json
import sys
import shutil
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.ledger_manager import LedgerManager, TaskStatus  # noqa: E402
from src.toy_apollo.core.settings import Settings  # noqa: E402
from src.toy_apollo.phase3_execution_batches import (  # noqa: E402
    resolve_batch_plan,
    task_ids_for_batch,
    write_execution_batch_plan,
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
        error_logs_dir=root / "error_logs",
        toyapollo_output_dir=root / "ToyApollo" / "Output",
        aristotle_outbox_dir=root / "aristotle_outbox",
        aristotle_archives_dir=root / "aristotle_archives",
        mathlib_index_file=root / "mathlib_index.faiss",
        mathlib_corpus_file=root / "mathlib_corpus.json",
        project_ledger_file=root / "project_ledger.json",
        lab_notebook_file=root / "lab_notebook.json",
        mathlib_path=root / ".lake" / "packages" / "mathlib" / "Mathlib",
        phase3_execution_batches_dir=root / "phase3_execution_batches",
    )


class Phase3ExecutionBatchTests(unittest.TestCase):
    def test_plan_batches_groups_independent_problems_together(self):
        root = REPO_ROOT / "tests" / "_tmp_phase3_execution_batches_same_batch"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            settings = make_settings(root)
            settings.plans_dir.mkdir(parents=True, exist_ok=True)
            plan_payload = [
                {"block_id": "def_4_3_sup_inf", "type": "Definition", "title": "sup", "content": "Definition."},
                {"block_id": "prob_4_2", "type": "Problem", "title": "p1", "content": "Problem 1", "dependencies": []},
                {"block_id": "prob_4_4", "type": "Problem", "title": "p2", "content": "Problem 2", "dependencies": []},
            ]
            (settings.plans_dir / "12_chap4_problems_plan.json").write_text(
                json.dumps(plan_payload, indent=2, ensure_ascii=False), encoding="utf-8"
            )
            ledger = LedgerManager(ledger_path=str(settings.project_ledger_file))
            for task in plan_payload:
                payload = dict(task)
                payload["source_plan"] = "12_chap4_problems"
                ledger.add_or_update_task(payload)
            ledger.update_status("def_4_3_sup_inf", TaskStatus.COMPLETED)
            ledger.mark_soft_imports_confirmed("prob_4_2", [])
            ledger.mark_soft_imports_confirmed("prob_4_4", [])

            plan_dir = write_execution_batch_plan(["prob_4_2", "prob_4_4"], ledger, settings)
            payload = json.loads((plan_dir / "batch_plan.json").read_text(encoding="utf-8"))
            self.assertEqual(len(payload["batches"]), 1)
            batch_tasks = [item["task_id"] for item in payload["batches"][0]["tasks"]]
            self.assertEqual(batch_tasks, ["prob_4_2", "prob_4_4"])
            self.assertEqual(payload["unscheduled"], [])
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_plan_batches_topologically_layers_problem_dependencies(self):
        root = REPO_ROOT / "tests" / "_tmp_phase3_execution_batches_layers"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            settings = make_settings(root)
            settings.plans_dir.mkdir(parents=True, exist_ok=True)
            plan_payload = [
                {"block_id": "def_5_1", "type": "Definition", "title": "base", "content": "Definition."},
                {"block_id": "prob_5_1", "type": "Problem", "title": "first", "content": "Problem 1", "dependencies": []},
                {
                    "block_id": "prob_5_2",
                    "type": "Problem",
                    "title": "second",
                    "content": "Problem 2",
                    "dependencies": ["prob_5_1"],
                },
            ]
            (settings.plans_dir / "13_chap5_problems_plan.json").write_text(
                json.dumps(plan_payload, indent=2, ensure_ascii=False), encoding="utf-8"
            )
            ledger = LedgerManager(ledger_path=str(settings.project_ledger_file))
            for task in plan_payload:
                payload = dict(task)
                payload["source_plan"] = "13_chap5_problems"
                ledger.add_or_update_task(payload)
            ledger.update_status("def_5_1", TaskStatus.COMPLETED)
            ledger.mark_soft_imports_confirmed("prob_5_1", [])
            ledger.mark_soft_imports_confirmed("prob_5_2", [])

            plan_dir = write_execution_batch_plan(["prob_5_1", "prob_5_2"], ledger, settings)
            payload = json.loads((plan_dir / "batch_plan.json").read_text(encoding="utf-8"))
            self.assertEqual(len(payload["batches"]), 2)
            self.assertEqual([item["task_id"] for item in payload["batches"][0]["tasks"]], ["prob_5_1"])
            self.assertEqual([item["task_id"] for item in payload["batches"][1]["tasks"]], ["prob_5_2"])
            _, batch_task_ids, batch_id = task_ids_for_batch(payload["batches"][1]["batch_id"], settings)
            self.assertEqual(batch_task_ids, ["prob_5_2"])
            self.assertTrue(batch_id.endswith("__batch_2"))
            _, _, matched_batch = resolve_batch_plan(payload["batches"][0]["batch_id"], settings)
            self.assertEqual(matched_batch["tasks"][0]["task_id"], "prob_5_1")
        finally:
            shutil.rmtree(root, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
