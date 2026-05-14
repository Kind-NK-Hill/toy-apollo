import json
import shutil
import sys
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.ledger_manager import LedgerManager, TaskStatus  # noqa: E402


class LedgerManagerSafetyTests(unittest.TestCase):
    def test_save_keeps_json_parseable_and_writes_recoverable_backup(self):
        root = REPO_ROOT / "tests" / "_tmp_ledger_backup_recovery"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            root.mkdir(parents=True, exist_ok=True)

            ledger_path = root / "project_ledger.json"
            ledger = LedgerManager(ledger_path=str(ledger_path))
            ledger.add_or_update_task(
                {
                    "block_id": "task_a",
                    "type": "Theorem",
                    "title": "Task A",
                    "content": "A",
                    "source_plan": "plan_a",
                    "dependencies": [],
                }
            )
            original = json.loads(ledger_path.read_text(encoding="utf-8"))

            ledger.update_status("task_a", TaskStatus.LOCAL_FIXING)

            current = json.loads(ledger_path.read_text(encoding="utf-8"))
            self.assertEqual(current["tasks"]["task_a"]["status"], TaskStatus.LOCAL_FIXING.value)

            backup_path = ledger.backup_path
            self.assertTrue(backup_path.exists())
            backup = json.loads(backup_path.read_text(encoding="utf-8"))
            self.assertEqual(backup, original)
            self.assertGreater(len(backup["tasks"]), 0)

            ledger_path.write_text("{ definitely not valid json", encoding="utf-8")
            restored = ledger.recover_from_backup()
            self.assertTrue(restored)
            self.assertEqual(ledger.ledger["tasks"]["task_a"]["status"], TaskStatus.DISCOVERED.value)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_save_does_not_overwrite_non_empty_disk_ledger_from_empty_memory_state(self):
        root = REPO_ROOT / "tests" / "_tmp_ledger_empty_overwrite"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            root.mkdir(parents=True, exist_ok=True)

            ledger_path = root / "project_ledger.json"
            ledger_path.write_text(
                json.dumps(
                    {
                        "tasks": {
                            "thm_4_3": {
                                "block_id": "thm_4_3",
                                "status": TaskStatus.COMPLETED.value,
                                "source_plan": "10_chap4_operations",
                            }
                        },
                        "symbols": {"thm_4_3": "thm_4_3"},
                    },
                    indent=2,
                    ensure_ascii=False,
                ),
                encoding="utf-8",
            )

            ledger = LedgerManager(ledger_path=str(ledger_path))
            ledger.ledger = {"tasks": {}, "symbols": {}}

            try:
                ledger.save()
            except Exception:
                pass

            persisted = json.loads(ledger_path.read_text(encoding="utf-8"))
            self.assertIn("thm_4_3", persisted["tasks"])
            self.assertEqual(persisted["tasks"]["thm_4_3"]["status"], TaskStatus.COMPLETED.value)
            self.assertEqual(persisted["symbols"]["thm_4_3"], "thm_4_3")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_stale_writer_does_not_clobber_parallel_updates(self):
        root = REPO_ROOT / "tests" / "_tmp_ledger_stale_writer"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            root.mkdir(parents=True, exist_ok=True)

            ledger_path = root / "project_ledger.json"
            writer_a = LedgerManager(ledger_path=str(ledger_path))
            writer_a.add_or_update_task(
                {
                    "block_id": "task_a",
                    "type": "Theorem",
                    "title": "Task A",
                    "content": "A",
                    "source_plan": "plan_a",
                    "dependencies": [],
                }
            )

            writer_b = LedgerManager(ledger_path=str(ledger_path))
            writer_b.add_or_update_task(
                {
                    "block_id": "task_b",
                    "type": "Theorem",
                    "title": "Task B",
                    "content": "B",
                    "source_plan": "plan_b",
                    "dependencies": [],
                }
            )

            try:
                writer_a.update_status("task_a", TaskStatus.LOCAL_FIXING)
            except Exception:
                pass

            persisted = LedgerManager(ledger_path=str(ledger_path)).ledger
            self.assertIn("task_a", persisted["tasks"])
            self.assertIn("task_b", persisted["tasks"])
            self.assertEqual(persisted["tasks"]["task_b"]["source_plan"], "plan_b")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_parallel_writers_merge_distinct_task_updates_without_error(self):
        root = REPO_ROOT / "tests" / "_tmp_ledger_parallel_merge"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            root.mkdir(parents=True, exist_ok=True)

            ledger_path = root / "project_ledger.json"
            writer_a = LedgerManager(ledger_path=str(ledger_path))
            writer_a.add_or_update_task(
                {
                    "block_id": "task_a",
                    "type": "Theorem",
                    "title": "Task A",
                    "content": "A",
                    "source_plan": "plan_a",
                    "dependencies": [],
                }
            )

            writer_b = LedgerManager(ledger_path=str(ledger_path))
            writer_b.add_or_update_task(
                {
                    "block_id": "task_b",
                    "type": "Theorem",
                    "title": "Task B",
                    "content": "B",
                    "source_plan": "plan_b",
                    "dependencies": [],
                }
            )

            writer_a.update_status("task_a", TaskStatus.LOCAL_FIXING)

            persisted = LedgerManager(ledger_path=str(ledger_path)).ledger
            self.assertEqual(persisted["tasks"]["task_a"]["status"], TaskStatus.LOCAL_FIXING.value)
            self.assertIn("task_b", persisted["tasks"])
            self.assertEqual(persisted["tasks"]["task_b"]["source_plan"], "plan_b")
        finally:
            shutil.rmtree(root, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
