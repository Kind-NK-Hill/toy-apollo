import asyncio
import json
import shutil
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.ledger_manager import LedgerManager, TaskStatus  # noqa: E402
from src.toy_apollo.cli.app import step3_aristotle_offload  # noqa: E402


class Phase3OffloadFlowTests(unittest.TestCase):
    def _setup_problem_tasks(
        self,
        root: Path,
        statuses: dict[str, TaskStatus],
        *,
        confirm_soft_imports: bool = True,
    ) -> LedgerManager:
        plans_dir = root / "plans"
        plans_dir.mkdir(parents=True, exist_ok=True)
        plan_payload = []
        for task_id in sorted(statuses):
            plan_payload.append(
                {
                    "block_id": task_id,
                    "type": "Problem",
                    "title": task_id,
                    "content": f"Content for {task_id}.",
                    "dependencies": [],
                }
            )
        (plans_dir / "39_chap1_problems_plan.json").write_text(
            json.dumps(plan_payload, indent=2, ensure_ascii=False),
            encoding="utf-8",
        )

        ledger = LedgerManager(ledger_path=str(root / "project_ledger.json"))
        for task in plan_payload:
            payload = dict(task)
            payload["source_plan"] = "39_chap1_problems"
            ledger.add_or_update_task(payload)
            ledger.update_status(payload["block_id"], statuses[payload["block_id"]])
            if confirm_soft_imports:
                ledger.mark_soft_imports_confirmed(payload["block_id"], [])
            if statuses[payload["block_id"]] == TaskStatus.OFFLOADED:
                ledger.update_runtime_metadata(payload["block_id"], cloud_project_id=f"cloud-{payload['block_id']}")
        return ledger

    def test_offload_batch_submits_all_tasks_before_harvesting(self):
        root = REPO_ROOT / "tests" / "_tmp_phase3_offload_submit_then_harvest"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            ledger = self._setup_problem_tasks(
                root,
                {
                    "prob_1_1": TaskStatus.PACKED,
                    "prob_1_2": TaskStatus.PACKED,
                },
            )
            events: list[str] = []

            class FakeOffloader:
                def __init__(self) -> None:
                    self.outbox_root = root / "aristotle_outbox" / "direct_test"

                async def prepare_package(self, candidate):
                    task_id = candidate["block_id"]
                    events.append(f"prepare:{task_id}")
                    (self.outbox_root / task_id).mkdir(parents=True, exist_ok=True)

            class FakeManager:
                async def submit_offload(self, task_id, staging_dir, prompt=None):
                    del staging_dir, prompt
                    events.append(f"submit:{task_id}")
                    return {"success": True, "cloud_project_id": f"cloud-{task_id}", "error": ""}

                async def harvest_offload(self, task_id, project_id):
                    events.append(f"harvest:{task_id}:{project_id}")
                    return {"success": True, "cloud_project_id": project_id, "error": ""}

            with patch("src.toy_apollo.integrations.AristotleDirectOffloader", return_value=FakeOffloader()), patch(
                "src.toy_apollo.integrations.AristotlePhase3Manager",
                return_value=FakeManager(),
            ):
                asyncio.run(
                    step3_aristotle_offload(
                        ledger,
                        plans_dir=root / "plans",
                        explicit_task_ids=["prob_1_1", "prob_1_2"],
                    )
                )

            submit_indices = [idx for idx, event in enumerate(events) if event.startswith("submit:")]
            harvest_indices = [idx for idx, event in enumerate(events) if event.startswith("harvest:")]
            self.assertEqual(len(submit_indices), 2)
            self.assertEqual(len(harvest_indices), 2)
            self.assertLess(max(submit_indices), min(harvest_indices))
            self.assertEqual(ledger.ledger["tasks"]["prob_1_1"]["status"], TaskStatus.HARVESTED.value)
            self.assertEqual(ledger.ledger["tasks"]["prob_1_2"]["status"], TaskStatus.HARVESTED.value)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_offload_batch_reuses_existing_cloud_project_ids_for_offloaded_tasks(self):
        root = REPO_ROOT / "tests" / "_tmp_phase3_offload_reuse_existing_project"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            ledger = self._setup_problem_tasks(
                root,
                {
                    "prob_1_1": TaskStatus.OFFLOADED,
                    "prob_1_2": TaskStatus.PACKED,
                },
            )
            events: list[str] = []

            class FakeOffloader:
                def __init__(self) -> None:
                    self.outbox_root = root / "aristotle_outbox" / "direct_test"

                async def prepare_package(self, candidate):
                    task_id = candidate["block_id"]
                    events.append(f"prepare:{task_id}")
                    (self.outbox_root / task_id).mkdir(parents=True, exist_ok=True)

            class FakeManager:
                async def submit_offload(self, task_id, staging_dir, prompt=None):
                    del staging_dir, prompt
                    events.append(f"submit:{task_id}")
                    return {"success": True, "cloud_project_id": f"cloud-{task_id}", "error": ""}

                async def harvest_offload(self, task_id, project_id):
                    events.append(f"harvest:{task_id}:{project_id}")
                    return {"success": True, "cloud_project_id": project_id, "error": ""}

            with patch("src.toy_apollo.integrations.AristotleDirectOffloader", return_value=FakeOffloader()), patch(
                "src.toy_apollo.integrations.AristotlePhase3Manager",
                return_value=FakeManager(),
            ):
                asyncio.run(
                    step3_aristotle_offload(
                        ledger,
                        plans_dir=root / "plans",
                        explicit_task_ids=["prob_1_1", "prob_1_2"],
                    )
                )

            self.assertNotIn("submit:prob_1_1", events)
            self.assertIn("submit:prob_1_2", events)
            self.assertIn("harvest:prob_1_1:cloud-prob_1_1", events)
            self.assertIn("harvest:prob_1_2:cloud-prob_1_2", events)
            self.assertEqual(ledger.ledger["tasks"]["prob_1_1"]["status"], TaskStatus.HARVESTED.value)
            self.assertEqual(ledger.ledger["tasks"]["prob_1_2"]["status"], TaskStatus.HARVESTED.value)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_problem_without_confirmed_soft_imports_is_not_submitted(self):
        root = REPO_ROOT / "tests" / "_tmp_phase3_offload_requires_soft_confirmation"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            ledger = self._setup_problem_tasks(
                root,
                {"prob_1_1": TaskStatus.PACKED},
                confirm_soft_imports=False,
            )
            events: list[str] = []

            class FakeOffloader:
                def __init__(self) -> None:
                    self.outbox_root = root / "aristotle_outbox" / "direct_test"

                async def prepare_package(self, candidate):
                    events.append(f"prepare:{candidate['block_id']}")

            class FakeManager:
                async def submit_offload(self, task_id, staging_dir, prompt=None):
                    del staging_dir, prompt
                    events.append(f"submit:{task_id}")
                    return {"success": True, "cloud_project_id": f"cloud-{task_id}", "error": ""}

                async def harvest_offload(self, task_id, project_id):
                    del project_id
                    events.append(f"harvest:{task_id}")
                    return {"success": True, "error": ""}

            with patch("src.toy_apollo.integrations.AristotleDirectOffloader", return_value=FakeOffloader()), patch(
                "src.toy_apollo.integrations.AristotlePhase3Manager",
                return_value=FakeManager(),
            ):
                asyncio.run(
                    step3_aristotle_offload(
                        ledger,
                        plans_dir=root / "plans",
                        explicit_task_ids=["prob_1_1"],
                    )
                )

            self.assertEqual(events, [])
            record = ledger.ledger["tasks"]["prob_1_1"]
            self.assertEqual(record["status"], TaskStatus.FAILED_LOCAL.value)
            self.assertIn("missing_soft_imports_selection", record["last_offload_error"])
        finally:
            shutil.rmtree(root, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
