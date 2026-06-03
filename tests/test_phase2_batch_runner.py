import asyncio
import json
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import AsyncMock, patch

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.toy_apollo.phase2_batch_controller import COMPLETED, NONTERMINAL  # noqa: E402
from src.toy_apollo.phase2_batch_runner import (  # noqa: E402
    build_live_batch_state,
    plan_batch_from_ledger,
    run_batch_actions,
)


class FakeLedger:
    def __init__(self, tasks):
        self.ledger = {"tasks": tasks}


class Phase2BatchRunnerTests(unittest.TestCase):
    def _settings(self, root: Path):
        output_dir = root / "ToyApollo" / "Output"
        output_dir.mkdir(parents=True)
        return SimpleNamespace(toyapollo_output_dir=output_dir)

    def test_completed_without_phase2_status_requires_fresh_existing_review(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            (settings.toyapollo_output_dir / "thm_1_1.lean").write_text("-- ok\n", encoding="utf-8")
            ledger = FakeLedger(
                {
                    "thm_1_1": {
                        "block_id": "thm_1_1",
                        "type": "Theorem",
                        "status": COMPLETED,
                    }
                }
            )

            plan = plan_batch_from_ledger(["thm_1_1"], ledger, settings)

        self.assertEqual(plan.actions[0].action, "review_existing")
        self.assertIn("--phase2-mode review-now", plan.actions[0].command)
        self.assertIn("--review-subject existing", plan.actions[0].command)
        self.assertEqual(plan.report.rows[0].report_status, "needs_fresh_review")

    def test_failed_task_routes_to_auto_loop(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            ledger = FakeLedger(
                {
                    "def_1_2": {
                        "block_id": "def_1_2",
                        "type": "Definition",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "missing Darboux tagged bridge",
                    }
                }
            )

            plan = plan_batch_from_ledger(["def_1_2"], ledger, settings)

        self.assertEqual(plan.actions[0].action, "auto_loop")
        self.assertIn("--phase2-mode auto-loop", plan.actions[0].command)
        self.assertIn("--tasks def_1_2", plan.actions[0].command)

    def test_blocked_downstream_is_skipped_until_root_repairs(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            ledger = FakeLedger(
                {
                    "root": {
                        "block_id": "root",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "phase2_status": "blocked",
                        "phase2_status_reason": "dependency gate",
                    },
                    "downstream": {
                        "block_id": "downstream",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "dependencies": ["root"],
                    },
                }
            )

            plan = plan_batch_from_ledger(["root", "downstream"], ledger, settings)

        actions = {action.task_id: action for action in plan.actions}
        self.assertEqual(actions["root"].action, "blocked")
        self.assertEqual(actions["downstream"].action, "skip_blocked")
        self.assertEqual(actions["downstream"].command, "")
        self.assertIn("root", actions["downstream"].reason)

    def test_live_batch_state_is_read_only_projection(self):
        ledger = FakeLedger(
            {
                "prob_11_6": {
                    "block_id": "prob_11_6",
                    "type": "Problem",
                    "status": COMPLETED,
                    "phase2_status": "pass",
                    "proof_class": "textbook_problem_completed",
                    "review_verdict": "pass",
                }
            }
        )

        state = build_live_batch_state(["prob_11_6"], ledger)

        self.assertEqual(state["batch_id"], "live-ledger")
        self.assertEqual(state["tasks"][0]["task_id"], "prob_11_6")
        self.assertEqual(state["tasks"][0]["phase2_status"], "pass")

    def test_batch_run_dispatches_only_bounded_executable_actions(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            ledger = FakeLedger(
                {
                    "def_1_2": {
                        "block_id": "def_1_2",
                        "type": "Definition",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "missing bridge",
                    },
                    "thm_1_1": {
                        "block_id": "thm_1_1",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "dependencies": ["def_1_2"],
                    },
                }
            )

            with patch(
                "src.toy_apollo.phase2_review_loop.run_codex_auto_loop",
                new=AsyncMock(return_value=(True, "advanced")),
            ) as auto_loop_mock:
                result = asyncio.run(run_batch_actions(["def_1_2", "thm_1_1"], ledger, settings, max_actions=1))

        auto_loop_mock.assert_awaited_once()
        self.assertEqual(len(result.executed), 1)
        self.assertEqual(result.executed[0].task_id, "def_1_2")

    def test_latest_verify_build_failure_routes_to_auto_loop(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            verify_path = root / "phase2_prompt_packs" / "def_1_4" / "verify_result_v1.json"
            verify_path.parent.mkdir(parents=True)
            verify_path.write_text(
                json.dumps(
                    {
                        "success": False,
                        "disposition": "review_existing_build_failed_no_review",
                        "primary_failure_kind": "unknown_identifier",
                        "diagnostics": [
                            {
                                "kind": "unknown_identifier",
                                "message": "Unknown identifier `RSCore.RSIntegral`",
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "def_1_4": {
                        "block_id": "def_1_4",
                        "type": "Definition",
                        "status": "PACKED",
                        "latest_verify_result_file": str(verify_path),
                    }
                }
            )

            plan = plan_batch_from_ledger(["def_1_4"], ledger, settings)

        self.assertEqual(plan.actions[0].action, "auto_loop")
        self.assertIn("--phase2-mode auto-loop", plan.actions[0].command)
        self.assertIn("unknown_identifier", plan.actions[0].reason)

    def test_worker_queue_prefers_non_problem_roots_by_fanout_and_limit(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            ledger = FakeLedger(
                {
                    "thm_low": {
                        "block_id": "thm_low",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                    },
                    "thm_high": {
                        "block_id": "thm_high",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                    },
                    "def_root": {
                        "block_id": "def_root",
                        "type": "Definition",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                    },
                    "prob_root": {
                        "block_id": "prob_root",
                        "type": "Problem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                    },
                    "downstream_a": {
                        "block_id": "downstream_a",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "dependencies": ["thm_high"],
                    },
                    "downstream_b": {
                        "block_id": "downstream_b",
                        "type": "Exercise",
                        "status": NONTERMINAL,
                        "dependencies": ["thm_high"],
                    },
                }
            )

            plan = plan_batch_from_ledger(
                ["thm_low", "thm_high", "def_root", "prob_root", "downstream_a", "downstream_b"],
                ledger,
                settings,
                task_kinds=["theorem", "definition"],
                limit=2,
                worker_slots=2,
            )

        self.assertEqual([action.task_id for action in plan.actions], ["thm_high", "def_root"])
        self.assertEqual(plan.actions[0].fanout, 2)
        self.assertEqual(plan.actions[0].worker_slot, 1)
        self.assertEqual(plan.actions[1].worker_slot, 2)
        self.assertEqual(plan.actions[0].conflict_group, "task:thm_high")


if __name__ == "__main__":
    unittest.main()
