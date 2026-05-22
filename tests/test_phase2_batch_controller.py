import json
import shutil
import subprocess
import sys
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.toy_apollo.phase2_batch_controller import (  # noqa: E402
    COMPLETED_WITH_PROOF_DEBT,
    DEPENDENCY_FAILED,
    DEPENDENCY_PROOF_DEBT,
    FAILED_LOCAL,
    NEEDS_DECOMPOSITION,
    NONTERMINAL,
    analyze_batch_state,
    count_substantive_failures,
)


class Phase2BatchControllerTests(unittest.TestCase):
    def test_dependency_failed_propagates_transitively_and_keeps_independent_nonterminal(self):
        report = analyze_batch_state(
            {
                "batch_id": "fixture",
                "tasks": [
                    {
                        "task_id": "def_4_root",
                        "status": FAILED_LOCAL,
                        "stop_reason": "hard_failure",
                        "build_fail_counter": 15,
                    },
                    {
                        "task_id": "thm_4_direct",
                        "status": NONTERMINAL,
                        "dependencies": ["def_4_root"],
                    },
                    {
                        "task_id": "thm_4_transitive",
                        "status": NONTERMINAL,
                        "dependencies": ["thm_4_direct"],
                    },
                    {
                        "task_id": "thm_4_independent",
                        "status": NONTERMINAL,
                        "dependencies": [],
                    },
                ],
            }
        )

        rows = {row.task_id: row for row in report.rows}
        self.assertEqual(rows["thm_4_direct"].status, DEPENDENCY_FAILED)
        self.assertEqual(rows["thm_4_direct"].failed_dependency, "def_4_root")
        self.assertEqual(rows["thm_4_transitive"].status, DEPENDENCY_FAILED)
        self.assertEqual(rows["thm_4_transitive"].failed_dependency, "def_4_root")
        self.assertEqual(rows["thm_4_independent"].status, NONTERMINAL)
        self.assertFalse(report.all_terminal)

    def test_substantive_failure_count_is_conservative(self):
        budget = count_substantive_failures(
            [
                {
                    "kind": "build_check_failure",
                    "candidate_changed": True,
                    "canonical_result": True,
                    "failure_fingerprint": "unknown-id",
                    "candidate_hash": "a",
                },
                {
                    "kind": "build_check_failure",
                    "candidate_changed": True,
                    "canonical_result": True,
                    "failure_fingerprint": "unknown-id",
                    "candidate_hash": "a",
                },
                {
                    "kind": "semantic_review_inconclusive",
                    "build_ready": True,
                    "canonical_result": True,
                    "failure_fingerprint": "missing-spine",
                    "candidate_hash": "b",
                },
                {
                    "kind": "review_apply_rejection",
                    "rejection_class": "freshness",
                    "canonical_result": True,
                },
                {
                    "kind": "review_apply_rejection",
                    "rejection_class": "configuration",
                    "canonical_result": True,
                },
                {
                    "kind": "build_check_failure",
                    "candidate_changed": True,
                    "canonical_result": False,
                    "mechanism_blocker": True,
                },
            ]
        )

        self.assertEqual(budget.counted, 3)
        self.assertFalse(budget.exhausted)

    def test_completed_with_proof_debt_blocks_dependents_until_debt_fix(self):
        report = analyze_batch_state(
            {
                "batch_id": "with-debt",
                "tasks": [
                    {
                        "task_id": "thm_11_7",
                        "status": COMPLETED_WITH_PROOF_DEBT,
                        "proof_obligation_summary": {
                            "status_counts": {"proved": 5, "accepted_as_proof_debt": 1},
                            "needs_concrete_decomposition": False,
                        },
                    },
                    {
                        "task_id": "prob_11_6",
                        "status": NONTERMINAL,
                        "dependencies": ["thm_11_7"],
                    },
                ],
            }
        )

        rows = {row.task_id: row for row in report.rows}
        self.assertEqual(rows["thm_11_7"].status, COMPLETED_WITH_PROOF_DEBT)
        self.assertTrue(rows["thm_11_7"].terminal)
        self.assertEqual(rows["thm_11_7"].next_action, "run debt-fix")
        self.assertEqual(rows["prob_11_6"].status, DEPENDENCY_PROOF_DEBT)
        self.assertEqual(rows["prob_11_6"].proof_debt_dependency, "thm_11_7")
        self.assertTrue(rows["prob_11_6"].terminal)
        self.assertEqual(rows["prob_11_6"].failed_dependency, "")

    def test_legacy_completed_task_with_accepted_proof_debt_blocks_dependents(self):
        report = analyze_batch_state(
            {
                "batch_id": "legacy-debt",
                "tasks": [
                    {
                        "task_id": "thm_10_8",
                        "status": "COMPLETED",
                        "proof_obligation_summary": {
                            "status_counts": {"proved": 4, "accepted_as_proof_debt": 3},
                            "needs_concrete_decomposition": False,
                        },
                    },
                    {
                        "task_id": "prob_10_10",
                        "status": NONTERMINAL,
                        "dependencies": ["thm_10_8"],
                    },
                ],
            }
        )

        rows = {row.task_id: row for row in report.rows}
        self.assertEqual(rows["thm_10_8"].status, COMPLETED_WITH_PROOF_DEBT)
        self.assertEqual(rows["prob_10_10"].status, DEPENDENCY_PROOF_DEBT)
        self.assertEqual(rows["prob_10_10"].proof_debt_dependency, "thm_10_8")

    def test_complex_hard_failure_before_retry_budget_is_flagged(self):
        report = analyze_batch_state(
            {
                "batch_id": "complex-retry",
                "tasks": [
                    {
                        "task_id": "thm_4_complex",
                        "status": FAILED_LOCAL,
                        "stop_reason": "hard_failure",
                        "complex_retry_after_under_evidenced_hard_stop": True,
                        "failure_events": [
                            {
                                "kind": "build_check_failure",
                                "candidate_changed": True,
                                "canonical_result": True,
                                "failure_fingerprint": f"failure-{index}",
                                "candidate_hash": f"candidate-{index}",
                            }
                            for index in range(14)
                        ],
                    }
                ],
            }
        )

        row = report.rows[0]
        self.assertEqual(row.build_fail_streak, 14)
        self.assertEqual(row.status, NONTERMINAL)
        self.assertFalse(row.terminal)
        self.assertIn("before build/review failure streak reaches 15", row.issue)

    def test_hard_failure_before_streak_budget_does_not_skip_downstream(self):
        report = analyze_batch_state(
            {
                "batch_id": "early-hard-failure",
                "tasks": [
                    {
                        "task_id": "thm_10_8",
                        "status": FAILED_LOCAL,
                        "stop_reason": "hard_failure",
                        "build_fail_counter": 14,
                        "review_fail_counter": 0,
                    },
                    {
                        "task_id": "thm_10_9",
                        "status": NONTERMINAL,
                        "dependencies": ["thm_10_8"],
                    },
                ],
            }
        )

        rows = {row.task_id: row for row in report.rows}
        self.assertEqual(rows["thm_10_8"].status, NONTERMINAL)
        self.assertFalse(rows["thm_10_8"].terminal)
        self.assertIn("before build/review failure streak reaches 15", rows["thm_10_8"].issue)
        self.assertEqual(rows["thm_10_9"].status, NONTERMINAL)
        self.assertEqual(rows["thm_10_9"].failed_dependency, "")

    def test_placeholder_decomposition_is_nonterminal_and_does_not_skip_downstream(self):
        report = analyze_batch_state(
            {
                "batch_id": "placeholder-decomposition",
                "tasks": [
                    {
                        "task_id": "thm_10_8",
                        "status": FAILED_LOCAL,
                        "stop_reason": "hard_failure",
                        "proof_obligation_summary": {
                            "requires_decomposition": True,
                            "open_blocking_ids": ["source_proof_spine"],
                            "needs_concrete_decomposition": True,
                        },
                    },
                    {
                        "task_id": "thm_10_9",
                        "status": NONTERMINAL,
                        "dependencies": ["thm_10_8"],
                    },
                ],
            }
        )

        rows = {row.task_id: row for row in report.rows}
        self.assertEqual(rows["thm_10_8"].status, NEEDS_DECOMPOSITION)
        self.assertFalse(rows["thm_10_8"].terminal)
        self.assertIn("concrete proof-obligation decomposition", rows["thm_10_8"].issue)
        self.assertEqual(rows["thm_10_9"].status, NONTERMINAL)
        self.assertEqual(rows["thm_10_9"].failed_dependency, "")

    def test_dependency_failed_without_failed_root_is_flagged(self):
        report = analyze_batch_state(
            {
                "batch_id": "bad-skip",
                "tasks": [
                    {
                        "task_id": "thm_4_skip",
                        "status": DEPENDENCY_FAILED,
                        "dependencies": ["def_4_unfailed"],
                    }
                ],
            }
        )

        row = report.rows[0]
        self.assertEqual(row.status, DEPENDENCY_FAILED)
        self.assertIn("without a failed hard dependency", row.issue)

    def test_script_renders_markdown_table_from_fixture(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_batch_controller"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            root.mkdir(parents=True)
            state_path = root / "batch.json"
            state_path.write_text(
                json.dumps(
                    {
                        "batch_id": "script-fixture",
                        "tasks": [
                            {"task_id": "def_4_root", "status": "COMPLETED"},
                            {"task_id": "thm_4_next", "status": "NONTERMINAL", "dependencies": ["def_4_root"]},
                        ],
                    }
                ),
                encoding="utf-8",
            )

            result = subprocess.run(
                [sys.executable, "tools/phase2_batch_status.py", str(state_path)],
                cwd=REPO_ROOT,
                check=True,
                text=True,
                capture_output=True,
            )

            self.assertIn("Phase 2 Batch Status: script-fixture", result.stdout)
            self.assertIn("| thm_4_next | NONTERMINAL |", result.stdout)
        finally:
            shutil.rmtree(root, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
