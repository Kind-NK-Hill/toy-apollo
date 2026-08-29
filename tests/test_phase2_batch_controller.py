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
    NONTERMINAL,
    analyze_batch_state,
    count_substantive_failures,
    render_markdown_report,
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

    def test_phase2_blocked_dependency_is_reported_as_blocked(self):
        report = analyze_batch_state(
            {
                "batch_id": "blocked-dependency",
                "tasks": [
                    {
                        "task_id": "prob_14_1",
                        "status": NONTERMINAL,
                        "phase2_status": "blocked",
                        "phase2_status_reason": "selected dependency is not clean",
                    },
                    {
                        "task_id": "prob_14_8",
                        "status": NONTERMINAL,
                        "dependencies": ["prob_14_1"],
                    },
                ],
            }
        )

        rows = {row.task_id: row for row in report.rows}
        self.assertEqual(rows["prob_14_1"].task_status, "blocked")
        self.assertEqual(rows["prob_14_1"].next_action, "repair dependency gate blocker")
        self.assertEqual(rows["prob_14_8"].status, NONTERMINAL)
        self.assertEqual(rows["prob_14_8"].task_status, "blocked")
        self.assertEqual(rows["prob_14_8"].report_status, "blocked")
        self.assertEqual(rows["prob_14_8"].blocked_dependency, "prob_14_1")
        self.assertEqual(rows["prob_14_8"].next_action, "skip; blocked by prob_14_1")
        markdown = render_markdown_report(report)
        self.assertIn("blocked_dependency", markdown)
        self.assertIn("| prob_14_8 | NONTERMINAL | blocked | blocked |", markdown)

    def test_family_support_without_current_pass_blocks_downstream_repair(self):
        cases = [
            (
                "source_route_finite_interval_covered",
                "finite_interval_completed_but_direct_downstream_blocked",
            ),
            (
                "source_route_support_completed_downstream_blocked",
                "not_completed_downstream_blocked",
            ),
        ]
        for proof_class, completion_class in cases:
            with self.subTest(proof_class=proof_class, completion_class=completion_class):
                report = analyze_batch_state(
                    {
                        "batch_id": "family-support",
                        "tasks": [
                            {
                                "task_id": "thm_7_8",
                                "status": NONTERMINAL,
                                "review_verdict": "fail",
                                "proof_class": proof_class,
                                "completion_class": completion_class,
                                "proof_obligation_summary": {
                                    "open_blocking_ids": [],
                                    "needs_concrete_decomposition": False,
                                },
                            },
                            {
                                "task_id": "obl_thm_7_9_t7_9_finite_bridge_abs",
                                "status": NONTERMINAL,
                                "dependencies": ["thm_7_8"],
                            },
                        ],
                    }
                )

                rows = {row.task_id: row for row in report.rows}
                self.assertEqual(rows["thm_7_8"].task_status, "fail")
                self.assertEqual(rows["thm_7_8"].proof_class, proof_class)
                self.assertEqual(
                    rows["obl_thm_7_9_t7_9_finite_bridge_abs"].blocked_dependency,
                    "thm_7_8",
                )
                self.assertEqual(rows["obl_thm_7_9_t7_9_finite_bridge_abs"].task_status, "blocked")

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

    def test_explicit_completed_with_proof_debt_blocks_dependents_until_re_review(self):
        report = analyze_batch_state(
            {
                "batch_id": "with-debt",
                "tasks": [
                    {
                        "task_id": "thm_11_7",
                        "status": COMPLETED_WITH_PROOF_DEBT,
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
        self.assertFalse(rows["thm_11_7"].terminal)
        self.assertTrue(rows["thm_11_7"].report_terminal)
        self.assertEqual(rows["thm_11_7"].next_action, "run review-now --review-subject existing")
        self.assertEqual(rows["prob_11_6"].status, DEPENDENCY_PROOF_DEBT)
        self.assertEqual(rows["prob_11_6"].proof_debt_dependency, "thm_11_7")
        self.assertFalse(rows["prob_11_6"].terminal)
        self.assertTrue(rows["prob_11_6"].report_terminal)
        self.assertEqual(rows["prob_11_6"].next_action, "repair proof-debt root thm_11_7 before downstream")
        self.assertEqual(rows["prob_11_6"].failed_dependency, "")
        self.assertFalse(report.all_terminal)
        self.assertTrue(report.all_reporting_terminal)
        self.assertFalse(report.all_clean_or_allowed_exception)

    def test_task_status_fail_prevents_clean_batch_completion(self):
        report = analyze_batch_state(
            {
                "batch_id": "task-status",
                "tasks": [
                    {
                        "task_id": "thm_14_6",
                        "type": "Theorem",
                        "status": "COMPLETED",
                        "phase2_review_verdict": "pass",
                        "phase2_proof_class": "mathlib_backed_adapter_completed",
                    }
                ],
            }
        )

        row = report.rows[0]
        self.assertEqual(row.status, "COMPLETED")
        self.assertEqual(row.task_status, "fail")
        self.assertFalse(row.clean_or_allowed_exception)
        self.assertFalse(report.all_clean_or_allowed_exception)
        self.assertEqual(row.next_action, "repair task-level proof status")
        markdown = render_markdown_report(report)
        self.assertIn("| task_id | ledger_status | phase2_status | report_status |", markdown)

    def test_completed_missing_task_status_is_not_clean(self):
        report = analyze_batch_state(
            {
                "batch_id": "missing-task-status",
                "tasks": [
                    {
                        "task_id": "thm_11_7",
                        "type": "Theorem",
                        "status": "COMPLETED",
                    }
                ],
            }
        )

        row = report.rows[0]
        self.assertEqual(row.status, "COMPLETED")
        self.assertEqual(row.task_status, "")
        self.assertEqual(row.report_status, "needs_fresh_review")
        self.assertFalse(row.clean_or_allowed_exception)
        self.assertFalse(row.terminal)
        self.assertFalse(report.all_clean_or_allowed_exception)
        self.assertEqual(row.next_action, "run fresh semantic review")

    def test_missing_proof_class_uses_report_status_not_phase2_status(self):
        report = analyze_batch_state(
            {
                "batch_id": "needs-class-normalization",
                "tasks": [
                    {
                        "task_id": "thm_11_7",
                        "type": "Theorem",
                        "status": "COMPLETED",
                        "phase2_review_verdict": "pass",
                    }
                ],
            }
        )

        row = report.rows[0]
        self.assertEqual(row.task_status, "fail")
        self.assertEqual(row.report_status, "needs_class_normalization")
        self.assertFalse(row.clean_or_allowed_exception)
        self.assertEqual(row.next_action, "run fresh classified semantic review")

    def test_proof_bearing_interface_bridge_review_pass_is_not_clean(self):
        report = analyze_batch_state(
            {
                "batch_id": "bridge-on-theorem",
                "tasks": [
                    {
                        "task_id": "thm_14_6",
                        "type": "Theorem",
                        "status": "COMPLETED",
                        "phase2_review_verdict": "pass",
                        "phase2_proof_class": "interface_bridge_completed",
                    }
                ],
            }
        )

        row = report.rows[0]
        self.assertEqual(row.task_status, "fail")
        self.assertFalse(row.clean_or_allowed_exception)
        self.assertEqual(row.next_action, "repair task-level proof status")

    def test_diagnostic_objective_preserves_report_terminal_for_proof_debt(self):
        report = analyze_batch_state(
            {
                "batch_id": "with-debt",
                "tasks": [
                    {
                        "task_id": "thm_11_7",
                        "status": COMPLETED_WITH_PROOF_DEBT,
                    },
                    {
                        "task_id": "prob_11_6",
                        "status": NONTERMINAL,
                        "dependencies": ["thm_11_7"],
                    },
                ],
            },
            objective="diagnostic",
        )

        rows = {row.task_id: row for row in report.rows}
        self.assertEqual(rows["thm_11_7"].status, COMPLETED_WITH_PROOF_DEBT)
        self.assertTrue(rows["thm_11_7"].terminal)
        self.assertEqual(rows["prob_11_6"].status, DEPENDENCY_PROOF_DEBT)
        self.assertTrue(rows["prob_11_6"].terminal)
        self.assertTrue(report.all_terminal)
        self.assertTrue(report.all_reporting_terminal)
        self.assertFalse(report.all_clean_or_allowed_exception)

    def test_allowed_beyond_book_exception_is_clean_for_textbook_objective(self):
        report = analyze_batch_state(
            {
                "batch_id": "allowed-beyond-book",
                "tasks": [
                    {
                        "task_id": "thm_14_8",
                        "status": COMPLETED_WITH_PROOF_DEBT,
                        "current_class": "beyond_book_exception",
                    }
                ],
            }
        )

        row = report.rows[0]
        self.assertTrue(row.allowed_beyond_book_exception)
        self.assertTrue(row.clean_or_allowed_exception)
        self.assertTrue(row.terminal)
        self.assertEqual(row.next_action, "none; allowed beyond-book exception")
        self.assertTrue(report.all_clean_or_allowed_exception)

    def test_cited_external_proof_exception_is_clean_or_allowed_for_textbook_objective(self):
        report = analyze_batch_state(
            {
                "batch_id": "allowed-cited-external",
                "tasks": [
                    {
                        "task_id": "thm_11_8",
                        "type": "Theorem",
                        "status": "COMPLETED",
                        "phase2_status": "allowed_exception",
                        "phase2_review_verdict": "pass",
                        "phase2_proof_class": "cited_external_proof_exception",
                    }
                ],
            }
        )

        row = report.rows[0]
        self.assertTrue(row.allowed_beyond_book_exception)
        self.assertTrue(row.clean_or_allowed_exception)
        self.assertTrue(row.terminal)
        self.assertTrue(report.all_clean_or_allowed_exception)

    def test_legacy_proof_obligation_summary_does_not_infer_or_block_on_proof_debt(self):
        report = analyze_batch_state(
            {
                "batch_id": "legacy-debt",
                "tasks": [
                    {
                        "task_id": "thm_10_8",
                        "status": "COMPLETED",
                        "phase2_status": "pass",
                        "phase2_review_verdict": "pass",
                        "phase2_proof_class": "source_route_proof_completed",
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
        self.assertEqual(rows["thm_10_8"].status, "COMPLETED")
        self.assertTrue(rows["thm_10_8"].terminal)
        self.assertTrue(rows["thm_10_8"].clean_or_allowed_exception)
        self.assertEqual(rows["prob_10_10"].status, NONTERMINAL)
        self.assertFalse(rows["prob_10_10"].terminal)
        self.assertEqual(rows["prob_10_10"].proof_debt_dependency, "")
        self.assertEqual(rows["prob_10_10"].blocked_dependency, "")

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

    def test_placeholder_summary_is_ignored_and_ordinary_failure_routing_applies(self):
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
        self.assertEqual(rows["thm_10_8"].status, NONTERMINAL)
        self.assertFalse(rows["thm_10_8"].terminal)
        self.assertIn("failure streak reaches 15", rows["thm_10_8"].issue)
        self.assertEqual(rows["thm_10_9"].status, NONTERMINAL)
        self.assertEqual(rows["thm_10_9"].failed_dependency, "")
        self.assertEqual(rows["thm_10_9"].blocked_dependency, "thm_10_8")
        self.assertEqual(rows["thm_10_9"].proof_debt_dependency, "")

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
