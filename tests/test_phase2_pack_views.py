import json
import os
import shutil
import sys
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formalization_engine.phase2_pack_views import build_failure_summary_markdown, build_operator_prompt  # noqa: E402
from tests.phase2_review_test_support import Phase2ReviewTestSupport  # noqa: E402


class Phase2PackViewsTests(Phase2ReviewTestSupport, unittest.TestCase):
    def test_build_operator_prompt_mentions_required_files_and_rules(self):
        prompt = build_operator_prompt({"block_id": "def_4_3_sup_inf"})
        self.assertIn("Return Lean code only", prompt)
        self.assertIn("imports.lean", prompt)
        self.assertIn("search_notes.md", prompt)
        self.assertIn("Do not redefine any object", prompt)
        self.assertIn("review-now --review-subject candidate", prompt)
        self.assertIn("review-now --review-subject existing", prompt)
        self.assertNotIn("Use `verify` only", prompt)

    def test_build_operator_prompt_auto_loop_authoring_requires_same_session_continuation(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_operator_prompt_auto_loop_authoring"
        try:
            self._clean_root(root)
            task_id = "thm_4_operator_prompt_auto_loop_authoring"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            ledger.update_runtime_metadata(
                task_id,
                current_auto_loop_enabled=True,
                current_auto_loop_entry_subject="current",
                current_auto_loop_round=1,
                current_auto_loop_max_rounds=6,
                current_auto_loop_max_build_attempts_per_round=3,
                current_auto_loop_nonprogress_limit=2,
                current_auto_loop_consecutive_nonprogress=0,
                current_auto_loop_phase="build_checking",
                current_auto_loop_status="active",
                current_auto_loop_stop_reason="",
                current_auto_loop_last_candidate_hash="",
                current_auto_loop_last_review_fingerprint="",
                current_auto_loop_last_repair_request_file="",
            )

            prompt = build_operator_prompt(
                {"block_id": task_id, "content": "Show a trivial theorem.", "type": "Theorem"},
                ledger,
                settings,
                pack_dir,
            )

            self.assertIn("same-session action", prompt.lower())
            self.assertIn("continue authoring in `draft.lean`", prompt.lower())
            self.assertIn("Immediately rerun `auto-loop`", prompt)
            self.assertIn("do not wait for a new user message", prompt.lower())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_build_operator_prompt_auto_loop_reviewer_requires_same_session_continuation(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_operator_prompt_auto_loop_reviewer"
        try:
            self._clean_root(root)
            task_id = "thm_4_operator_prompt_auto_loop_reviewer"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            ledger.update_runtime_metadata(
                task_id,
                current_auto_loop_enabled=True,
                current_auto_loop_entry_subject="current",
                current_auto_loop_round=2,
                current_auto_loop_max_rounds=6,
                current_auto_loop_max_build_attempts_per_round=3,
                current_auto_loop_nonprogress_limit=2,
                current_auto_loop_consecutive_nonprogress=0,
                current_auto_loop_phase="reviewing",
                current_auto_loop_status="active",
                current_auto_loop_stop_reason="",
                current_auto_loop_last_candidate_hash="abc",
                current_auto_loop_last_review_fingerprint="def",
                current_auto_loop_last_repair_request_file="",
                current_review_input_file=str(pack_dir / "semantic_review_input_v1.json"),
            )

            prompt = build_operator_prompt(
                {"block_id": task_id, "content": "Show a trivial theorem.", "type": "Theorem"},
                ledger,
                settings,
                pack_dir,
            )

            self.assertIn("independent read-only semantic reviewer", prompt.lower())
            self.assertIn("independent read-only semantic review mode", prompt.lower())
            self.assertIn("reviewer_independence", prompt)
            self.assertIn("Immediately rerun `auto-loop`", prompt)
            self.assertIn("do not wait for a new user message", prompt.lower())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_build_operator_prompt_routes_superseded_candidate_to_existing_review(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_operator_prompt_official_guard"
        try:
            self._clean_root(root)
            task_id = "thm_4_operator_prompt_official_guard"
            stale_candidate = f"import Mathlib\n\ntheorem {task_id} : True := by\n  trivial\n"
            repaired_output = f"import Mathlib\n\n-- repaired official output\ntheorem {task_id} : True := by\n  trivial\n"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(
                root,
                task_id,
                candidate_code=stale_candidate,
            )
            candidate_path = pack_dir / "candidate_v1.lean"
            candidate_path.write_text(stale_candidate, encoding="utf-8")
            os.utime(candidate_path, (1000, 1000))
            ledger.update_runtime_metadata(
                task_id,
                latest_build_ready_candidate_file=str(candidate_path),
                latest_build_ready_candidate_hash=ledger._hash_text(stale_candidate),
                latest_build_ready_candidate_kind="draft",
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(repaired_output, encoding="utf-8")
            os.utime(output_path, (2000, 2000))

            prompt = build_operator_prompt(
                {
                    "block_id": task_id,
                    "content": "Show a trivial theorem.",
                    "type": "Theorem",
                    "source_plan": "08_chap4_measurable_functions",
                },
                ledger,
                settings,
                pack_dir,
            )

            self.assertIn("Official output routing guard", prompt)
            self.assertIn("review-now --review-subject existing", prompt)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_build_operator_prompt_blocks_lean_author_before_math_review_go(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_operator_prompt_math_gate"
        try:
            self._clean_root(root)
            task_id = "prob_14_1"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            ledger.update_runtime_metadata(
                task_id,
                phase2_status="fail",
                phase2_status_reason="semantic_fail_public_premise: moved the core urn law into setup",
                latest_semantic_fail_triage_category="public_premise",
            )

            prompt = build_operator_prompt(
                {"block_id": task_id, "content": "Solve the urn limit problem.", "type": "Problem"},
                ledger,
                settings,
                pack_dir,
            )

            self.assertIn("Math Review Gate", prompt)
            self.assertIn("natural language proof skeleton", prompt)
            self.assertIn("independent read-only math reviewer", prompt)
            self.assertIn("pre-author checklist", prompt)
            self.assertIn("source statement identified", prompt)
            self.assertIn("no public premise relocation", prompt)
            self.assertIn("math proof skeleton reviewed go", prompt)
            self.assertIn("independent semantic review after build", prompt)
            self.assertNotIn("Return Lean code only", prompt)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_build_operator_prompt_for_blocking_proof_stop_lists_current_blocker(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_operator_prompt_math_blocking_proof"
        try:
            self._clean_root(root)
            task_id = "prob_14_1"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            (pack_dir / "math_proof_skeleton_v8.md").write_text(
                "# Math Proof Skeleton\n\nThe analytic convergence theorem is the remaining blocker.",
                encoding="utf-8",
            )
            (pack_dir / "math_review_result_v8.json").write_text(
                json.dumps(
                    {
                        "verdict": "stop",
                        "stop_mode": "blocking_proof",
                        "blocking_theorems": [
                            "prob_14_1_stirling_beta_cdf_convergence_internal"
                        ],
                        "allowed_next_targets": [
                            "gamma_ratio_global_power_bound",
                            "left_tail_eventually_small",
                            "scaled_mass_uniform_on_compact",
                        ],
                        "forbidden_work": ["canonical-corpus promotion", "semantic review"],
                    }
                ),
                encoding="utf-8",
            )
            ledger.update_runtime_metadata(
                task_id,
                phase2_status="fail",
                phase2_status_reason="private_axiom_or_open_math_debt",
            )

            prompt = build_operator_prompt(
                {"block_id": task_id, "content": "Solve the urn limit problem.", "type": "Problem"},
                ledger,
                settings,
                pack_dir,
            )

            self.assertIn("blocking proof", prompt.lower())
            self.assertIn("prob_14_1_stirling_beta_cdf_convergence_internal", prompt)
            self.assertIn("gamma_ratio_global_power_bound", prompt)
            self.assertIn("left_tail_eventually_small", prompt)
            self.assertIn("scaled_mass_uniform_on_compact", prompt)
            self.assertIn("pre-author checklist", prompt)
            self.assertIn("source statement identified", prompt)
            self.assertIn("no public premise relocation", prompt)
            self.assertIn("math proof skeleton reviewed go", prompt)
            self.assertIn("independent semantic review after build", prompt)
            self.assertNotIn("Resume Lean author/build only after the Math Review Gate verdict is `go`", prompt)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_auto_loop_nonprogress_is_explained_in_runtime_views(self):
        history = {
            "attempts": [
                {"stage": "build", "primary_failure_kind": "semantic_no_progress"},
                {"stage": "build", "primary_failure_kind": "semantic_no_progress"},
            ]
        }

        summary = build_failure_summary_markdown(
            "thm_4_auto_loop_nonprogress",
            history,
            auto_loop_state={
                "enabled": True,
                "status": "stopped",
                "phase": "stopped",
                "stop_reason": "nonprogress",
            },
        )

        self.assertIn("non-progress", summary.lower())
        self.assertIn("Latest auto-loop stop reason: `nonprogress`", summary)
        self.assertNotIn("waiting", summary.lower())

    def test_failure_summary_routes_task_local_missing_lemma_to_proof_work(self):
        history = {
            "attempts": [
                {
                    "attempt": 7,
                    "stage": "build",
                    "success": False,
                    "primary_failure_kind": "missing_local_foundation_lemma",
                    "candidate_file": "candidate_v7.lean",
                    "blocking_symbols": ["prob_11_10_polya_uniformization_from_pointwise"],
                }
            ]
        }

        summary = build_failure_summary_markdown("prob_11_10", history)

        self.assertIn("missing_local_foundation_lemma", summary)
        self.assertIn("prob_11_10_polya_uniformization_from_pointwise", summary)
        self.assertIn("Prove or split the task-local missing lemma", summary)


if __name__ == "__main__":
    unittest.main()
