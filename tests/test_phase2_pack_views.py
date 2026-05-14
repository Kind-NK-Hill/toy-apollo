import json
import shutil
import sys
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.toy_apollo.phase2_pack_views import build_failure_summary_markdown, build_operator_prompt  # noqa: E402
from tests.phase2_review_test_support import Phase2ReviewTestSupport  # noqa: E402


class Phase2PackViewsTests(Phase2ReviewTestSupport, unittest.TestCase):
    def test_build_operator_prompt_mentions_required_files_and_rules(self):
        prompt = build_operator_prompt({"block_id": "def_4_3_sup_inf"})
        self.assertIn("Return Lean code only", prompt)
        self.assertIn("imports.lean", prompt)
        self.assertIn("search_notes.md", prompt)
        self.assertIn("Do not redefine any object", prompt)
        self.assertIn("review-pack`/`review-apply` as the default semantic review path", prompt)
        self.assertIn("Use `verify` only", prompt)

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

            self.assertIn("same-session semantic reviewer", prompt.lower())
            self.assertIn("semantic review mode", prompt.lower())
            self.assertIn("Immediately rerun `auto-loop`", prompt)
            self.assertIn("do not wait for a new user message", prompt.lower())
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


if __name__ == "__main__":
    unittest.main()
