import asyncio
import json
import os
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import AsyncMock, patch

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formalization_engine.phase2_review_loop import (  # noqa: E402
    run_codex_auto_loop,
    run_codex_review_fix,
    run_codex_review_now,
)
from formalization_engine.phase2_prompt_pack import (  # noqa: E402
    build_check_prompt_pack_candidate,
)
from tests.phase2_review_test_support import Phase2ReviewTestSupport  # noqa: E402


class Phase2ReviewLoopTests(Phase2ReviewTestSupport, unittest.TestCase):
    def test_auto_loop_pass_is_terminal_only_after_apply(self):
        from formalization_engine.phase2_prompt_pack import write_codex_review_pack

        with tempfile.TemporaryDirectory() as tmp:
            task_id = "thm_4_handoff_completion"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(Path(tmp), task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            review_success, review_detail = asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            self.assertTrue(review_success, review_detail)
            self._write_codex_review_result(pack_dir, verdict="pass")

            def promote(*args, **kwargs):
                output_path.parent.mkdir(parents=True, exist_ok=True)
                output_path.write_text((pack_dir / "candidate_v1.lean").read_text(encoding="utf-8"), encoding="utf-8")
                return True, "final build ok"

            with patch("formalization_engine.phase2_review_apply.run_staged_official_build", side_effect=promote):
                outcome = asyncio.run(run_codex_auto_loop(task_id, ledger, settings))

            self.assertTrue(outcome.success, outcome.detail)
            self.assertIsInstance(outcome, tuple)
            self.assertEqual(tuple(outcome), (outcome.success, outcome.detail))
            self.assertTrue(outcome.is_terminal)
            self.assertEqual(outcome.next_action, "completed")
            self.assertEqual(outcome.stop_reason, "completed")
            self.assertEqual(ledger.ledger["tasks"][task_id]["status"], "COMPLETED")
            self.assertEqual(ledger.ledger["tasks"][task_id]["current_auto_loop_stop_reason"], "passed")
            self.assertTrue(output_path.is_file())

    def _setup_downstream_of_proof_debt_task(self, root: Path):
        self._clean_root(root)
        plans_dir = root / "plans"
        plans_dir.mkdir(parents=True, exist_ok=True)
        dep_id = "thm_10_8"
        task_id = "thm_10_9"
        (plans_dir / "chapter10-continuous-mapping_plan.json").write_text(
            json.dumps(
                [
                    {
                        "block_id": dep_id,
                        "type": "Theorem",
                        "title": "Debt-bearing upstream",
                        "content": "Upstream theorem with accepted proof debt.",
                        "dependencies": [],
                    },
                    {
                        "block_id": task_id,
                        "type": "Theorem",
                        "title": "Downstream theorem",
                        "content": "Downstream theorem depending on the upstream result.",
                        "dependencies": [dep_id],
                    },
                ],
                indent=2,
            ),
            encoding="utf-8",
        )
        from formalization_engine.ledger_manager import LedgerManager, TaskStatus

        ledger = LedgerManager(ledger_path=str(root / "project_ledger.json"))
        for block_id, dependencies in ((dep_id, []), (task_id, [dep_id])):
            ledger.add_or_update_task(
                {
                    "block_id": block_id,
                    "type": "Theorem",
                    "title": block_id,
                    "content": "test task",
                    "source_plan": "chapter10-continuous-mapping",
                    "dependencies": dependencies,
                }
            )
        ledger.update_status(dep_id, TaskStatus.COMPLETED_WITH_PROOF_DEBT)
        ledger.update_runtime_metadata(
            dep_id,
            proof_obligation_summary={"status_counts": {"proved": 5, "accepted_as_proof_debt": 1}},
        )
        settings = self._make_settings(root, plans_dir)
        return ledger, settings, task_id, dep_id

    def test_review_now_rejects_removed_support_subject(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_support_removed"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_loop_support_removed"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id, completed=True)

            success, detail = asyncio.run(run_codex_review_now(task_id, ledger, settings, review_subject="support"))

            self.assertFalse(success)
            self.assertIn("unsupported review-now subject", detail.lower())
            self.assertFalse((pack_dir / "semantic_review_request.json").exists())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_now_current_requires_existing_request(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_current_requires_request"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            task_id = "thm_4_review_loop_current_requires_request"
            ledger, settings, _, _ = self._setup_trivial_phase2_task(root, task_id)

            success, detail = asyncio.run(run_codex_review_now(task_id, ledger, settings, review_subject="current"))

            self.assertFalse(success)
            self.assertIn("request", detail.lower())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_now_stops_before_preparing_downstream_with_proof_debt_dependency(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_proof_debt_dep_review_now"
        try:
            ledger, settings, task_id, dep_id = self._setup_downstream_of_proof_debt_task(root)

            success, detail = asyncio.run(run_codex_review_now(task_id, ledger, settings, review_subject="current"))

            self.assertFalse(success)
            self.assertIn(dep_id, detail)
            self.assertIn("proof debt", detail.lower())
            self.assertFalse((settings.phase2_prompt_packs_dir / task_id).exists())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_auto_loop_stops_before_preparing_downstream_with_proof_debt_dependency(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_proof_debt_dep_auto_loop"
        try:
            ledger, settings, task_id, dep_id = self._setup_downstream_of_proof_debt_task(root)

            success, detail = asyncio.run(run_codex_auto_loop(task_id, ledger, settings))

            self.assertFalse(success)
            self.assertIn(dep_id, detail)
            self.assertIn("proof debt", detail.lower())
            self.assertFalse((settings.phase2_prompt_packs_dir / task_id).exists())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_now_existing_ignores_broken_draft_when_official_output_is_valid(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_existing_ignores_broken_draft"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            task_id = "thm_4_review_loop_existing_ignores_broken_draft"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(root, task_id, completed=True)
            self.assertTrue(output_path.exists())
            (pack_dir / "draft.lean").write_text("import Missing.Module\n#check impossible_name\n", encoding="utf-8")

            with patch(
                "formalization_engine.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                outcome = asyncio.run(run_codex_review_now(task_id, ledger, settings, review_subject="existing"))

            success, detail = outcome
            self.assertEqual(outcome.next_action, "reviewer_write_result")
            self.assertEqual(outcome.is_terminal, False)
            self.assertEqual(outcome.stop_reason, "")
            self.assertTrue(Path(outcome.request_path).is_file())
            self.assertFalse(Path(outcome.expected_result_path).exists())
            self.assertTrue(success, detail)
            self.assertEqual(ledger.ledger["tasks"][task_id]["current_review_subject_kind"], "official_output")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_auto_loop_reuses_next_round_after_prior_completed_cycle(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_round_reuse"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            task_id = "thm_4_review_loop_round_reuse"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            ledger.update_runtime_metadata(
                task_id,
                current_auto_loop_enabled=True,
                current_auto_loop_entry_subject="current",
                current_auto_loop_round=1,
                current_auto_loop_max_rounds=6,
                current_auto_loop_max_build_attempts_per_round=1,
                current_auto_loop_nonprogress_limit=2,
                current_auto_loop_consecutive_nonprogress=0,
                current_auto_loop_phase="build_checking",
                current_auto_loop_status="active",
                current_auto_loop_stop_reason="",
                current_auto_loop_last_candidate_hash="",
                current_auto_loop_last_review_fingerprint="",
                current_auto_loop_last_repair_request_file="",
            )
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            ledger.update_runtime_metadata(
                task_id,
                current_auto_loop_phase="completed",
                current_auto_loop_status="completed",
                current_auto_loop_stop_reason="passed",
            )

            with patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.validate_with_repl_async",
                new=AsyncMock(return_value=(True, "repl ok")),
            ), patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.build_async",
                new=AsyncMock(return_value=(True, "temp build ok")),
            ), patch(
                "formalization_engine.phase2_prompt_pack._run_staged_official_build",
                return_value=(True, "final build ok"),
            ):
                outcome = asyncio.run(
                    run_codex_auto_loop(
                        task_id,
                        ledger,
                        settings,
                        review_subject="current",
                        max_auto_rounds=6,
                        nonprogress_limit=2,
                        max_build_attempts_per_round=1,
                    )
                )

            success, detail = outcome
            self.assertEqual(outcome.next_action, "reviewer_write_result")
            self.assertEqual(outcome.is_terminal, False)
            self.assertEqual(outcome.stop_reason, "")
            self.assertTrue(Path(outcome.request_path).is_file())
            self.assertFalse(Path(outcome.expected_result_path).exists())
            self.assertTrue(success, detail)
            self.assertIn("independent read-only reviewer", detail)
            self.assertIn("continue this same-session auto-loop now", detail)
            task_record = ledger.ledger["tasks"][task_id]
            self.assertEqual(task_record.get("current_auto_loop_phase"), "reviewing")
            context = (pack_dir / "context.md").read_text(encoding="utf-8")
            self.assertIn("Current auto-loop next action: `reviewer_write_result`", context)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_auto_loop_build_failure_message_demands_same_session_continuation(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_author_detail"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            task_id = "thm_4_review_loop_author_detail"
            ledger, settings, _, _ = self._setup_trivial_phase2_task(root, task_id)
            with patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.validate_with_repl_async",
                new=AsyncMock(return_value=(False, "REPL System Error: synthetic failure")),
            ), patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.build_async",
                new=AsyncMock(return_value=(True, "temp build ok")),
            ):
                outcome = asyncio.run(
                    run_codex_auto_loop(
                        task_id,
                        ledger,
                        settings,
                        review_subject="current",
                        max_auto_rounds=6,
                        nonprogress_limit=2,
                        max_build_attempts_per_round=3,
                    )
                )

            success, detail = outcome
            self.assertEqual(outcome.next_action, "author_repair")
            self.assertEqual(outcome.is_terminal, False)
            self.assertEqual(outcome.stop_reason, "")
            self.assertTrue(success)
            self.assertIn("must now repair `draft.lean`", detail)
            self.assertIn("continue this same-session auto-loop now", detail)
            self.assertNotIn("rerun auto-loop", detail.lower())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_auto_loop_defaults_to_hardcoded_15_by_15_budget(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_default_budget"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            task_id = "thm_4_review_loop_default_budget"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            with patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.validate_with_repl_async",
                new=AsyncMock(return_value=(False, "REPL System Error: synthetic failure")),
            ), patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.build_async",
                new=AsyncMock(return_value=(True, "temp build ok")),
            ):
                success, detail = asyncio.run(run_codex_auto_loop(task_id, ledger, settings))

            self.assertTrue(success, detail)
            self.assertIn("Build attempts used in this round: 1/15", detail)
            task_record = ledger.ledger["tasks"][task_id]
            self.assertEqual(task_record["current_auto_loop_max_rounds"], 15)
            self.assertEqual(task_record["current_auto_loop_max_build_attempts_per_round"], 15)
            self.assertEqual(task_record["current_auto_loop_nonprogress_limit"], 15)
            context = (pack_dir / "context.md").read_text(encoding="utf-8")
            self.assertIn("Current auto-loop max rounds: `15`", context)
            self.assertIn("Current auto-loop max build attempts per round: `15`", context)
            self.assertIn("Current auto-loop non-progress limit: `15`", context)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_now_current_reprepares_existing_subject_after_result_exists(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_existing_reprepare"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_loop_existing_reprepare"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(root, task_id, completed=True)
            self.assertTrue(output_path.exists())
            with patch("formalization_engine.phase2_prompt_pack._run_official_module_build", return_value=(True, "build ok")):
                success, detail = asyncio.run(
                    run_codex_review_now(task_id, ledger, settings, review_subject="existing")
                )
            self.assertTrue(success, detail)
            self._write_codex_review_result(pack_dir, verdict="fail")

            with patch("formalization_engine.phase2_prompt_pack._run_official_module_build", return_value=(True, "build ok")):
                success, detail = asyncio.run(
                    run_codex_review_now(task_id, ledger, settings, review_subject="current")
                )

            self.assertTrue(success, detail)
            self.assertTrue((pack_dir / "official_snapshot_v2.lean").exists())
            self.assertTrue((pack_dir / "semantic_review_request_v2.json").exists())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_fix_requires_active_repair_request(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_fix_requires_active_request"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_loop_fix_requires_active_request"
            ledger, settings, _, _ = self._setup_trivial_phase2_task(root, task_id)
            success, detail = asyncio.run(run_codex_review_fix(task_id, ledger, settings))
            self.assertFalse(success)
            self.assertIn("repair", detail.lower())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_fix_backfills_missing_active_repair_request_from_latest_failed_review(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_fix_backfill"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_loop_fix_backfill"
            from formalization_engine.phase2_prompt_pack import apply_codex_review_result, write_codex_review_pack

            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            result_path = self._write_codex_review_result(pack_dir, verdict="fail", source_claims=[], claim_mapping=[])
            asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))
            ledger.update_runtime_metadata(
                task_id,
                current_review_repair_request_file="",
                current_review_repair_summary_file="",
                current_review_repair_seed_file="",
                current_review_repair_origin_result_file="",
                current_review_repair_archive_file="",
                latest_review_repair_request_file="",
                latest_review_repair_summary_file="",
                latest_review_repair_request_alias_file="",
                latest_review_repair_summary_alias_file="",
            )
            for path in (
                pack_dir / "review_repair_request_v1.json",
                pack_dir / "review_repair_request.json",
                pack_dir / "review_repair_summary_v1.md",
                pack_dir / "review_repair_summary.md",
            ):
                if path.exists():
                    path.unlink()

            success, detail = asyncio.run(run_codex_review_fix(task_id, ledger, settings))

            self.assertTrue(success, detail)
            self.assertIn("repair contract is active", detail.lower())
            repair_request = json.loads((pack_dir / "review_repair_request_v1.json").read_text(encoding="utf-8"))
            self.assertEqual(repair_request["failed_verdict"], "fail")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_fix_rejects_stale_repair_result_hash(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_fix_stale_hash"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_loop_fix_stale_hash"
            from formalization_engine.phase2_prompt_pack import apply_codex_review_result, write_codex_review_pack

            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            result_path = self._write_codex_review_result(pack_dir, verdict="fail", source_claims=[], claim_mapping=[])
            asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))
            result_path.write_text(result_path.read_text(encoding="utf-8") + "\n", encoding="utf-8")

            success, detail = asyncio.run(run_codex_review_fix(task_id, ledger, settings))

            self.assertFalse(success)
            self.assertIn("stale", detail.lower())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_fix_abandon_appends_note_and_clears_current_repair_metadata(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_fix_abandon"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_loop_fix_abandon"
            from formalization_engine.phase2_prompt_pack import apply_codex_review_result, write_codex_review_pack

            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            result_path = self._write_codex_review_result(pack_dir, verdict="fail", source_claims=[], claim_mapping=[])
            asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            success, detail = asyncio.run(run_codex_review_fix(task_id, ledger, settings, abandon_current_repair=True))

            self.assertTrue(success, detail)
            task_record = ledger.ledger["tasks"][task_id]
            self.assertEqual(str(task_record.get("current_review_repair_request_file", "") or ""), "")
            summary_text = (pack_dir / "review_repair_summary.md").read_text(encoding="utf-8")
            self.assertIn("abandoned", summary_text.lower())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_now_candidate_clears_active_repair_metadata(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_review_now_candidate_clears_repair"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_loop_review_now_candidate_clears_repair"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            ledger.update_runtime_metadata(
                task_id,
                current_review_repair_request_file=str(pack_dir / "review_repair_request_v1.json"),
                current_review_repair_summary_file=str(pack_dir / "review_repair_summary_v1.md"),
                current_review_repair_seed_file=str(pack_dir / "candidate_v1.lean"),
                current_review_repair_origin_result_file=str(pack_dir / "semantic_review_result_v1.json"),
                current_review_repair_archive_file=str(pack_dir / "draft_pre_repair_v1.lean"),
            )

            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            success, detail = asyncio.run(run_codex_review_now(task_id, ledger, settings, review_subject="candidate"))

            self.assertTrue(success, detail)
            task_record = ledger.ledger["tasks"][task_id]
            self.assertEqual(str(task_record.get("current_review_repair_request_file", "") or ""), "")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_now_candidate_rejects_candidate_superseded_by_official_output(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_stale_candidate_official"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_loop_stale_candidate_official"
            stale_candidate = f"import Mathlib\n\ntheorem {task_id} : True := by\n  trivial\n"
            repaired_output = f"import Mathlib\n\n-- repaired official output\ntheorem {task_id} : True := by\n  trivial\n"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(
                root,
                task_id,
                candidate_code=stale_candidate,
            )

            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            candidate_path = Path(str(ledger.ledger["tasks"][task_id]["latest_build_ready_candidate_file"]))
            os.utime(candidate_path, (1000, 1000))
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(repaired_output, encoding="utf-8")
            os.utime(output_path, (2000, 2000))

            success, detail = asyncio.run(run_codex_review_now(task_id, ledger, settings, review_subject="candidate"))

            self.assertFalse(success)
            self.assertIn("Stale candidate review target", detail)
            self.assertIn("review-now --review-subject existing", detail)
            self.assertFalse((pack_dir / "semantic_review_request.json").exists())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_now_candidate_allows_build_ready_candidate_after_staging_restore(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_staging_restore_candidate"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_loop_staging_restore_candidate"
            active_candidate = f"import Mathlib\n\n-- active candidate repair\ntheorem {task_id} : True := by\n  trivial\n"
            old_output = f"import Mathlib\n\n-- old official output\ntheorem {task_id} : True := by\n  trivial\n"
            ledger, settings, _pack_dir, output_path = self._setup_trivial_phase2_task(
                root,
                task_id,
                candidate_code=active_candidate,
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(old_output, encoding="utf-8")
            os.utime(output_path, (1000, 1000))

            with patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.validate_with_repl_async",
                new=AsyncMock(return_value=(True, "repl ok")),
            ), patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.build_async",
                new=AsyncMock(return_value=(True, "temp build ok")),
            ), patch(
                "formalization_engine.phase2_prompt_pack._run_staged_official_build",
                return_value=(True, "official build ok"),
            ):
                build_success, build_detail = asyncio.run(build_check_prompt_pack_candidate(task_id, ledger, settings))

            self.assertTrue(build_success, build_detail)
            success, detail = asyncio.run(run_codex_review_now(task_id, ledger, settings, review_subject="candidate"))

            self.assertTrue(success, detail)
            self.assertEqual(ledger.ledger["tasks"][task_id]["current_review_subject_kind"], "candidate")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_now_candidate_allows_newer_active_candidate_repair(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_newer_candidate_allowed"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_loop_newer_candidate_allowed"
            active_candidate = f"import Mathlib\n\n-- active candidate repair\ntheorem {task_id} : True := by\n  trivial\n"
            old_output = f"import Mathlib\n\n-- old official output\ntheorem {task_id} : True := by\n  trivial\n"
            ledger, settings, _pack_dir, output_path = self._setup_trivial_phase2_task(
                root,
                task_id,
                candidate_code=active_candidate,
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(old_output, encoding="utf-8")
            os.utime(output_path, (1000, 1000))

            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            candidate_path = Path(str(ledger.ledger["tasks"][task_id]["latest_build_ready_candidate_file"]))
            os.utime(candidate_path, (2000, 2000))

            success, detail = asyncio.run(run_codex_review_now(task_id, ledger, settings, review_subject="candidate"))

            self.assertTrue(success, detail)
            self.assertEqual(ledger.ledger["tasks"][task_id]["current_review_subject_kind"], "candidate")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_now_current_rejects_stale_candidate_request_after_official_output_changes(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_current_stale_candidate"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_loop_current_stale_candidate"
            stale_candidate = f"import Mathlib\n\ntheorem {task_id} : True := by\n  trivial\n"
            repaired_output = f"import Mathlib\n\n-- repaired official output\ntheorem {task_id} : True := by\n  trivial\n"
            ledger, settings, _pack_dir, output_path = self._setup_trivial_phase2_task(
                root,
                task_id,
                candidate_code=stale_candidate,
            )
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            success, detail = asyncio.run(run_codex_review_now(task_id, ledger, settings, review_subject="candidate"))
            self.assertTrue(success, detail)

            candidate_path = Path(str(ledger.ledger["tasks"][task_id]["latest_build_ready_candidate_file"]))
            os.utime(candidate_path, (1000, 1000))
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(repaired_output, encoding="utf-8")
            os.utime(output_path, (2000, 2000))

            success, detail = asyncio.run(run_codex_review_now(task_id, ledger, settings, review_subject="current"))

            self.assertFalse(success)
            self.assertIn("Stale current candidate review request", detail)
            self.assertIn("review-now --review-subject existing", detail)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_fix_rejects_candidate_seed_superseded_by_official_output(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_stale_repair_seed"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_loop_stale_repair_seed"
            stale_candidate = f"import Mathlib\n\ntheorem {task_id} : True := by\n  trivial\n"
            repaired_output = f"import Mathlib\n\n-- repaired official output\ntheorem {task_id} : True := by\n  trivial\n"
            from formalization_engine.phase2_prompt_pack import apply_codex_review_result, write_codex_review_pack

            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(
                root,
                task_id,
                candidate_code=stale_candidate,
            )
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            result_path = self._write_codex_review_result(
                pack_dir,
                verdict="fail",
                source_claims=[],
                claim_mapping=[],
                proof_class="partial_source_route",
                completion_class="partial_source_route",
            )
            payload = json.loads(result_path.read_text(encoding="utf-8"))
            payload["summary"] = "The route is accepted; one medium lemma missing within an accepted route."
            payload["findings"] = [{"severity": "warning", "category": "proof", "message": payload["summary"]}]
            result_path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
            asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))
            candidate_path = Path(str(ledger.ledger["tasks"][task_id]["current_review_repair_seed_file"]))
            os.utime(candidate_path, (1000, 1000))
            draft_before = "import Mathlib\n\n-- do not overwrite stale repair seed\n"
            (pack_dir / "draft.lean").write_text(draft_before, encoding="utf-8")
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(repaired_output, encoding="utf-8")
            os.utime(output_path, (2000, 2000))

            success, detail = asyncio.run(run_codex_review_fix(task_id, ledger, settings))

            self.assertFalse(success)
            self.assertIn("Stale review-fix repair seed target", detail)
            self.assertEqual((pack_dir / "draft.lean").read_text(encoding="utf-8"), draft_before)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_fix_backfill_rejects_candidate_seed_superseded_by_official_output(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_stale_backfill_seed"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_loop_stale_backfill_seed"
            stale_candidate = f"import Mathlib\n\ntheorem {task_id} : True := by\n  trivial\n"
            repaired_output = f"import Mathlib\n\n-- repaired official output\ntheorem {task_id} : True := by\n  trivial\n"
            from formalization_engine.phase2_prompt_pack import apply_codex_review_result, write_codex_review_pack

            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(
                root,
                task_id,
                candidate_code=stale_candidate,
            )
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            result_path = self._write_codex_review_result(
                pack_dir,
                verdict="fail",
                source_claims=[],
                claim_mapping=[],
                proof_class="partial_source_route",
                completion_class="partial_source_route",
            )
            payload = json.loads(result_path.read_text(encoding="utf-8"))
            payload["summary"] = "The route is accepted; one medium lemma missing within an accepted route."
            payload["findings"] = [{"severity": "warning", "category": "proof", "message": payload["summary"]}]
            result_path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
            asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))
            seed_path = Path(str(ledger.ledger["tasks"][task_id]["current_review_repair_seed_file"]))
            os.utime(seed_path, (1000, 1000))
            ledger.update_runtime_metadata(
                task_id,
                current_review_repair_request_file="",
                current_review_repair_summary_file="",
                current_review_repair_seed_file="",
                current_review_repair_origin_result_file="",
                current_review_repair_archive_file="",
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(repaired_output, encoding="utf-8")
            os.utime(output_path, (2000, 2000))

            success, detail = asyncio.run(run_codex_review_fix(task_id, ledger, settings))

            self.assertFalse(success)
            self.assertIn("Stale review-fix backfill seed target", detail)
            self.assertEqual(str(ledger.ledger["tasks"][task_id].get("current_review_repair_request_file", "") or ""), "")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_auto_loop_build_failure_exhausts_round_budget_and_mirrors_state(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_build_budget"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_loop_build_budget"
            bad_candidate = f"import Mathlib\n\ntheorem {task_id} : True := by\n  sorry\n"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id, candidate_code=bad_candidate)
            outcome = asyncio.run(
                run_codex_auto_loop(
                    task_id,
                    ledger,
                    settings,
                    review_subject="current",
                    max_auto_rounds=6,
                    nonprogress_limit=2,
                    max_build_attempts_per_round=1,
                )
            )
            success, detail = outcome
            self.assertEqual(outcome.next_action, "stopped")
            self.assertEqual(outcome.is_terminal, True)
            self.assertEqual(outcome.stop_reason, "build_budget_exhausted")
            self.assertFalse(success)
            self.assertIn("build budget", detail.lower())
            context_text = (pack_dir / "context.md").read_text(encoding="utf-8")
            self.assertIn("Current auto-loop stop reason: `build_budget_exhausted`", context_text)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_auto_loop_rejects_same_candidate_review_after_semantic_failure(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_same_candidate_guard"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_loop_same_candidate_guard"
            from formalization_engine.phase2_prompt_pack import apply_codex_review_result, write_codex_review_pack

            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            result_path = self._write_codex_review_result(
                pack_dir,
                verdict="fail",
                source_claims=[],
                claim_mapping=[],
                proof_class="partial_source_route",
                completion_class="partial_source_route",
            )
            payload = json.loads(result_path.read_text(encoding="utf-8"))
            payload["summary"] = "The route is accepted; one medium lemma is missing within the accepted route."
            payload["findings"] = [{"severity": "warning", "category": "proof", "message": payload["summary"]}]
            result_path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
            asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))
            task_record_before = ledger.ledger["tasks"][task_id]
            self.assertEqual(int(task_record_before.get("current_auto_loop_round") or 0), 0)
            self.assertFalse((pack_dir / "semantic_review_request_v2.json").exists())

            with patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.validate_with_repl_async",
                new=AsyncMock(return_value=(True, "repl ok")),
            ), patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.build_async",
                new=AsyncMock(return_value=(True, "temp build ok")),
            ), patch(
                "formalization_engine.phase2_prompt_pack._run_staged_official_build",
                return_value=(True, "final build ok"),
            ):
                success, detail = asyncio.run(
                    run_codex_auto_loop(
                        task_id,
                        ledger,
                        settings,
                        review_subject="current",
                        max_auto_rounds=6,
                        nonprogress_limit=2,
                        max_build_attempts_per_round=3,
                    )
                )

            self.assertTrue(success, detail)
            self.assertIn("same candidate", detail.lower())
            self.assertIn("repair `draft.lean`", detail)
            task_record = ledger.ledger["tasks"][task_id]
            self.assertEqual(task_record.get("current_auto_loop_phase"), "authoring")
            self.assertEqual(task_record.get("current_auto_loop_status"), "active")
            self.assertEqual(int(task_record.get("current_auto_loop_round") or 0), 2)
            self.assertFalse((pack_dir / "semantic_review_request_v2.json").exists())
            context_text = (pack_dir / "context.md").read_text(encoding="utf-8")
            self.assertIn("Current auto-loop phase: `authoring`", context_text)
            history = json.loads((pack_dir / "attempt_history.json").read_text(encoding="utf-8"))
            round_two_builds = [
                item
                for item in history["attempts"]
                if item.get("stage") == "build" and int(item.get("auto_loop_round") or 0) == 2
            ]
            self.assertEqual(len(round_two_builds), 1)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_auto_loop_restart_preserves_seeded_repair_draft_and_rechecks_freshness(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_restart_seeded_repair"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_loop_restart_seeded_repair"
            from formalization_engine.phase2_prompt_pack import apply_codex_review_result, write_codex_review_pack

            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            result_path = self._write_codex_review_result(
                pack_dir,
                verdict="fail",
                source_claims=[],
                claim_mapping=[],
                proof_class="partial_source_route",
                completion_class="partial_source_route",
            )
            result_payload = json.loads(result_path.read_text(encoding="utf-8"))
            result_payload["summary"] = "The public interface must be rewritten after external diagnosis."
            result_payload["findings"] = [
                {"severity": "error", "category": "interface", "message": result_payload["summary"]}
            ]
            result_path.write_text(json.dumps(result_payload, indent=2, ensure_ascii=False), encoding="utf-8")
            asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            seed_success, seed_detail = asyncio.run(run_codex_review_fix(task_id, ledger, settings))
            self.assertTrue(seed_success, seed_detail)
            request_path = Path(ledger.ledger["tasks"][task_id]["current_review_repair_request_file"])
            authored_draft = (pack_dir / "draft.lean").read_text(encoding="utf-8") + "\n-- author rewrite after diagnoser and Math Review Gate go\n"
            (pack_dir / "draft.lean").write_text(authored_draft, encoding="utf-8")
            archives_before_restart = sorted(pack_dir.glob("pre_repair_draft_v*.lean"))
            ledger.update_runtime_metadata(
                task_id,
                current_auto_loop_enabled=True,
                current_auto_loop_entry_subject="current",
                current_auto_loop_round=1,
                current_auto_loop_max_rounds=6,
                current_auto_loop_max_build_attempts_per_round=3,
                current_auto_loop_nonprogress_limit=2,
                current_auto_loop_consecutive_nonprogress=0,
                current_auto_loop_phase="stopped",
                current_auto_loop_status="stopped",
                current_auto_loop_stop_reason="math_review_gate_required",
                current_auto_loop_last_candidate_hash="",
                current_auto_loop_last_review_fingerprint="",
                current_auto_loop_last_repair_request_file=str(request_path),
            )

            with patch(
                "formalization_engine.phase2_review_loop.run_build_check_cycle",
                new=AsyncMock(return_value=(False, "intentional build stop after repair seed decision")),
            ) as build_check_mock:
                success, detail = asyncio.run(
                    run_codex_auto_loop(
                        task_id,
                        ledger,
                        settings,
                        review_subject="current",
                        max_auto_rounds=6,
                        nonprogress_limit=2,
                        max_build_attempts_per_round=3,
                    )
                )

            self.assertTrue(success, detail)
            build_check_mock.assert_awaited_once()
            self.assertEqual((pack_dir / "draft.lean").read_text(encoding="utf-8"), authored_draft)
            self.assertEqual(sorted(pack_dir.glob("pre_repair_draft_v*.lean")), archives_before_restart)

            request_payload = json.loads(request_path.read_text(encoding="utf-8"))
            failed_result_path = Path(request_payload["failed_review_result_file"])
            if not failed_result_path.is_absolute():
                failed_result_path = (pack_dir / failed_result_path).resolve()
            failed_result_path.write_text(
                failed_result_path.read_text(encoding="utf-8") + "\n",
                encoding="utf-8",
            )
            ledger.update_runtime_metadata(
                task_id,
                current_auto_loop_phase="stopped",
                current_auto_loop_status="stopped",
                current_auto_loop_stop_reason="math_review_gate_required",
            )

            stale_success, stale_detail = asyncio.run(
                run_codex_auto_loop(
                    task_id,
                    ledger,
                    settings,
                    review_subject="current",
                    max_auto_rounds=6,
                    nonprogress_limit=2,
                    max_build_attempts_per_round=3,
                )
            )

            self.assertFalse(stale_success)
            self.assertIn("stale", stale_detail.lower())
            self.assertEqual(ledger.ledger["tasks"][task_id]["current_auto_loop_stop_reason"], "freshness_error")
            self.assertEqual((pack_dir / "draft.lean").read_text(encoding="utf-8"), authored_draft)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_auto_loop_stops_same_candidate_legacy_open_debt_with_diagnoser_triage(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_same_candidate_legacy_open_debt"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_loop_same_candidate_legacy_open_debt"
            from formalization_engine.phase2_prompt_pack import apply_codex_review_result, write_codex_review_pack

            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            result_path = self._write_codex_review_result(
                pack_dir,
                verdict="fail",
                source_claims=[],
                claim_mapping=[],
                proof_class="open_math_debt",
                completion_class="open_math_debt",
            )
            payload = json.loads(result_path.read_text(encoding="utf-8"))
            payload["summary"] = "The proof still relies on a private axiom and remains open_math_debt."
            payload["findings"] = [{"severity": "error", "category": "proof", "message": payload["summary"]}]
            result_path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
            asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            request_path = pack_dir / "review_repair_request_v1.json"
            request_payload = json.loads(request_path.read_text(encoding="utf-8"))
            request_payload.pop("semantic_fail_triage", None)
            request_path.write_text(json.dumps(request_payload, indent=2, ensure_ascii=False), encoding="utf-8")
            for stale_path in list(pack_dir.glob("semantic_fail_triage*.json")) + list(pack_dir.glob("prepared_diagnoser_prompt*.txt")):
                stale_path.unlink()
            ledger.update_runtime_metadata(
                task_id,
                latest_semantic_fail_triage_file="",
                latest_semantic_fail_triage_category="",
                latest_semantic_fail_triage_needs_diagnoser=False,
                latest_semantic_fail_triage_local_repair_allowed=False,
                latest_diagnoser_prompt_file="",
                latest_diagnosis_state="",
            )

            with patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.validate_with_repl_async",
                new=AsyncMock(return_value=(True, "repl ok")),
            ), patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.build_async",
                new=AsyncMock(return_value=(True, "temp build ok")),
            ), patch(
                "formalization_engine.phase2_prompt_pack._run_staged_official_build",
                return_value=(True, "final build ok"),
            ):
                success, detail = asyncio.run(
                    run_codex_auto_loop(
                        task_id,
                        ledger,
                        settings,
                        review_subject="current",
                        max_auto_rounds=6,
                        nonprogress_limit=2,
                        max_build_attempts_per_round=3,
                    )
                )

            self.assertFalse(success)
            self.assertIn("diagnoser", detail.lower())
            task_record = ledger.ledger["tasks"][task_id]
            self.assertEqual(task_record.get("current_auto_loop_phase"), "stopped")
            self.assertEqual(task_record.get("current_auto_loop_status"), "stopped")
            self.assertEqual(task_record.get("current_auto_loop_stop_reason"), "diagnoser_required")
            triage = json.loads((pack_dir / "semantic_fail_triage.json").read_text(encoding="utf-8"))
            self.assertEqual(triage["category"], "private_axiom_or_open_math_debt")
            self.assertTrue(triage["needs_diagnoser"])
            self.assertFalse(triage["local_repair_allowed"])
            self.assertTrue(Path(triage["prompt_path"]).exists())
            self.assertTrue(task_record["latest_semantic_fail_triage_needs_diagnoser"])
            self.assertFalse(task_record["latest_semantic_fail_triage_local_repair_allowed"])
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_auto_loop_allows_same_candidate_review_for_non_semantic_repair_seed(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_same_candidate_invalid_exception"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_loop_same_candidate_invalid_exception"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            candidate_hash = str(ledger.ledger["tasks"][task_id].get("latest_build_ready_candidate_hash", "") or "")
            repair_request = {
                "schema_version": "phase2.review_repair.request.v1",
                "task_id": task_id,
                "origin_review_mode": "review-apply",
                "review_subject_kind": "candidate",
                "failed_verdict": "invalid",
                "failed_review_subject_hash": candidate_hash,
                "must_fix": ["rewrite invalid reviewer artifact"],
                "next_draft_seed_file": str(pack_dir / "candidate_v1.lean"),
            }
            repair_path = pack_dir / "review_repair_request_v1.json"
            repair_path.write_text(json.dumps(repair_request, indent=2), encoding="utf-8")
            ledger.update_runtime_metadata(
                task_id,
                current_review_repair_request_file=str(repair_path),
                current_review_repair_summary_file=str(pack_dir / "review_repair_summary_v1.md"),
                current_review_repair_seed_file=str(pack_dir / "candidate_v1.lean"),
                current_auto_loop_enabled=True,
                current_auto_loop_entry_subject="current",
                current_auto_loop_round=2,
                current_auto_loop_max_rounds=6,
                current_auto_loop_max_build_attempts_per_round=3,
                current_auto_loop_nonprogress_limit=2,
                current_auto_loop_consecutive_nonprogress=0,
                current_auto_loop_phase="entry",
                current_auto_loop_status="active",
                current_auto_loop_stop_reason="",
                current_auto_loop_last_candidate_hash="",
                current_auto_loop_last_review_fingerprint="",
                current_auto_loop_last_repair_request_file=str(repair_path),
            )

            with patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.validate_with_repl_async",
                new=AsyncMock(return_value=(True, "repl ok")),
            ), patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.build_async",
                new=AsyncMock(return_value=(True, "temp build ok")),
            ), patch(
                "formalization_engine.phase2_prompt_pack._run_staged_official_build",
                return_value=(True, "final build ok"),
            ):
                success, detail = asyncio.run(
                    run_codex_auto_loop(
                        task_id,
                        ledger,
                        settings,
                        review_subject="current",
                        max_auto_rounds=6,
                        nonprogress_limit=2,
                        max_build_attempts_per_round=3,
                    )
                )

            self.assertTrue(success, detail)
            self.assertIn("independent read-only reviewer", detail)
            task_record = ledger.ledger["tasks"][task_id]
            current_request = Path(str(task_record.get("current_review_request_file", "") or ""))
            self.assertTrue(current_request.exists())
            self.assertEqual(task_record.get("current_auto_loop_phase"), "reviewing")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_auto_loop_stops_after_repeated_nonprogress_failures(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_nonprogress"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_loop_nonprogress"
            from formalization_engine.phase2_prompt_pack import write_codex_review_pack

            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            result_path = self._write_codex_review_result(
                pack_dir,
                verdict="fail",
                source_claims=[],
                claim_mapping=[],
                proof_class="partial_source_route",
                completion_class="partial_source_route",
            )
            payload = json.loads(result_path.read_text(encoding="utf-8"))
            payload["summary"] = "The route is accepted; one medium lemma missing within an accepted route."
            payload["findings"] = [{"severity": "warning", "category": "proof", "message": payload["summary"]}]
            result_path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")

            with patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.validate_with_repl_async",
                new=AsyncMock(return_value=(True, "repl ok")),
            ), patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.build_async",
                new=AsyncMock(return_value=(True, "temp build ok")),
            ), patch(
                "formalization_engine.phase2_prompt_pack._run_staged_official_build",
                return_value=(True, "final build ok"),
            ):
                success, detail = asyncio.run(
                    run_codex_auto_loop(
                        task_id,
                        ledger,
                        settings,
                        review_subject="candidate",
                        max_auto_rounds=6,
                        nonprogress_limit=1,
                        max_build_attempts_per_round=3,
                    )
                )

            self.assertTrue(success, detail)
            self.assertIn("same candidate", detail.lower())
            draft_path = pack_dir / "draft.lean"
            draft_path.write_text(draft_path.read_text(encoding="utf-8") + "\n-- substantive repair attempt\n", encoding="utf-8")

            with patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.validate_with_repl_async",
                new=AsyncMock(return_value=(True, "repl ok")),
            ), patch(
                "formalization_engine.phase2_prompt_pack.LeanCompiler.build_async",
                new=AsyncMock(return_value=(True, "temp build ok")),
            ), patch(
                "formalization_engine.phase2_prompt_pack._run_staged_official_build",
                return_value=(True, "final build ok"),
            ):
                success, detail = asyncio.run(
                    run_codex_auto_loop(
                        task_id,
                        ledger,
                        settings,
                        review_subject="candidate",
                        max_auto_rounds=6,
                        nonprogress_limit=1,
                        max_build_attempts_per_round=3,
                    )
                )

            self.assertTrue(success, detail)
            self.assertIn("semantic_review_result", detail)
            second_result_path = self._write_codex_review_result(
                pack_dir,
                verdict="fail",
                source_claims=[],
                claim_mapping=[],
                proof_class="partial_source_route",
                completion_class="partial_source_route",
            )
            second_payload = json.loads(second_result_path.read_text(encoding="utf-8"))
            second_payload["summary"] = "The route is accepted; one medium lemma missing within an accepted route."
            second_payload["findings"] = [{"severity": "warning", "category": "proof", "message": second_payload["summary"]}]
            second_result_path.write_text(json.dumps(second_payload, indent=2, ensure_ascii=False), encoding="utf-8")
            self.assertNotEqual(str(result_path), str(second_result_path))

            success, detail = asyncio.run(
                run_codex_auto_loop(
                    task_id,
                    ledger,
                    settings,
                    review_subject="candidate",
                    max_auto_rounds=6,
                    nonprogress_limit=1,
                    max_build_attempts_per_round=3,
                )
            )

            self.assertFalse(success)
            self.assertIn("non-progress", detail.lower())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_auto_loop_pauses_when_semantic_fail_triage_requires_diagnoser(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_diagnoser_required"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_loop_diagnoser_required"
            from formalization_engine.phase2_prompt_pack import write_codex_review_pack

            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            result_path = self._write_codex_review_result(
                pack_dir,
                verdict="fail",
                source_claims=[],
                claim_mapping=[],
                proof_class="open_math_debt",
                completion_class="open_math_debt",
            )
            payload = json.loads(result_path.read_text(encoding="utf-8"))
            payload["summary"] = "The final theorem depends on a private axiom and remains open_math_debt."
            payload["findings"] = [{"severity": "error", "category": "proof", "message": payload["summary"]}]
            result_path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")

            outcome = asyncio.run(
                run_codex_auto_loop(
                    task_id,
                    ledger,
                    settings,
                    review_subject="candidate",
                    max_auto_rounds=3,
                    nonprogress_limit=2,
                    max_build_attempts_per_round=3,
                )
            )

            success, detail = outcome
            self.assertEqual(outcome.next_action, "diagnoser_read_only")
            self.assertEqual(outcome.is_terminal, False)
            self.assertEqual(outcome.stop_reason, "diagnoser_required")
            self.assertFalse(success)
            self.assertIn("diagnoser", detail.lower())
            task_record = ledger.ledger["tasks"][task_id]
            self.assertEqual(task_record["current_auto_loop_stop_reason"], "diagnoser_required")
            triage = json.loads((pack_dir / "semantic_fail_triage.json").read_text(encoding="utf-8"))
            self.assertTrue(triage["needs_diagnoser"])
            self.assertTrue(Path(triage["prompt_path"]).exists())
        finally:
            shutil.rmtree(root, ignore_errors=True)
