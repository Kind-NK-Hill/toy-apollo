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

from src.toy_apollo.phase2_review_loop import (  # noqa: E402
    run_codex_auto_loop,
    run_codex_review_fix,
    run_codex_review_now,
)
from tests.phase2_review_test_support import Phase2ReviewTestSupport  # noqa: E402


class Phase2ReviewLoopTests(Phase2ReviewTestSupport, unittest.TestCase):

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
                "src.toy_apollo.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = asyncio.run(run_codex_review_now(task_id, ledger, settings, review_subject="existing"))

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
                "src.toy_apollo.phase2_prompt_pack.LeanCompiler.validate_with_repl_async",
                new=AsyncMock(return_value=(True, "repl ok")),
            ), patch(
                "src.toy_apollo.phase2_prompt_pack.LeanCompiler.build_module_async",
                new=AsyncMock(return_value=(True, "temp build ok")),
            ), patch(
                "src.toy_apollo.phase2_prompt_pack._run_staged_official_build",
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
                        max_build_attempts_per_round=1,
                    )
                )

            self.assertTrue(success, detail)
            self.assertIn("must now perform the reviewer step", detail)
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
                "src.toy_apollo.phase2_prompt_pack.LeanCompiler.validate_with_repl_async",
                new=AsyncMock(return_value=(False, "REPL System Error: synthetic failure")),
            ), patch(
                "src.toy_apollo.phase2_prompt_pack.LeanCompiler.build_module_async",
                new=AsyncMock(return_value=(True, "temp build ok")),
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

            self.assertTrue(success)
            self.assertIn("must now repair `draft.lean`", detail)
            self.assertIn("continue this same-session auto-loop now", detail)
            self.assertNotIn("rerun auto-loop", detail.lower())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_now_current_reprepares_existing_subject_after_result_exists(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_existing_reprepare"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_loop_existing_reprepare"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(root, task_id, completed=True)
            self.assertTrue(output_path.exists())
            with patch("src.toy_apollo.phase2_prompt_pack._run_official_module_build", return_value=(True, "build ok")):
                success, detail = asyncio.run(
                    run_codex_review_now(task_id, ledger, settings, review_subject="existing")
                )
            self.assertTrue(success, detail)
            self._write_codex_review_result(pack_dir, verdict="fail")

            with patch("src.toy_apollo.phase2_prompt_pack._run_official_module_build", return_value=(True, "build ok")):
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
            from src.toy_apollo.phase2_prompt_pack import apply_codex_review_result, write_codex_review_pack

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
            from src.toy_apollo.phase2_prompt_pack import apply_codex_review_result, write_codex_review_pack

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
            from src.toy_apollo.phase2_prompt_pack import apply_codex_review_result, write_codex_review_pack

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

    def test_auto_loop_build_failure_exhausts_round_budget_and_mirrors_state(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_build_budget"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_loop_build_budget"
            bad_candidate = f"import Mathlib\n\ntheorem {task_id} : True := by\n  sorry\n"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id, candidate_code=bad_candidate)
            success, detail = asyncio.run(
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
            self.assertFalse(success)
            self.assertIn("build budget", detail.lower())
            context_text = (pack_dir / "context.md").read_text(encoding="utf-8")
            self.assertIn("Current auto-loop stop reason: `build_budget_exhausted`", context_text)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_auto_loop_candidate_review_preparation_preserves_auto_loop_after_repair_clear(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_review_prepare"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_loop_review_prepare"
            from src.toy_apollo.phase2_prompt_pack import apply_codex_review_result, write_codex_review_pack

            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            result_path = self._write_codex_review_result(pack_dir, verdict="fail", source_claims=[], claim_mapping=[])
            asyncio.run(apply_codex_review_result(task_id, ledger, settings, str(result_path)))

            with patch(
                "src.toy_apollo.phase2_prompt_pack.LeanCompiler.validate_with_repl_async",
                new=AsyncMock(return_value=(True, "repl ok")),
            ), patch(
                "src.toy_apollo.phase2_prompt_pack.LeanCompiler.build_module_async",
                new=AsyncMock(return_value=(True, "temp build ok")),
            ), patch(
                "src.toy_apollo.phase2_prompt_pack._run_staged_official_build",
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
            task_record = ledger.ledger["tasks"][task_id]
            self.assertEqual(task_record.get("current_auto_loop_phase"), "reviewing")
            self.assertEqual(str(task_record.get("current_review_repair_request_file", "") or ""), "")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_auto_loop_stops_after_repeated_nonprogress_failures(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_loop_nonprogress"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_loop_nonprogress"
            from src.toy_apollo.phase2_prompt_pack import write_codex_review_pack

            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            asyncio.run(write_codex_review_pack(task_id, ledger, settings))
            result_path = self._write_codex_review_result(pack_dir, verdict="fail", source_claims=[], claim_mapping=[])

            with patch(
                "src.toy_apollo.phase2_prompt_pack.LeanCompiler.validate_with_repl_async",
                new=AsyncMock(return_value=(True, "repl ok")),
            ), patch(
                "src.toy_apollo.phase2_prompt_pack.LeanCompiler.build_module_async",
                new=AsyncMock(return_value=(True, "temp build ok")),
            ), patch(
                "src.toy_apollo.phase2_prompt_pack._run_staged_official_build",
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
            second_result_path = self._write_codex_review_result(pack_dir, verdict="fail", source_claims=[], claim_mapping=[])
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
