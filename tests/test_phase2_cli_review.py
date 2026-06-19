import argparse
import asyncio
import runpy
import shutil
import sys
import unittest
from pathlib import Path
from unittest.mock import AsyncMock, patch

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tests.phase2_review_test_support import Phase2ReviewTestSupport  # noqa: E402


class Phase2CliReviewTests(Phase2ReviewTestSupport, unittest.TestCase):
    def test_module_entrypoint_invokes_main(self):
        with patch.object(sys, "argv", ["app.py", "--help"]):
            with self.assertRaises(SystemExit) as exc:
                runpy.run_module("src.toy_apollo.cli.app", run_name="__main__")
        self.assertEqual(exc.exception.code, 0)

    def test_phase2_default_mode_is_pack(self):
        from src.toy_apollo.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "toy-apollo",
                "--phase",
                "2",
                "--tasks",
                "thm_4_default_pack",
            ],
        ), patch.object(cli_app, "process_target", new=AsyncMock()) as process_target_mock:
            code = cli_app.main()

        self.assertEqual(code, 0)
        process_target_mock.assert_awaited_once()
        args = process_target_mock.await_args.args[0]
        self.assertEqual(args.phase2_mode, "pack")

    def test_cli_rejects_legacy_phase2_mode(self):
        from src.toy_apollo.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "toy-apollo",
                "--phase",
                "2",
                "--phase2-mode",
                "legacy",
                "--tasks",
                "thm_4_legacy",
            ],
        ):
            with self.assertRaises(SystemExit) as exc:
                cli_app.main()

        self.assertEqual(exc.exception.code, 2)

    def test_cli_review_fix_accepts_abandon_flag(self):
        from src.toy_apollo.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "toy-apollo",
                "--phase",
                "2",
                "--phase2-mode",
                "review-fix",
                "--tasks",
                "thm_4_cli_review_fix",
                "--abandon-current-repair",
            ],
        ), patch.object(cli_app, "process_target", new=AsyncMock()) as process_target_mock:
            code = cli_app.main()

        self.assertEqual(code, 0)
        process_target_mock.assert_awaited_once()
        args = process_target_mock.await_args.args[0]
        self.assertEqual(args.phase2_mode, "review-fix")
        self.assertTrue(args.abandon_current_repair)

    def test_cli_debt_fix_mode_is_accepted(self):
        from src.toy_apollo.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "toy-apollo",
                "--phase",
                "2",
                "--phase2-mode",
                "debt-fix",
                "--tasks",
                "thm_4_cli_debt_fix",
            ],
        ), patch.object(cli_app, "process_target", new=AsyncMock()) as process_target_mock:
            code = cli_app.main()

        self.assertEqual(code, 0)
        process_target_mock.assert_awaited_once()
        args = process_target_mock.await_args.args[0]
        self.assertEqual(args.phase2_mode, "debt-fix")

    def test_cli_promote_obligations_mode_is_rejected(self):
        from src.toy_apollo.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "toy-apollo",
                "--phase",
                "2",
                "--phase2-mode",
                "promote-obligations",
            ],
        ), patch.object(cli_app, "process_target", new=AsyncMock()) as process_target_mock:
            with self.assertRaises(SystemExit) as raised:
                cli_app.main()

        self.assertEqual(raised.exception.code, 2)
        process_target_mock.assert_not_awaited()

    def test_cli_batch_plan_accepts_multiple_tasks(self):
        from src.toy_apollo.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "toy-apollo",
                "--phase",
                "2",
                "--phase2-mode",
                "batch-plan",
                "--tasks",
                "thm_1_1,def_1_2",
            ],
        ), patch.object(cli_app, "process_target", new=AsyncMock()) as process_target_mock:
            code = cli_app.main()

        self.assertEqual(code, 0)
        process_target_mock.assert_awaited_once()
        args = process_target_mock.await_args.args[0]
        self.assertEqual(args.phase2_mode, "batch-plan")
        self.assertEqual(args.task_ids, ["thm_1_1", "def_1_2"])

    def test_cli_batch_run_accepts_multiple_tasks_and_action_limit(self):
        from src.toy_apollo.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "toy-apollo",
                "--phase",
                "2",
                "--phase2-mode",
                "batch-run",
                "--tasks",
                "thm_1_1,def_1_2",
                "--batch-max-actions",
                "2",
            ],
        ), patch.object(cli_app, "process_target", new=AsyncMock()) as process_target_mock:
            code = cli_app.main()

        self.assertEqual(code, 0)
        process_target_mock.assert_awaited_once()
        args = process_target_mock.await_args.args[0]
        self.assertEqual(args.phase2_mode, "batch-run")
        self.assertEqual(args.task_ids, ["thm_1_1", "def_1_2"])
        self.assertEqual(args.batch_max_actions, 2)

    def test_cli_batch_plan_accepts_worker_queue_options(self):
        from src.toy_apollo.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "toy-apollo",
                "--phase",
                "2",
                "--phase2-mode",
                "batch-plan",
                "--tasks",
                "thm_1_1,def_1_2,prob_1_1",
                "--batch-task-kinds",
                "theorem,definition",
                "--batch-limit",
                "15",
                "--batch-workers",
                "5",
            ],
        ), patch.object(cli_app, "process_target", new=AsyncMock()) as process_target_mock:
            code = cli_app.main()

        self.assertEqual(code, 0)
        process_target_mock.assert_awaited_once()
        args = process_target_mock.await_args.args[0]
        self.assertEqual(args.phase2_mode, "batch-plan")
        self.assertEqual(args.batch_task_kinds, ["theorem", "definition"])
        self.assertEqual(args.batch_limit, 15)
        self.assertEqual(args.batch_workers, 5)

    def test_cli_batch_plan_accepts_explicit_legacy_audit_mode(self):
        from src.toy_apollo.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "toy-apollo",
                "--phase",
                "2",
                "--phase2-mode",
                "batch-plan",
                "--tasks",
                "obl_prob_14_1_obligation_1",
                "--batch-include-legacy",
            ],
        ), patch.object(cli_app, "process_target", new=AsyncMock()) as process_target_mock:
            code = cli_app.main()

        self.assertEqual(code, 0)
        process_target_mock.assert_awaited_once()
        args = process_target_mock.await_args.args[0]
        self.assertEqual(args.phase2_mode, "batch-plan")
        self.assertTrue(args.batch_include_legacy)

    def test_cli_auto_loop_accepts_limits_above_15_and_review_subject(self):
        from src.toy_apollo.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "toy-apollo",
                "--phase",
                "2",
                "--phase2-mode",
                "auto-loop",
                "--tasks",
                "thm_4_cli_auto_loop",
                "--review-subject",
                "candidate",
                "--max-auto-rounds",
                "16",
                "--nonprogress-limit",
                "17",
                "--max-build-attempts-per-round",
                "18",
            ],
        ), patch.object(cli_app, "process_target", new=AsyncMock()) as process_target_mock:
            code = cli_app.main()

        self.assertEqual(code, 0)
        process_target_mock.assert_awaited_once()
        args = process_target_mock.await_args.args[0]
        self.assertEqual(args.phase2_mode, "auto-loop")
        self.assertEqual(args.review_subject, "candidate")
        self.assertEqual(args.max_auto_rounds, 16)
        self.assertEqual(args.nonprogress_limit, 17)
        self.assertEqual(args.max_build_attempts_per_round, 18)

    def test_cli_auto_loop_rejects_limits_below_hardcoded_15_budget(self):
        from src.toy_apollo.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "toy-apollo",
                "--phase",
                "2",
                "--phase2-mode",
                "auto-loop",
                "--tasks",
                "thm_4_cli_auto_loop_low_budget",
                "--max-auto-rounds",
                "14",
            ],
        ), self.assertRaises(SystemExit) as caught:
            cli_app.main()

        self.assertEqual(caught.exception.code, 2)

    def test_cli_auto_loop_defaults_to_hardcoded_15_by_15_budget(self):
        from src.toy_apollo.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "toy-apollo",
                "--phase",
                "2",
                "--phase2-mode",
                "auto-loop",
                "--tasks",
                "thm_4_cli_auto_loop_default_budget",
            ],
        ), patch.object(cli_app, "process_target", new=AsyncMock()) as process_target_mock:
            code = cli_app.main()

        self.assertEqual(code, 0)
        process_target_mock.assert_awaited_once()
        args = process_target_mock.await_args.args[0]
        self.assertEqual(args.max_auto_rounds, 15)
        self.assertEqual(args.max_build_attempts_per_round, 15)
        self.assertEqual(args.nonprogress_limit, 15)

    def test_cli_phase2_soft_pack_accepts_problem_batch(self):
        from src.toy_apollo.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "toy-apollo",
                "--phase",
                "2",
                "--phase2-mode",
                "soft-pack",
                "--tasks",
                "prob_4_2,prob_4_4",
            ],
        ), patch.object(cli_app, "process_target", new=AsyncMock()) as process_target_mock:
            code = cli_app.main()

        self.assertEqual(code, 0)
        process_target_mock.assert_awaited_once()
        args = process_target_mock.await_args.args[0]
        self.assertEqual(args.phase, 2)
        self.assertEqual(args.phase2_mode, "soft-pack")
        self.assertEqual(args.task_ids, ["prob_4_2", "prob_4_4"])

    def test_cli_phase2_soft_apply_requires_selection(self):
        from src.toy_apollo.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            ["toy-apollo", "--phase", "2", "--phase2-mode", "soft-apply", "--tasks", "prob_4_2"],
        ), self.assertRaises(SystemExit) as caught:
            cli_app.main()
        self.assertEqual(caught.exception.code, 2)

    def test_cli_phase2_soft_modes_reject_non_problem_tasks(self):
        from src.toy_apollo.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            ["toy-apollo", "--phase", "2", "--phase2-mode", "soft-pack", "--tasks", "thm_4_7"],
        ), self.assertRaises(SystemExit) as caught:
            cli_app.main()
        self.assertEqual(caught.exception.code, 2)

    def test_cli_phase3_soft_modes_are_merged_into_phase2(self):
        from src.toy_apollo.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "toy-apollo",
                "--phase",
                "3",
                "--phase3-mode",
                "soft-pack",
                "--tasks",
                "prob_4_2",
            ],
        ), self.assertRaises(SystemExit) as caught:
            cli_app.main()
        self.assertEqual(caught.exception.code, 2)

    def test_cli_phase3_mode_flag_is_not_valid_with_phase2(self):
        from src.toy_apollo.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "toy-apollo",
                "--phase",
                "2",
                "--phase2-mode",
                "soft-pack",
                "--phase3-mode",
                "soft-pack",
                "--tasks",
                "prob_4_2",
            ],
        ), self.assertRaises(SystemExit) as caught:
            cli_app.main()
        self.assertEqual(caught.exception.code, 2)

    def test_cli_review_apply_requires_review_result(self):
        from src.toy_apollo.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            ["toy-apollo", "--phase", "2", "--phase2-mode", "review-apply", "--tasks", "thm_4_cli_review"],
        ), self.assertRaises(SystemExit) as caught:
            cli_app.main()
        self.assertEqual(caught.exception.code, 2)

    def test_cli_review_result_is_only_for_review_apply(self):
        from src.toy_apollo.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "toy-apollo",
                "--phase",
                "2",
                "--phase2-mode",
                "review-pack",
                "--tasks",
                "thm_4_cli_review",
                "--review-result",
                "semantic_review_result_v1.json",
            ],
        ), self.assertRaises(SystemExit) as caught:
            cli_app.main()
        self.assertEqual(caught.exception.code, 2)

    def test_process_target_review_now_prints_request_ready_banner(self):
        from src.toy_apollo.cli import app as cli_app

        root = REPO_ROOT / "tests" / "_tmp_phase2_cli_review_now_banner"
        try:
            self._clean_root(root)
            task_id = "thm_4_cli_review_now_banner"
            ledger, settings, _, _ = self._setup_trivial_phase2_task(root, task_id)
            args = argparse.Namespace(
                phase=2,
                input="",
                tasks=task_id,
                task_ids=[task_id],
                phase2_mode="review-now",
                phase3_mode="soft-pack",
                candidate="",
                review_result="",
                review_subject="current",
                auto_apply_pass=False,
                abandon_current_repair=False,
                max_auto_rounds=6,
                nonprogress_limit=2,
                max_build_attempts_per_round=3,
                selection="",
                batch="",
                status=False,
            )
            with patch.object(cli_app, "get_settings", return_value=settings), patch(
                "src.toy_apollo.core.LedgerManager",
                return_value=ledger,
            ), patch(
                "src.toy_apollo.phase2_review_loop.run_codex_review_now",
                new=AsyncMock(return_value=(True, "detail")),
            ), patch("builtins.print") as print_mock:
                asyncio.run(cli_app.process_target(args))

            printed = " ".join(" ".join(str(item) for item in call.args) for call in print_mock.call_args_list)
            self.assertIn("review request ready", printed.lower())
            self.assertIn("reviewer step required now", printed.lower())
            self.assertNotIn("waiting", printed.lower())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_process_target_auto_loop_prints_continue_now_banner(self):
        from src.toy_apollo.cli import app as cli_app

        root = REPO_ROOT / "tests" / "_tmp_phase2_cli_auto_loop_banner"
        try:
            self._clean_root(root)
            task_id = "thm_4_cli_auto_loop_banner"
            ledger, settings, _, _ = self._setup_trivial_phase2_task(root, task_id)
            args = argparse.Namespace(
                phase=2,
                input="",
                tasks=task_id,
                task_ids=[task_id],
                phase2_mode="auto-loop",
                phase3_mode="soft-pack",
                candidate="",
                review_result="",
                review_subject="current",
                auto_apply_pass=False,
                abandon_current_repair=False,
                max_auto_rounds=6,
                nonprogress_limit=2,
                max_build_attempts_per_round=3,
                selection="",
                batch="",
                status=False,
            )
            with patch.object(cli_app, "get_settings", return_value=settings), patch(
                "src.toy_apollo.core.LedgerManager",
                return_value=ledger,
            ), patch(
                "src.toy_apollo.phase2_review_loop.run_codex_auto_loop",
                new=AsyncMock(return_value=(True, "detail")),
            ), patch("builtins.print") as print_mock:
                asyncio.run(cli_app.process_target(args))

            printed = " ".join(" ".join(str(item) for item in call.args) for call in print_mock.call_args_list)
            self.assertIn("continue this same-session step now", printed.lower())
            self.assertNotIn("waiting", printed.lower())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_process_target_auto_loop_rejects_multiple_tasks(self):
        from src.toy_apollo.cli import app as cli_app

        root = REPO_ROOT / "tests" / "_tmp_phase2_cli_auto_loop_multi_guard"
        try:
            self._clean_root(root)
            task_id = "thm_4_cli_auto_loop_multi_guard"
            ledger, settings, _, _ = self._setup_trivial_phase2_task(root, task_id)
            args = argparse.Namespace(
                phase=2,
                input="",
                tasks=f"{task_id},thm_4_cli_auto_loop_other",
                task_ids=[task_id, "thm_4_cli_auto_loop_other"],
                phase2_mode="auto-loop",
                phase3_mode="soft-pack",
                candidate="",
                review_result="",
                review_subject="current",
                auto_apply_pass=False,
                abandon_current_repair=False,
                max_auto_rounds=6,
                nonprogress_limit=2,
                max_build_attempts_per_round=3,
                selection="",
                batch="",
                status=False,
            )
            with patch.object(cli_app, "get_settings", return_value=settings), patch(
                "src.toy_apollo.core.LedgerManager",
                return_value=ledger,
            ), patch(
                "src.toy_apollo.phase2_review_loop.run_codex_auto_loop",
                new=AsyncMock(return_value=(True, "should not run")),
            ) as auto_loop_mock, patch("builtins.print") as print_mock:
                asyncio.run(cli_app.process_target(args))

            auto_loop_mock.assert_not_awaited()
            printed = " ".join(" ".join(str(item) for item in call.args) for call in print_mock.call_args_list)
            self.assertIn("exactly one task", printed.lower())
            self.assertIn("auto-loop", printed.lower())
        finally:
            shutil.rmtree(root, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
