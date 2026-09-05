import argparse
import asyncio
import io
import json
import os
import runpy
import shutil
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from dataclasses import replace
from pathlib import Path
from unittest.mock import AsyncMock, patch

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formalization_engine.phase2_handoff import ReviewLoopOutcome
from tests.phase2_review_test_support import Phase2ReviewTestSupport  # noqa: E402


class Phase2CliReviewTests(Phase2ReviewTestSupport, unittest.TestCase):
    def test_module_entrypoint_invokes_main(self):
        with patch.object(sys, "argv", ["app.py", "--help"]):
            with self.assertRaises(SystemExit) as exc:
                runpy.run_module("formalization_engine.cli.app", run_name="__main__")
        self.assertEqual(exc.exception.code, 0)

    def test_phase2_default_mode_is_pack(self):
        from formalization_engine.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "formalize",
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
        from formalization_engine.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "formalize",
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
        from formalization_engine.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "formalize",
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

    def test_cli_rejects_removed_review_support_and_debt_fix_modes(self):
        from formalization_engine.cli import app as cli_app

        for mode in ("review-support", "debt-fix"):
            with self.subTest(mode=mode), patch.object(
                sys,
                "argv",
                ["formalize", "--phase", "2", "--phase2-mode", mode, "--tasks", "thm_4_7"],
            ), patch.object(cli_app, "process_target", new=AsyncMock()) as process_target_mock, self.assertRaises(
                SystemExit
            ) as caught:
                cli_app.main()

            self.assertEqual(caught.exception.code, 2)
            process_target_mock.assert_not_awaited()

    def test_cli_rejects_removed_support_review_subject(self):
        from formalization_engine.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "formalize",
                "--phase",
                "2",
                "--phase2-mode",
                "review-now",
                "--tasks",
                "thm_4_7",
                "--review-subject",
                "support",
            ],
        ), patch.object(cli_app, "process_target", new=AsyncMock()) as process_target_mock, self.assertRaises(
            SystemExit
        ) as caught:
            cli_app.main()

        self.assertEqual(caught.exception.code, 2)
        process_target_mock.assert_not_awaited()

    def test_cli_promote_obligations_mode_is_rejected(self):
        from formalization_engine.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "formalize",
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
        from formalization_engine.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "formalize",
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
        from formalization_engine.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "formalize",
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
        from formalization_engine.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "formalize",
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
        from formalization_engine.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "formalize",
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
        from formalization_engine.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "formalize",
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
        from formalization_engine.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "formalize",
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
        from formalization_engine.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "formalize",
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
        from formalization_engine.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "formalize",
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
        from formalization_engine.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            ["formalize", "--phase", "2", "--phase2-mode", "soft-apply", "--tasks", "prob_4_2"],
        ), self.assertRaises(SystemExit) as caught:
            cli_app.main()
        self.assertEqual(caught.exception.code, 2)

    def test_cli_phase2_soft_modes_reject_non_problem_tasks(self):
        from formalization_engine.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            ["formalize", "--phase", "2", "--phase2-mode", "soft-pack", "--tasks", "thm_4_7"],
        ), self.assertRaises(SystemExit) as caught:
            cli_app.main()
        self.assertEqual(caught.exception.code, 2)

    def test_cli_rejects_removed_phase3_and_phase4(self):
        from formalization_engine.cli import app as cli_app

        for phase in ("3", "4"):
            with self.subTest(phase=phase), patch.object(
                sys,
                "argv",
                ["formalize", "--phase", phase],
            ), patch.object(cli_app, "process_target", new=AsyncMock()) as process_target_mock, self.assertRaises(
                SystemExit
            ) as caught:
                cli_app.main()

            self.assertEqual(caught.exception.code, 2)
            process_target_mock.assert_not_awaited()

    def test_cli_rejects_removed_audit_and_verify_modes(self):
        from formalization_engine.cli import app as cli_app

        for mode in ("audit", "verify"):
            with self.subTest(mode=mode), patch.object(
                sys,
                "argv",
                ["formalize", "--phase", "2", "--phase2-mode", mode, "--tasks", "thm_4_7"],
            ), self.assertRaises(SystemExit) as caught:
                cli_app.main()

            self.assertEqual(caught.exception.code, 2)

    def test_status_reports_default_source_and_does_not_create_missing_roots(self):
        from formalization_engine.cli import app as cli_app

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "missing-runtime"
            settings = replace(
                self._make_settings(root, root / "plans"),
                phase1_prompt_packs_dir=root / "phase1_prompt_packs",
                dependency_decisions_dir=root / "dependency_decisions",
            )
            stdout = io.StringIO()
            with patch.object(sys, "argv", ["formalize", "--status"]), patch.object(
                cli_app,
                "get_settings",
                return_value=settings,
            ), patch.object(cli_app, "process_target", new=AsyncMock()) as process_target_mock, patch.dict(
                os.environ,
                {},
                clear=True,
            ), redirect_stdout(stdout):
                code = cli_app.main()

            self.assertEqual(code, 0)
            output = stdout.getvalue()
            self.assertIn("STATUS_SCOPE=resolved_for_this_process_not_global_authority", output)
            self.assertIn(f"ARTIFACT_ROOT={root}", output)
            self.assertIn("ARTIFACT_ROOT_SOURCE=default", output)
            self.assertIn("ARTIFACT_ROOT_ENV_VAR=FORMALIZATION_ENGINE_ARTIFACT_ROOT", output)
            self.assertIn("ARTIFACT_ROOT_ENV_PRESENT=false", output)
            self.assertIn("ARTIFACT_ROOT_ENV_VALUE=<unset>", output)
            self.assertIn(f"PLAN_ROOT={root / 'plans'}", output)
            self.assertIn(f"LEDGER_ROOT={root}", output)
            self.assertIn(f"PHASE1_PROMPT_PACK_ROOT={root / 'phase1_prompt_packs'}", output)
            self.assertIn(f"PHASE2_PROMPT_PACK_ROOT={root / 'phase2_prompt_packs'}", output)
            self.assertIn(f"DEPENDENCY_DECISION_ROOT={root / 'dependency_decisions'}", output)
            self.assertIn(f"OUTPUT_ROOT={root / 'ProbabilityTheory'}", output)
            self.assertIn("LEDGER_STATUS=missing_not_created", output)
            self.assertFalse(root.exists())
            process_target_mock.assert_not_awaited()

    def test_status_reports_environment_values_and_preserves_existing_tree(self):
        from formalization_engine.cli import app as cli_app

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "runtime"
            root.mkdir()
            settings = replace(
                self._make_settings(root, root / "plans"),
                phase1_prompt_packs_dir=root / "phase1_prompt_packs",
                dependency_decisions_dir=root / "dependency_decisions",
            )
            settings.plans_dir.mkdir()
            settings.phase1_prompt_packs_dir.mkdir()
            settings.phase2_prompt_packs_dir.mkdir()
            settings.canonical_lean_dir.mkdir(parents=True)
            settings.project_ledger_file.write_text(
                json.dumps({"tasks": {}}, indent=2),
                encoding="utf-8",
            )
            (settings.plans_dir / "sentinel.json").write_text("plan sentinel\n", encoding="utf-8")
            (settings.phase1_prompt_packs_dir / "sentinel.txt").write_text("phase1 sentinel\n", encoding="utf-8")
            (settings.phase2_prompt_packs_dir / "sentinel.txt").write_text("phase2 sentinel\n", encoding="utf-8")
            (settings.canonical_lean_dir / "Sentinel.lean").write_text("theorem sentinel : True := by trivial\n", encoding="utf-8")

            def snapshot() -> dict[str, tuple[bytes, int]]:
                return {
                    path.relative_to(root).as_posix(): (path.read_bytes(), path.stat().st_mtime_ns)
                    for path in root.rglob("*")
                    if path.is_file()
                }

            before = snapshot()
            stdout = io.StringIO()
            env = {
                "FORMALIZATION_ENGINE_RUNTIME_ROOT": str(root),
                "FORMALIZATION_ENGINE_ARTIFACT_ROOT": str(root),
            }
            with patch.object(sys, "argv", ["formalize", "--status"]), patch.object(
                cli_app,
                "get_settings",
                return_value=settings,
            ), patch.object(cli_app, "process_target", new=AsyncMock()) as process_target_mock, patch.dict(
                os.environ,
                env,
                clear=True,
            ), redirect_stdout(stdout):
                code = cli_app.main()

            self.assertEqual(code, 0)
            output = stdout.getvalue()
            self.assertIn("ARTIFACT_ROOT_SOURCE=environment", output)
            self.assertIn("ARTIFACT_ROOT_ENV_PRESENT=true", output)
            self.assertIn(f"ARTIFACT_ROOT_ENV_VALUE={root}", output)
            self.assertIn("LEDGER_STATUS=legacy_present_frozen", output)
            self.assertEqual(snapshot(), before)
            self.assertFalse(settings.dependency_decisions_dir.exists())
            process_target_mock.assert_not_awaited()

    def test_status_reports_active_sqlite_campaign_when_legacy_json_is_absent(self):
        from formalization_engine.cli import app as cli_app

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "runtime"
            settings = replace(
                self._make_settings(root, root / "plans"),
                state_db_file=root / "state.sqlite3",
            )
            fake_store = type(
                "FakeStore",
                (),
                {
                    "exists": True,
                    "summary": lambda self: {
                        "schema_version": 1,
                        "subjects": 3,
                        "reviews": 2,
                        "task_heads": 3,
                    },
                },
            )()
            fake_ledger = type("FakeLedger", (), {"ledger": {"tasks": {"def_1": {}, "def_2": {}}}})()
            stdout = io.StringIO()

            with patch(
                "formalization_engine.state_store.WorkspaceStateStore",
                return_value=fake_store,
            ), patch(
                "formalization_engine.core.open_runtime_ledger",
                return_value=fake_ledger,
            ), redirect_stdout(stdout):
                cli_app.print_read_only_status(settings)

            output = stdout.getvalue()
            self.assertIn("CAMPAIGN_LEDGER_STATUS=loaded_read_only", output)
            self.assertIn("CAMPAIGN_LEDGER_TASKS=2", output)
            self.assertIn("LEGACY_LEDGER_STATUS=missing_not_created", output)
            self.assertIn("LEDGER_STATUS=active_sqlite_campaign", output)

    def test_status_rejects_operational_arguments_before_loading_settings(self):
        from formalization_engine.cli import app as cli_app

        stderr = io.StringIO()
        with patch.object(sys, "argv", ["formalize", "--status", "--phase", "2"]), patch.object(
            cli_app,
            "get_settings",
        ) as get_settings_mock, patch.object(
            cli_app,
            "process_target",
            new=AsyncMock(),
        ) as process_target_mock, redirect_stderr(stderr), self.assertRaises(SystemExit) as caught:
            cli_app.main()

        self.assertEqual(caught.exception.code, 2)
        self.assertIn("strictly read-only", stderr.getvalue())
        get_settings_mock.assert_not_called()
        process_target_mock.assert_not_awaited()

    def test_cli_rejects_removed_phase3_mode_flag(self):
        from formalization_engine.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "formalize",
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
        from formalization_engine.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            ["formalize", "--phase", "2", "--phase2-mode", "review-apply", "--tasks", "thm_4_cli_review"],
        ), self.assertRaises(SystemExit) as caught:
            cli_app.main()
        self.assertEqual(caught.exception.code, 2)

    def test_cli_review_result_is_only_for_review_apply(self):
        from formalization_engine.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "formalize",
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

    def test_process_target_batch_plan_opens_read_only_and_creates_no_directories(self):
        from formalization_engine.cli import app as cli_app
        from formalization_engine.core.settings import Settings

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            runtime = root / "runtime"
            artifact = root / "artifacts"
            settings = Settings(
                runtime_root=runtime,
                artifact_root=artifact,
                plans_dir=artifact / "plans",
                reports_dir=artifact / "reports",
                formalized_chapters_dir=artifact / "formalized_chapters",
                output_lean_files_dir=artifact / "output_lean_files",
                phase2_prompt_packs_dir=artifact / "phase2_prompt_packs",
                phase2_softdep_packs_dir=artifact / "phase2_softdep_packs",
                error_logs_dir=artifact / "error_logs",
                canonical_lean_dir=runtime / "ProbabilityTheory",
                canonical_manifest_required=False,
                aristotle_outbox_dir=artifact / "aristotle_outbox",
                aristotle_archives_dir=artifact / "aristotle_archives",
                mathlib_index_file=artifact / "mathlib_index.faiss",
                mathlib_corpus_file=artifact / "mathlib_corpus.json",
                project_ledger_file=artifact / "project_ledger.json",
                lab_notebook_file=artifact / "lab_notebook.json",
                mathlib_path=runtime / ".lake" / "packages" / "mathlib" / "Mathlib",
                phase0_ingestion_packs_dir=artifact / "phase0_ingestion_packs",
                phase1_prompt_packs_dir=artifact / "phase1_prompt_packs",
                dependency_decisions_dir=artifact / "dependency_decisions",
                workspace_root=root,
                state_db_file=root / "state.sqlite3",
            )
            ledger = type("FakeLedger", (), {"ledger": {"tasks": {}}})()
            args = argparse.Namespace(
                phase=2,
                input="",
                tasks="def_5_1",
                task_ids=["def_5_1"],
                phase2_mode="batch-plan",
                batch_task_kinds=[],
                batch_limit=0,
                batch_workers=0,
                batch_include_legacy=False,
            )

            with patch.object(cli_app, "get_settings", return_value=settings), patch(
                "formalization_engine.core.open_runtime_ledger",
                return_value=ledger,
            ) as open_ledger, patch(
                "formalization_engine.phase2_batch_runner.plan_batch_from_ledger",
                return_value=object(),
            ), patch(
                "formalization_engine.phase2_batch_runner.render_batch_runner_plan",
                return_value="# plan\n",
            ), patch("builtins.print"):
                asyncio.run(cli_app.process_target(args))

            open_ledger.assert_called_once_with(settings, read_only=True)
            self.assertFalse(runtime.exists())
            self.assertFalse(artifact.exists())

    def test_process_target_review_now_prints_request_ready_banner(self):
        from formalization_engine.cli import app as cli_app

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
                "formalization_engine.core.open_runtime_ledger",
                return_value=ledger,
            ), patch(
                "formalization_engine.phase2_review_loop.run_codex_review_now",
                new=AsyncMock(return_value=ReviewLoopOutcome(True, "detail", next_action="reviewer_write_result")),
            ), patch("builtins.print") as print_mock:
                asyncio.run(cli_app.process_target(args))

            printed = " ".join(" ".join(str(item) for item in call.args) for call in print_mock.call_args_list)
            self.assertIn("review request ready", printed.lower())
            self.assertIn("reviewer step required now", printed.lower())
            handoff_line = next(call.args[0] for call in print_mock.call_args_list if str(call.args[0]).startswith("PHASE2_HANDOFF_JSON="))
            handoff = json.loads(handoff_line.split("=", 1)[1])
            self.assertEqual(handoff["task_id"], task_id)
            self.assertEqual(handoff["next_action"], "reviewer_write_result")
            self.assertFalse(handoff["is_terminal"])
            self.assertNotIn("waiting", printed.lower())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_process_target_review_now_failure_exits_nonzero(self):
        from formalization_engine.cli import app as cli_app

        root = REPO_ROOT / "tests" / "_tmp_phase2_cli_review_now_failure"
        try:
            self._clean_root(root)
            task_id = "thm_4_cli_review_now_failure"
            ledger, settings, _, _ = self._setup_trivial_phase2_task(root, task_id)
            args = argparse.Namespace(
                phase=2,
                input="",
                tasks=task_id,
                task_ids=[task_id],
                phase2_mode="review-now",
                candidate="",
                review_result="",
                review_subject="existing",
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
                "formalization_engine.core.open_runtime_ledger",
                return_value=ledger,
            ), patch(
                "formalization_engine.phase2_review_loop.run_codex_review_now",
                new=AsyncMock(return_value=ReviewLoopOutcome(False, "basis changed", next_action="resolve_blocker")),
            ), patch("builtins.print"):
                with self.assertRaises(SystemExit) as caught:
                    asyncio.run(cli_app.process_target(args))

            self.assertEqual(caught.exception.code, 1)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_process_target_auto_loop_prints_continue_now_banner(self):
        from formalization_engine.cli import app as cli_app

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
                "formalization_engine.core.open_runtime_ledger",
                return_value=ledger,
            ), patch(
                "formalization_engine.phase2_review_loop.run_codex_auto_loop",
                new=AsyncMock(return_value=ReviewLoopOutcome(True, "detail", next_action="author_repair")),
            ), patch("builtins.print") as print_mock:
                asyncio.run(cli_app.process_target(args))

            printed = " ".join(" ".join(str(item) for item in call.args) for call in print_mock.call_args_list)
            self.assertIn("continue this same-session step now", printed.lower())
            self.assertNotIn("waiting", printed.lower())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_process_target_auto_loop_rejects_multiple_tasks(self):
        from formalization_engine.cli import app as cli_app

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
                "formalization_engine.core.open_runtime_ledger",
                return_value=ledger,
            ), patch(
                "formalization_engine.phase2_review_loop.run_codex_auto_loop",
                new=AsyncMock(return_value=(True, "should not run")),
            ) as auto_loop_mock, patch("builtins.print") as print_mock:
                asyncio.run(cli_app.process_target(args))

            auto_loop_mock.assert_not_awaited()
            printed = " ".join(" ".join(str(item) for item in call.args) for call in print_mock.call_args_list)
            self.assertIn("exactly one task", printed.lower())
        finally:
            shutil.rmtree(root, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
