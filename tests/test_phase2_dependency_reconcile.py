import asyncio
import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import AsyncMock, patch

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formalization_engine.ledger_manager import LedgerDependencyConflictError, TaskStatus  # noqa: E402
from formalization_engine.core.sqlite_ledger import SQLiteLedgerManager  # noqa: E402
from formalization_engine.phase2_batch_runner import plan_batch_from_ledger  # noqa: E402
from formalization_engine.phase2_dependency_reconcile import (  # noqa: E402
    DependencyReconciliationError,
    reconcile_phase2_task_dependencies,
)
from formalization_engine.phase2_pack_generation import resolve_phase2_task  # noqa: E402
from formalization_engine.phase2_prompt_pack import (  # noqa: E402
    apply_codex_review_result,
    write_existing_output_review_pack,
)
from formalization_engine.phase2_review_request import _validate_review_input_freshness  # noqa: E402
from formalization_engine.state_store import WorkspaceStateStore  # noqa: E402
from tests.phase2_review_test_support import Phase2ReviewTestSupport  # noqa: E402


class Phase2DependencyReconcileTests(Phase2ReviewTestSupport, unittest.TestCase):
    TASK_ID = "thm_7_6"
    WRONG_DEPENDENCIES = ["def_12_2", "def_9_1", "thm_7_13"]

    def _setup_contaminated_task(self, root: Path):
        ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(
            root,
            self.TASK_ID,
            completed=True,
        )
        plan_path = settings.plans_dir / "08_chap4_measurable_functions_plan.json"
        plan_payload = json.loads(plan_path.read_text(encoding="utf-8"))
        plan_payload[0]["source_plan"] = "08_chap4_measurable_functions"
        plan_path.write_text(json.dumps(plan_payload, indent=2), encoding="utf-8")
        ledger.add_or_update_task(
            {
                **plan_payload[0],
                "source_plan": "08_chap4_measurable_functions",
                "dependencies": self.WRONG_DEPENDENCIES,
            }
        )
        ledger.update_status(self.TASK_ID, TaskStatus.COMPLETED)
        ledger.update_runtime_metadata(
            self.TASK_ID,
            phase2_status="pass",
            phase2_task_status="pass",
            phase2_review_verdict="pass",
            phase2_proof_class="source_route_theorem",
            phase2_completion_class="source_route_theorem",
            latest_applied_review_subject_hash="old-subject",
            latest_applied_review_origin_basis_hash="old-origin-basis",
            latest_applied_review_post_basis_hash="old-post-basis",
            latest_applied_review_input_hash="old-input",
            latest_applied_review_result_file="old-result.json",
            latest_applied_review_result_hash="old-result-hash",
            latest_applied_review_subject_kind="official_output",
        )
        return ledger, settings, pack_dir, output_path, plan_path

    def test_single_task_reconciliation_uses_phase1_plan_and_records_audit(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            ledger, settings, _pack_dir, _output_path, plan_path = self._setup_contaminated_task(root)
            stale_pack_task = json.loads(
                (settings.phase2_prompt_packs_dir / self.TASK_ID / "task.json").read_text(encoding="utf-8")
            )
            stale_pack_task["dependencies"] = ["def_7_stale_pack"]
            stale_pack_task["final_import_union"] = ["def_7_stale_pack"]
            (settings.phase2_prompt_packs_dir / self.TASK_ID / "task.json").write_text(
                json.dumps(stale_pack_task),
                encoding="utf-8",
            )

            event = reconcile_phase2_task_dependencies(
                self.TASK_ID,
                ledger,
                settings,
                expected_old_dependencies=self.WRONG_DEPENDENCIES,
            )

            record = ledger.ledger["tasks"][self.TASK_ID]
            resolved = resolve_phase2_task(self.TASK_ID, ledger, settings)
            self.assertEqual(record["candidate_snapshot"]["dependencies"], [])
            self.assertEqual(resolved["dependencies"], [])
            self.assertNotIn("def_7_stale_pack", resolved["final_import_union"])
            self.assertEqual(event["previous_dependencies"], self.WRONG_DEPENDENCIES)
            self.assertEqual(event["reconciled_dependencies"], [])
            self.assertEqual(event["source_file"], "plans/08_chap4_measurable_functions_plan.json")
            self.assertEqual(event["source_file_sha256"], hashlib.sha256(plan_path.read_bytes()).hexdigest())
            self.assertEqual(record["dependency_reconciliation_history"], [event])
            self.assertEqual(record["latest_dependency_reconciliation"], event)
            self.assertEqual(record["dependency_reconciliation_revision"], 1)

    def test_cas_mismatch_is_atomic_and_leaves_pass_binding_untouched(self):
        with tempfile.TemporaryDirectory() as tmp:
            ledger, settings, _pack_dir, _output_path, _plan_path = self._setup_contaminated_task(Path(tmp))
            before = json.loads(json.dumps(ledger.ledger["tasks"][self.TASK_ID]))

            with self.assertRaisesRegex(DependencyReconciliationError, "compare-and-swap failed"):
                reconcile_phase2_task_dependencies(
                    self.TASK_ID,
                    ledger,
                    settings,
                    expected_old_dependencies=["def_12_2", "def_9_1"],
                )

            self.assertEqual(ledger.ledger["tasks"][self.TASK_ID], before)

    def test_sqlite_transaction_reloads_current_row_before_cas(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _legacy, settings, _pack_dir, _output_path, _plan_path = self._setup_contaminated_task(root)
            store = WorkspaceStateStore(root / "state.sqlite3")
            first = SQLiteLedgerManager(
                state_store=store,
                artifact_root=root,
                legacy_ledger_path=settings.project_ledger_file,
                campaign_id="test:dependency-reconcile",
            )
            stale = SQLiteLedgerManager(
                state_store=store,
                artifact_root=root,
                legacy_ledger_path=settings.project_ledger_file,
                campaign_id="test:dependency-reconcile",
            )
            first.reconcile_candidate_dependencies(
                self.TASK_ID,
                expected_dependencies=self.WRONG_DEPENDENCIES,
                replacement_dependencies=[],
                audit_event={"schema_version": "test", "reconciliation_id": "first"},
            )

            with self.assertRaisesRegex(LedgerDependencyConflictError, r"current \[\]"):
                stale.reconcile_candidate_dependencies(
                    self.TASK_ID,
                    expected_dependencies=self.WRONG_DEPENDENCIES,
                    replacement_dependencies=[],
                    audit_event={"schema_version": "test", "reconciliation_id": "stale"},
                )

            stored, _revision = store.load_campaign_ledger("test:dependency-reconcile")
            self.assertEqual(stored["tasks"][self.TASK_ID]["candidate_snapshot"]["dependencies"], [])
            self.assertEqual(
                stored["tasks"][self.TASK_ID]["latest_dependency_reconciliation"]["reconciliation_id"],
                "first",
            )

    def test_reconciliation_invalidates_review_pass_and_batch_routes_fresh_review(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            ledger, settings, _pack_dir, _output_path, _plan_path = self._setup_contaminated_task(root)

            reconcile_phase2_task_dependencies(
                self.TASK_ID,
                ledger,
                settings,
                expected_old_dependencies=self.WRONG_DEPENDENCIES,
            )
            record = ledger.ledger["tasks"][self.TASK_ID]
            plan = plan_batch_from_ledger([self.TASK_ID], ledger, settings)

            self.assertEqual(record["status"], TaskStatus.DISCOVERED.value)
            self.assertEqual(record["phase2_status"], "")
            self.assertEqual(record["phase2_task_status"], "")
            self.assertTrue(record["dependency_reconciliation_requires_fresh_review"])
            self.assertEqual(record["phase2_review_verdict"], "")
            self.assertEqual(record["latest_applied_review_post_basis_hash"], "")
            self.assertEqual(record["latest_applied_review_result_file"], "")
            self.assertEqual(record["latest_build_ready_candidate_hash"], "")
            self.assertEqual(plan.report.rows[0].dependencies, ())
            self.assertEqual(plan.report.rows[0].report_status, "needs_fresh_review")
            self.assertEqual(plan.actions[0].action, "review_existing")

    def test_dependency_drift_makes_already_prepared_review_input_stale(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            ledger, settings, pack_dir, _output_path, _plan_path = self._setup_contaminated_task(root)
            with patch(
                "formalization_engine.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = asyncio.run(
                    write_existing_output_review_pack(self.TASK_ID, ledger, settings)
                )
            self.assertTrue(success, detail)
            review_input = json.loads(
                (pack_dir / "semantic_review_input_v1.json").read_text(encoding="utf-8")
            )
            self.assertEqual(review_input["task"]["dependencies"], self.WRONG_DEPENDENCIES)

            reconcile_phase2_task_dependencies(
                self.TASK_ID,
                ledger,
                settings,
                expected_old_dependencies=self.WRONG_DEPENDENCIES,
            )
            error, _freshness = _validate_review_input_freshness(
                task=resolve_phase2_task(self.TASK_ID, ledger, settings),
                ledger=ledger,
                settings=settings,
                pack_dir=pack_dir,
                review_input=review_input,
            )

            self.assertIn("basis changed", error)

    def test_fresh_review_apply_satisfies_reconciliation_marker(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            ledger, settings, pack_dir, _output_path, _plan_path = self._setup_contaminated_task(root)
            event = reconcile_phase2_task_dependencies(
                self.TASK_ID,
                ledger,
                settings,
                expected_old_dependencies=self.WRONG_DEPENDENCIES,
            )
            with patch(
                "formalization_engine.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                review_success, review_detail = asyncio.run(
                    write_existing_output_review_pack(
                        self.TASK_ID,
                        ledger,
                        settings,
                        force_new_attempt=True,
                    )
                )
            self.assertTrue(review_success, review_detail)
            result_path = self._write_codex_review_result(pack_dir, verdict="pass")

            with patch(
                "formalization_engine.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "apply build ok"),
            ):
                success, detail = asyncio.run(
                    apply_codex_review_result(
                        self.TASK_ID,
                        ledger,
                        settings,
                        str(result_path),
                    )
                )

            self.assertTrue(success, detail)
            record = ledger.ledger["tasks"][self.TASK_ID]
            self.assertFalse(record["dependency_reconciliation_requires_fresh_review"])
            self.assertEqual(
                record["dependency_reconciliation_reviewed_id"],
                event["reconciliation_id"],
            )
            self.assertEqual(record["phase2_status"], "pass")

    def test_cli_requires_and_parses_expected_old_dependencies(self):
        from formalization_engine.cli import app as cli_app

        with patch.object(
            sys,
            "argv",
            [
                "formalize",
                "--phase",
                "2",
                "--phase2-mode",
                "dependency-reconcile",
                "--tasks",
                self.TASK_ID,
                "--expected-old-dependencies",
                ",".join(self.WRONG_DEPENDENCIES),
            ],
        ), patch.object(cli_app, "process_target", new=AsyncMock()) as process_target:
            self.assertEqual(cli_app.main(), 0)

        args = process_target.await_args.args[0]
        self.assertEqual(args.phase2_mode, "dependency-reconcile")
        self.assertEqual(args.expected_old_dependencies, self.WRONG_DEPENDENCIES)

        with patch.object(
            sys,
            "argv",
            [
                "formalize",
                "--phase",
                "2",
                "--phase2-mode",
                "dependency-reconcile",
                "--tasks",
                self.TASK_ID,
            ],
        ):
            with self.assertRaises(SystemExit) as caught:
                cli_app.main()
        self.assertEqual(caught.exception.code, 2)


if __name__ == "__main__":
    unittest.main()
