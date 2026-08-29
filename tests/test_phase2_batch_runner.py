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
    _dependencies_from_record,
    _normalize_kind,
    _obligation_fingerprint,
    _task_kind,
    build_live_batch_state,
    plan_batch_from_ledger,
    render_batch_runner_plan,
    run_batch_actions,
)
from src.toy_apollo.phase2_prompt_pack import (  # noqa: E402
    apply_codex_review_result,
    write_existing_output_review_pack,
)
from tests.phase2_review_test_support import Phase2ReviewTestSupport  # noqa: E402


class FakeLedger:
    def __init__(self, tasks):
        self.ledger = {"tasks": tasks}


class Phase2BatchRunnerTests(Phase2ReviewTestSupport, unittest.TestCase):
    def test_lemma_and_corollary_are_proof_bearing_batch_kinds(self):
        self.assertEqual(_normalize_kind("Lemma"), "theorem")
        self.assertEqual(_normalize_kind("Corollary"), "theorem")
        self.assertEqual(_task_kind("lem_18", {}), "theorem")
        self.assertEqual(_task_kind("cor_21", {}), "theorem")

    def _settings(self, root: Path):
        output_dir = root / "ToyApollo" / "Output"
        output_dir.mkdir(parents=True)
        plans_dir = root / "plans"
        plans_dir.mkdir(parents=True)
        return SimpleNamespace(
            toyapollo_output_dir=output_dir,
            phase2_prompt_packs_dir=root / "phase2_prompt_packs",
            plans_dir=plans_dir,
        )

    @staticmethod
    def _write_plan(settings, tasks):
        plan_path = settings.plans_dir / "chapter_test_plan.json"
        plan_path.write_text(json.dumps(tasks), encoding="utf-8")
        return plan_path

    def _setup_applied_dependency_with_historical_triage(
        self,
        root: Path,
        dependency_id: str,
        consumer_id: str,
        *,
        blocking_dependency_id: str = "",
        alias_current_result: bool = False,
    ):
        ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(
            root,
            dependency_id,
            completed=True,
        )
        if blocking_dependency_id:
            authority_plan_path = settings.plans_dir / "08_chap4_measurable_functions_plan.json"
            authority_tasks = json.loads(authority_plan_path.read_text(encoding="utf-8"))
            authority_tasks[0]["dependencies"] = [blocking_dependency_id]
            authority_tasks.append(
                {
                    "block_id": blocking_dependency_id,
                    "type": "Definition",
                    "title": "Unresolved basis dependency",
                    "content": "Supply the unresolved upstream basis.",
                    "dependencies": [],
                }
            )
            authority_plan_path.write_text(
                json.dumps(authority_tasks),
                encoding="utf-8",
            )
            ledger.update_runtime_metadata(
                dependency_id,
                dependencies=[blocking_dependency_id],
            )
            task_path = pack_dir / "task.json"
            task_payload = json.loads(task_path.read_text(encoding="utf-8"))
            task_payload["dependencies"] = [blocking_dependency_id]
            task_payload["final_import_union"] = [blocking_dependency_id]
            task_path.write_text(
                json.dumps(task_payload, indent=2, ensure_ascii=False),
                encoding="utf-8",
            )
            ledger.add_or_update_task(
                {
                    "block_id": blocking_dependency_id,
                    "type": "Definition",
                    "title": "Unresolved basis dependency",
                    "content": "Supply the unresolved upstream basis.",
                    "source_plan": "08_chap4_measurable_functions",
                    "dependencies": [],
                }
            )
            ledger.update_runtime_metadata(
                blocking_dependency_id,
                phase2_status="fail",
                phase2_status_reason="ordinary unresolved upstream basis",
            )
        self._append_direct_downstream_consumer(settings.plans_dir, dependency_id, consumer_id)
        ledger.add_or_update_task(
            {
                "block_id": consumer_id,
                "type": "Theorem",
                "title": "Downstream consumer",
                "content": "Consume the reviewed dependency.",
                "source_plan": "09_chap4_composition",
                "dependencies": [dependency_id],
            }
        )
        ledger.update_runtime_metadata(
            consumer_id,
            phase2_status="fail",
            phase2_status_reason="ordinary downstream repair remains",
        )
        with patch(
            "src.toy_apollo.phase2_prompt_pack._run_official_module_build",
            return_value=(True, "build ok"),
        ):
            success, detail = asyncio.run(
                write_existing_output_review_pack(
                    dependency_id,
                    ledger,
                    settings,
                    force_new_attempt=True,
                )
            )
        self.assertTrue(success, detail)
        result_path = self._write_codex_review_result(
            pack_dir,
            verdict="pass",
            proof_class="textbook_proof_completed",
            completion_class="textbook_proof_completed",
        )
        with patch(
            "src.toy_apollo.phase2_review_apply.run_official_module_build",
            return_value=(True, "build ok"),
        ):
            success, detail = asyncio.run(
                apply_codex_review_result(
                    dependency_id,
                    ledger,
                    settings,
                    str(result_path),
                )
            )
        self.assertTrue(success, detail)
        if alias_current_result:
            applied_result_path = Path(
                ledger.ledger["tasks"][dependency_id]["latest_applied_review_result_file"]
            )
            alias_result_path = pack_dir / "semantic_review_result.json"
            alias_result_path.write_bytes(applied_result_path.read_bytes())
            ledger.update_runtime_metadata(
                dependency_id,
                latest_semantic_review_result_file=str(alias_result_path),
            )

        triage_path = pack_dir / "historical_semantic_fail_triage.json"
        triage_path.write_text(
            json.dumps(
                {
                    "needs_diagnoser": True,
                    "local_repair_allowed": False,
                    "category": "historical_wrong_route",
                }
            ),
            encoding="utf-8",
        )
        ledger.update_runtime_metadata(
            dependency_id,
            latest_semantic_fail_triage_file=str(triage_path),
            latest_semantic_fail_triage_needs_diagnoser=True,
            latest_semantic_fail_triage_local_repair_allowed=False,
            latest_semantic_fail_triage_category="historical_wrong_route",
        )
        return ledger, settings, pack_dir, output_path

    def test_plan_backed_unregistered_tasks_feed_dependency_fanout_read_only(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            self._write_plan(
                settings,
                [
                    {
                        "block_id": "def_5_root",
                        "type": "Definition",
                        "content": "Root definition.",
                        "dependencies": [],
                        "source_plan": "chapter_test",
                    },
                    {
                        "block_id": "thm_5_downstream",
                        "type": "Theorem_Statement",
                        "content": "Downstream theorem.",
                        "dependencies": ["def_5_root"],
                        "source_plan": "chapter_test",
                    },
                ],
            )
            ledger = FakeLedger({})

            state = build_live_batch_state(
                ["def_5_root", "thm_5_downstream"],
                ledger,
                settings,
            )
            plan = plan_batch_from_ledger(
                ["def_5_root", "thm_5_downstream"],
                ledger,
                settings,
            )

        tasks = {task["task_id"]: task for task in state["tasks"]}
        actions = {action.task_id: action for action in plan.actions}
        self.assertEqual(tasks["thm_5_downstream"]["dependencies"], ["def_5_root"])
        self.assertEqual(actions["def_5_root"].fanout, 1)
        self.assertEqual(ledger.ledger["tasks"], {})

    def test_imported_record_missing_dependency_field_falls_back_to_plan(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            self._write_plan(
                settings,
                [
                    {
                        "block_id": "def_5_root",
                        "type": "Definition",
                        "content": "Root definition.",
                        "dependencies": [],
                        "source_plan": "chapter_test",
                    },
                    {
                        "block_id": "thm_5_downstream",
                        "type": "Theorem_Statement",
                        "content": "Plan theorem content.",
                        "dependencies": ["def_5_root"],
                        "source_plan": "chapter_test",
                    },
                ],
            )
            ledger = FakeLedger(
                {
                    "thm_5_downstream": {
                        "block_id": "thm_5_downstream",
                        "type": "Theorem_Statement",
                        "content": "Imported theorem content.",
                        "status": COMPLETED,
                    }
                }
            )

            state = build_live_batch_state(["thm_5_downstream"], ledger, settings)

        self.assertEqual(state["tasks"][0]["dependencies"], ["def_5_root"])
        self.assertNotIn("dependencies", ledger.ledger["tasks"]["thm_5_downstream"])

    def test_explicit_empty_ledger_dependencies_override_plan_fallback(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            self._write_plan(
                settings,
                [
                    {
                        "block_id": "thm_5_downstream",
                        "type": "Theorem_Statement",
                        "content": "Plan theorem content.",
                        "dependencies": ["def_5_root"],
                        "source_plan": "chapter_test",
                    }
                ],
            )
            ledger = FakeLedger(
                {
                    "thm_5_downstream": {
                        "block_id": "thm_5_downstream",
                        "type": "Theorem_Statement",
                        "content": "Imported theorem content.",
                        "dependencies": [],
                    }
                }
            )

            state = build_live_batch_state(["thm_5_downstream"], ledger, settings)

        self.assertEqual(state["tasks"][0]["dependencies"], [])

    def test_plan_resolution_preserves_runtime_fields_from_snapshot_only_record(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            self._write_plan(
                settings,
                [
                    {
                        "block_id": "thm_5_snapshot",
                        "type": "Theorem_Statement",
                        "content": "Plan theorem content.",
                        "dependencies": ["def_5_root"],
                        "source_plan": "chapter_test",
                    }
                ],
            )
            ledger = FakeLedger(
                {
                    "thm_5_snapshot": {
                        "block_id": "thm_5_snapshot",
                        "status": COMPLETED,
                        "phase2_status": "fail",
                        "phase2_status_reason": "historical semantic failure",
                        "latest_semantic_review_result_file": "old-review.json",
                        "candidate_snapshot": {
                            "dependencies": ["def_5_root"],
                        },
                    }
                }
            )

            state = build_live_batch_state(["thm_5_snapshot"], ledger, settings)

        task = state["tasks"][0]
        self.assertEqual(task["dependencies"], ["def_5_root"])
        self.assertEqual(task["phase2_status"], "fail")
        self.assertEqual(task["phase2_status_reason"], "historical semantic failure")
        self.assertEqual(
            ledger.ledger["tasks"]["thm_5_snapshot"]["latest_semantic_review_result_file"],
            "old-review.json",
        )

    def test_current_pack_import_manifest_overrides_stale_ledger_dependencies(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            self._write_plan(
                settings,
                [
                    {
                        "block_id": "thm_5_pack_current",
                        "type": "Theorem_Statement",
                        "content": "Plan theorem content.",
                        "dependencies": ["def_5_plan"],
                        "source_plan": "chapter_test",
                    }
                ],
            )
            pack_dir = settings.phase2_prompt_packs_dir / "thm_5_pack_current"
            pack_dir.mkdir(parents=True)
            (pack_dir / "task.json").write_text(
                json.dumps(
                    {
                        "block_id": "thm_5_pack_current",
                        "type": "Theorem_Statement",
                        "content": "Current packed theorem content.",
                        "dependencies": ["def_5_pack"],
                        "soft_imports": ["thm_5_soft"],
                        "final_import_union": ["def_5_pack", "thm_5_soft"],
                        "source_plan": "chapter_test",
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "thm_5_pack_current": {
                        "block_id": "thm_5_pack_current",
                        "type": "Theorem_Statement",
                        "content": "Stale ledger theorem content.",
                        "dependencies": ["def_5_stale"],
                        "status": COMPLETED,
                    }
                }
            )

            state = build_live_batch_state(["thm_5_pack_current"], ledger, settings)

        task = state["tasks"][0]
        self.assertEqual(task["dependencies"], ["def_5_pack", "thm_5_soft"])
        self.assertEqual(task["status"], COMPLETED)
        self.assertEqual(
            ledger.ledger["tasks"]["thm_5_pack_current"]["dependencies"],
            ["def_5_stale"],
        )

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

    def test_ledger_pass_with_legacy_unbound_review_requires_fresh_review(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            task_id = "thm_1_legacy_review"
            output_path = settings.toyapollo_output_dir / f"{task_id}.lean"
            output_path.write_text("import Mathlib\n\ntheorem thm_1_legacy_review : True := by trivial\n", encoding="utf-8")
            result_path = root / "phase2_prompt_packs" / task_id / "semantic_review_result_v1.json"
            result_path.parent.mkdir(parents=True)
            result_path.write_text(
                json.dumps(
                    {
                        "schema_version": "phase2.semantic_review.result.v1",
                        "task_id": task_id,
                        "verdict": "pass",
                        "proof_class": "textbook_proof_completed",
                        "completion_class": "textbook_proof_completed",
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    task_id: {
                        "block_id": task_id,
                        "type": "Theorem",
                        "status": COMPLETED,
                        "phase2_status": "pass",
                        "latest_official_review_result_file": str(result_path),
                    }
                }
            )

            plan = plan_batch_from_ledger([task_id], ledger, settings)

        self.assertEqual(plan.report.rows[0].report_status, "needs_fresh_review")
        self.assertEqual(plan.actions[0].action, "review_existing")

    def test_stale_review_freshness_routes_before_old_semantic_fail_triage(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            task_id = "def_3_stale_triage"
            output_path = settings.toyapollo_output_dir / f"{task_id}.lean"
            output_path.write_text("import Mathlib\n\ndef def_3_stale_triage : Prop := True\n", encoding="utf-8")
            pack_dir = settings.phase2_prompt_packs_dir / task_id
            pack_dir.mkdir(parents=True)
            legacy_result = pack_dir / "semantic_review_result_v1.json"
            legacy_result.write_text(
                json.dumps(
                    {
                        "schema_version": "phase2.semantic_review.result.v1",
                        "task_id": task_id,
                        "verdict": "pass",
                        "proof_class": "textbook_definition_completed",
                        "completion_class": "textbook_definition_completed",
                    }
                ),
                encoding="utf-8",
            )
            triage = pack_dir / "semantic_fail_triage.json"
            triage.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "mathlib_adapter",
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    task_id: {
                        "block_id": task_id,
                        "type": "Definition",
                        "status": COMPLETED,
                        "phase2_status": "pass",
                        "latest_official_review_result_file": str(legacy_result),
                        "latest_semantic_fail_triage_file": str(triage),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                        "latest_semantic_fail_triage_local_repair_allowed": False,
                        "latest_semantic_fail_triage_category": "mathlib_adapter",
                    }
                }
            )

            plan = plan_batch_from_ledger([task_id], ledger, settings)

        self.assertEqual(plan.report.rows[0].report_status, "needs_fresh_review")
        self.assertEqual(plan.actions[0].action, "review_existing")
        self.assertIn("--review-subject existing", plan.actions[0].command)

    def test_fresh_review_with_illegal_class_is_not_counted_as_pass(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            task_id = "thm_1_illegal_class"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(
                root,
                task_id,
                completed=True,
            )
            with patch(
                "src.toy_apollo.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = asyncio.run(write_existing_output_review_pack(task_id, ledger, settings))
            self.assertTrue(success, detail)
            result_path = self._write_codex_review_result(
                pack_dir,
                verdict="pass",
                proof_class="textbook_proof_completed",
                completion_class="semantically_complete",
            )
            ledger.update_runtime_metadata(
                task_id,
                phase2_status="pass",
                latest_official_review_result_file=str(result_path),
            )

            plan = plan_batch_from_ledger([task_id], ledger, settings)

        self.assertEqual(plan.report.rows[0].report_status, "needs_class_normalization")
        self.assertEqual(plan.actions[0].action, "review_existing")

    def test_only_fresh_applied_review_is_counted_as_pass(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            task_id = "thm_1_fresh_applied"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(
                root,
                task_id,
                completed=True,
            )
            with patch(
                "src.toy_apollo.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = asyncio.run(write_existing_output_review_pack(task_id, ledger, settings))
            self.assertTrue(success, detail)
            result_path = self._write_codex_review_result(
                pack_dir,
                verdict="pass",
                proof_class="textbook_proof_completed",
                completion_class="textbook_proof_completed",
            )
            with patch(
                "src.toy_apollo.phase2_review_apply.run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = asyncio.run(
                    apply_codex_review_result(task_id, ledger, settings, str(result_path))
                )
            self.assertTrue(success, detail)

            plan = plan_batch_from_ledger([task_id], ledger, settings)

        self.assertEqual(plan.report.rows[0].report_status, "pass")
        self.assertEqual(plan.report.rows[0].task_status, "pass")

    def test_alias_current_result_matching_versioned_applied_receipt_ignores_historical_triage_for_basis_only_stale_pass(
        self,
    ):
        with tempfile.TemporaryDirectory() as tmp:
            dependency_id = "thm_42_clean_dependency"
            consumer_id = "thm_42_downstream_consumer"
            blocking_dependency_id = "def_42_unresolved_basis"
            ledger, settings, _, _ = self._setup_applied_dependency_with_historical_triage(
                Path(tmp),
                dependency_id,
                consumer_id,
                blocking_dependency_id=blocking_dependency_id,
                alias_current_result=True,
            )
            record = ledger.ledger["tasks"][dependency_id]
            current_result_path = Path(record["latest_semantic_review_result_file"])
            applied_result_path = Path(record["latest_applied_review_result_file"])
            result_paths_are_distinct = (
                current_result_path.resolve() != applied_result_path.resolve()
            )
            result_bytes_match = (
                current_result_path.read_bytes() == applied_result_path.read_bytes()
            )

            state = build_live_batch_state([consumer_id], ledger, settings)
            plan = plan_batch_from_ledger([consumer_id], ledger, settings)

        self.assertTrue(result_paths_are_distinct)
        self.assertTrue(result_bytes_match)
        projected_tasks = {task["task_id"]: task for task in state["tasks"]}
        self.assertTrue(
            projected_tasks[dependency_id]["latest_clean_applied_review_is_current"]
        )
        rows = {row.task_id: row for row in plan.report.rows}
        self.assertEqual(rows[dependency_id].report_status, "needs_fresh_review")
        self.assertEqual(rows[dependency_id].blocked_dependency, blocking_dependency_id)
        self.assertEqual(plan.actions[0].task_id, consumer_id)
        self.assertEqual(plan.actions[0].action, "skip_blocked")
        self.assertIn(blocking_dependency_id, plan.actions[0].reason)
        self.assertNotIn("diagnoser", plan.actions[0].reason)
        self.assertNotIn("historical_wrong_route", plan.actions[0].reason)

    def test_alias_current_result_identity_stays_fail_closed_for_content_or_receipt_mismatch(self):
        for mismatch in ("different_content", "input_receipt"):
            with self.subTest(mismatch=mismatch), tempfile.TemporaryDirectory() as tmp:
                dependency_id = f"thm_42_alias_{mismatch}_dependency"
                consumer_id = f"thm_42_alias_{mismatch}_consumer"
                ledger, settings, pack_dir, _ = (
                    self._setup_applied_dependency_with_historical_triage(
                        Path(tmp),
                        dependency_id,
                        consumer_id,
                        blocking_dependency_id=f"def_42_alias_{mismatch}_basis",
                        alias_current_result=True,
                    )
                )
                record = ledger.ledger["tasks"][dependency_id]
                if mismatch == "different_content":
                    alias_result_path = pack_dir / "semantic_review_result.json"
                    alias_result = json.loads(alias_result_path.read_text(encoding="utf-8"))
                    alias_result["summary"] = "different current review result"
                    alias_result_path.write_text(
                        json.dumps(alias_result, indent=2, ensure_ascii=False),
                        encoding="utf-8",
                    )
                else:
                    ledger.update_runtime_metadata(
                        dependency_id,
                        latest_applied_review_input_hash="mismatched-review-input-receipt",
                    )

                state = build_live_batch_state([consumer_id], ledger, settings)
                plan = plan_batch_from_ledger([consumer_id], ledger, settings)

            self.assertNotEqual(
                Path(record["latest_semantic_review_result_file"]).resolve(),
                Path(record["latest_applied_review_result_file"]).resolve(),
            )
            projected_tasks = {task["task_id"]: task for task in state["tasks"]}
            self.assertFalse(
                projected_tasks[dependency_id]["latest_clean_applied_review_is_current"]
            )
            self.assertEqual(plan.actions[0].task_id, consumer_id)
            self.assertEqual(plan.actions[0].action, "skip_blocked")
            self.assertIn("diagnoser-required semantic failure", plan.actions[0].reason)
            self.assertIn(dependency_id, plan.actions[0].reason)

    def test_nonconsumable_dependency_authority_keeps_historical_diagnoser_blocker(self):
        for authority_state in ("needs_fresh_review", "current_fail"):
            with self.subTest(authority_state=authority_state), tempfile.TemporaryDirectory() as tmp:
                dependency_id = f"thm_42_{authority_state}_dependency"
                consumer_id = f"thm_42_{authority_state}_consumer"
                ledger, settings, pack_dir, output_path = (
                    self._setup_applied_dependency_with_historical_triage(
                        Path(tmp),
                        dependency_id,
                        consumer_id,
                    )
                )
                if authority_state == "needs_fresh_review":
                    output_path.write_text(
                        output_path.read_text(encoding="utf-8") + "\n-- authority drift\n",
                        encoding="utf-8",
                    )
                else:
                    with patch(
                        "src.toy_apollo.phase2_prompt_pack._run_official_module_build",
                        return_value=(True, "build ok"),
                    ):
                        success, detail = asyncio.run(
                            write_existing_output_review_pack(
                                dependency_id,
                                ledger,
                                settings,
                                force_new_attempt=True,
                            )
                        )
                    self.assertTrue(success, detail)
                    fail_result_path = self._write_codex_review_result(
                        pack_dir,
                        verdict="fail",
                        proof_class="open_math_debt",
                        completion_class="open_math_debt",
                    )
                    success, detail = asyncio.run(
                        apply_codex_review_result(
                            dependency_id,
                            ledger,
                            settings,
                            str(fail_result_path),
                        )
                    )
                    self.assertFalse(success, detail)

                plan = plan_batch_from_ledger([consumer_id], ledger, settings)

                rows = {row.task_id: row for row in plan.report.rows}
                expected_status = "needs_fresh_review" if authority_state == "needs_fresh_review" else "fail"
                self.assertEqual(rows[dependency_id].report_status, expected_status)
                self.assertEqual(plan.actions[0].task_id, consumer_id)
                self.assertEqual(plan.actions[0].action, "skip_blocked")
                self.assertIn("diagnoser-required semantic failure", plan.actions[0].reason)
                self.assertIn(dependency_id, plan.actions[0].reason)

    def test_fresh_but_unapplied_pass_result_is_not_counted_as_pass(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            task_id = "thm_1_fresh_unapplied"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(
                root,
                task_id,
                completed=True,
            )
            with patch(
                "src.toy_apollo.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = asyncio.run(write_existing_output_review_pack(task_id, ledger, settings))
            self.assertTrue(success, detail)
            result_path = self._write_codex_review_result(
                pack_dir,
                verdict="pass",
                proof_class="textbook_proof_completed",
                completion_class="textbook_proof_completed",
            )
            ledger.update_runtime_metadata(
                task_id,
                phase2_status="pass",
                latest_official_review_result_file=str(result_path),
            )

            plan = plan_batch_from_ledger([task_id], ledger, settings)

        self.assertEqual(plan.report.rows[0].report_status, "needs_fresh_review")
        self.assertIn("review-apply", plan.report.rows[0].task_status_reason)

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

    def test_family_completion_class_not_summary_routes_to_inspection(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            review_result = root / "phase2_prompt_packs" / "thm_7_8" / "semantic_review_result_v6.json"
            review_result.parent.mkdir(parents=True)
            review_result.write_text(
                json.dumps(
                    {
                        "verdict": "fail",
                        "proof_class": "source_route_support_completed_downstream_blocked",
                        "completion_class": "not_completed_downstream_blocked",
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "thm_7_8": {
                        "block_id": "thm_7_8",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "current_review_expected_result_file": str(review_result),
                    }
                }
            )

            plan = plan_batch_from_ledger(["thm_7_8"], ledger, settings)

        self.assertEqual(plan.actions[0].action, "inspect")
        self.assertEqual(plan.actions[0].command, "")
        self.assertIn("direct downstream obligations", plan.actions[0].reason)

    def test_worker_selection_reports_omitted_inspection_as_not_completion(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            ledger = FakeLedger(
                {
                    "def_1_2": {
                        "block_id": "def_1_2",
                        "type": "Definition",
                        "status": NONTERMINAL,
                    }
                }
            )

            plan = plan_batch_from_ledger(["def_1_2"], ledger, settings, limit=20)
            rendered = render_batch_runner_plan(plan)

        self.assertEqual(plan.actions, ())
        self.assertIn("visible actions omitted by worker selection: `1` (inspect=1)", rendered)
        self.assertIn("selected-worker-queue-empty-is-not-completion", rendered)
        self.assertIn("Inspection is still required for: def_1_2", rendered)

    def test_semantic_fail_triage_requiring_diagnoser_is_not_auto_looped(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            triage_path = root / "phase2_prompt_packs" / "def_1_2" / "semantic_fail_triage.json"
            triage_path.parent.mkdir(parents=True)
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "public_premise",
                        "prompt_path": str(triage_path.with_name("prepared_diagnoser_prompt.txt")),
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "def_1_2": {
                        "block_id": "def_1_2",
                        "type": "Definition",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "core obligation moved into a public premise",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    }
                }
            )

            plan = plan_batch_from_ledger(["def_1_2"], ledger, settings)

        self.assertEqual(plan.actions[0].action, "diagnoser_required")
        self.assertEqual(plan.actions[0].command, "")
        self.assertIn("public_premise", plan.actions[0].reason)
        self.assertIn("read-only diagnoser", plan.actions[0].reason)

    def test_obligation_pack_manifest_overrides_stale_batch_plan_dependencies(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            task_id = "obl_obl_prob_14_1_obligation_1_concrete_child"
            pack_dir = settings.phase2_prompt_packs_dir / task_id
            pack_dir.mkdir(parents=True)
            (pack_dir / "task.json").write_text(
                json.dumps(
                    {
                        "block_id": task_id,
                        "type": "Phase2ObligationTask",
                        "content": "Focused child.",
                        "dependencies": ["prob_13_11"],
                        "soft_imports": ["prob_14_1"],
                        "final_import_union": ["prob_13_11", "prob_14_1"],
                    }
                ),
                encoding="utf-8",
            )
            stale_record = {
                "block_id": task_id,
                "type": "Phase2ObligationTask",
                "dependencies": ["prob_14_1", "old_nonimportable_child"],
                "soft_imports": ["prob_14_1"],
                "final_import_union": ["prob_14_1", "old_nonimportable_child"],
            }

            deps = _dependencies_from_record(stale_record, task_id=task_id, settings=settings)

        self.assertEqual(deps, ["prob_13_11"])

    def test_diagnoser_result_requiring_source_rewrite_returns_author_action(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = root / "phase2_prompt_packs" / "thm_1_2"
            pack_dir.mkdir(parents=True)
            triage_path = pack_dir / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "wrong_route",
                        "prompt_path": str(pack_dir / "prepared_diagnoser_prompt.txt"),
                    }
                ),
                encoding="utf-8",
            )
            (pack_dir / "diagnoser_result_v2.json").write_text(
                json.dumps(
                    {
                        "diagnosis_verdict": "route_rewrite_required",
                        "route_wrong": True,
                        "statement_mismatch": False,
                        "local_repair_allowed": False,
                        "recommended_next_action": "rewrite the source-facing proof decomposition",
                        "forbidden_shortcuts": ["do not continue patching private axioms"],
                        "required_local_checks": [],
                        "rationale": "The current route hides the source spine and needs decomposition first.",
                    }
                ),
                encoding="utf-8",
            )
            obligation = {
                "id": "bridge",
                "kind": "source_step",
                "status": "blocked",
                "source_ref": "source bridge",
                "lean_landing": "bridge_landing",
                "notes": "promote this bridge",
                "depends_on": [],
                "scaffold_hypotheses": [],
                "source_output_alignment": {},
            }
            (pack_dir / "proof_obligations.json").write_text(
                json.dumps({"obligations": [obligation]}),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "thm_1_2": {
                        "block_id": "thm_1_2",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "current route hides the source spine",
                        "current_auto_loop_stop_reason": "diagnoser_required",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    }
                }
            )

            plan = plan_batch_from_ledger(
                ["thm_1_2"],
                ledger,
                settings,
                task_kinds=["theorem"],
                limit=1,
                worker_slots=1,
            )
            rendered = render_batch_runner_plan(plan)

        self.assertEqual(len(plan.actions), 1)
        self.assertEqual(plan.actions[0].action, "auto_loop")
        self.assertIn("--phase2-mode auto-loop", plan.actions[0].command)
        self.assertIn("diagnoser_result local_repair_allowed=false", plan.actions[0].reason)
        self.assertIn("source-facing rewrite/decomposition", plan.actions[0].reason)
        self.assertNotIn("subagent-dispatch-required", rendered)

    def test_math_review_gate_blocks_risky_task_before_author_loop(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = root / "phase2_prompt_packs" / "prob_14_1"
            pack_dir.mkdir(parents=True)
            triage_path = pack_dir / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "public_premise",
                        "prompt_path": str(pack_dir / "prepared_diagnoser_prompt.txt"),
                    }
                ),
                encoding="utf-8",
            )
            (pack_dir / "diagnoser_result_v1.json").write_text(
                json.dumps(
                    {
                        "diagnosis_verdict": "route_rewrite_required",
                        "route_wrong": True,
                        "statement_mismatch": False,
                        "local_repair_allowed": False,
                        "recommended_next_action": "write a source-facing proof skeleton before Lean authoring",
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "prob_14_1": {
                        "block_id": "prob_14_1",
                        "type": "Problem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "semantic_fail_public_premise: white-count law moved into setup",
                        "current_auto_loop_stop_reason": "diagnoser_required",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    }
                }
            )

            plan = plan_batch_from_ledger(["prob_14_1"], ledger, settings, limit=1, worker_slots=1)
            rendered = render_batch_runner_plan(plan)

        self.assertEqual(plan.all_actions[0].action, "math_review_gate_required")
        self.assertEqual(plan.all_actions[0].command, "")
        self.assertIn("Math Review Gate", plan.all_actions[0].reason)
        self.assertIn("public_premise", plan.all_actions[0].reason)
        self.assertNotIn("--phase2-mode auto-loop", rendered)
        self.assertIn("math_review_gate_required", rendered)

    def test_math_review_gate_go_allows_author_loop(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = root / "phase2_prompt_packs" / "prob_14_1"
            pack_dir.mkdir(parents=True)
            triage_path = pack_dir / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "public_premise",
                        "prompt_path": str(pack_dir / "prepared_diagnoser_prompt.txt"),
                    }
                ),
                encoding="utf-8",
            )
            (pack_dir / "diagnoser_result_v1.json").write_text(
                json.dumps(
                    {
                        "diagnosis_verdict": "route_rewrite_required",
                        "route_wrong": True,
                        "statement_mismatch": False,
                        "local_repair_allowed": False,
                        "recommended_next_action": "rewrite from the source-facing proof skeleton",
                    }
                ),
                encoding="utf-8",
            )
            (pack_dir / "math_proof_skeleton_v1.md").write_text(
                "# Math Proof Skeleton\n\nSource-faithful proof route.",
                encoding="utf-8",
            )
            (pack_dir / "math_review_result_v1.json").write_text(
                json.dumps({"verdict": "go", "rounds": [{"round": 1}, {"round": 2}, {"round": 3}]}),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "prob_14_1": {
                        "block_id": "prob_14_1",
                        "type": "Problem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "semantic_fail_public_premise: white-count law moved into setup",
                        "current_auto_loop_stop_reason": "diagnoser_required",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    }
                }
            )

            plan = plan_batch_from_ledger(["prob_14_1"], ledger, settings, limit=1, worker_slots=1)

        self.assertEqual(plan.actions[0].action, "auto_loop")
        self.assertIn("--phase2-mode auto-loop", plan.actions[0].command)
        self.assertIn("diagnoser_result local_repair_allowed=false", plan.actions[0].reason)

    def test_math_review_gate_stop_blocking_proof_surfaces_blocker_not_author_loop(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = root / "phase2_prompt_packs" / "prob_14_1"
            pack_dir.mkdir(parents=True)
            (pack_dir / "math_proof_skeleton_v8.md").write_text(
                "# Math Proof Skeleton\n\nAnalytic convergence is the remaining blocker.",
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
                        "forbidden_work": ["ToyApollo/Output promotion", "semantic review"],
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "prob_14_1": {
                        "block_id": "prob_14_1",
                        "type": "Problem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "private_axiom_or_open_math_debt",
                    }
                }
            )

            plan = plan_batch_from_ledger(["prob_14_1"], ledger, settings, limit=1, worker_slots=1)
            rendered = render_batch_runner_plan(plan)

        self.assertEqual(plan.all_actions[0].action, "blocking_proof_required")
        self.assertEqual(plan.all_actions[0].command, "")
        self.assertIn("blocking_proof", plan.all_actions[0].reason)
        self.assertIn("prob_14_1_stirling_beta_cdf_convergence_internal", plan.all_actions[0].reason)
        self.assertIn("gamma_ratio_global_power_bound", plan.all_actions[0].reason)
        self.assertIn("pre-author checklist", plan.all_actions[0].reason)
        self.assertIn("source statement identified", plan.all_actions[0].reason)
        self.assertIn("no public premise relocation", plan.all_actions[0].reason)
        self.assertIn("math proof skeleton reviewed go", plan.all_actions[0].reason)
        self.assertIn("independent semantic review after build", plan.all_actions[0].reason)
        self.assertNotIn("--phase2-mode auto-loop", rendered)

    def test_math_review_gate_missing_skeleton_surfaces_pre_author_checklist(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            ledger = FakeLedger(
                {
                    "prob_14_1": {
                        "block_id": "prob_14_1",
                        "type": "Problem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "semantic_fail_public_premise: white-count law moved into setup",
                    }
                }
            )

            plan = plan_batch_from_ledger(["prob_14_1"], ledger, settings)

        self.assertEqual(plan.actions[0].action, "math_review_gate_required")
        self.assertIn("pre-author checklist", plan.actions[0].reason)
        self.assertIn("source statement identified", plan.actions[0].reason)
        self.assertIn("no public premise relocation", plan.actions[0].reason)
        self.assertIn("math proof skeleton reviewed go", plan.actions[0].reason)
        self.assertIn("independent semantic review after build", plan.actions[0].reason)

    def test_diagnoser_result_requiring_obligation_promotion_routes_to_absorption(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = root / "phase2_prompt_packs" / "ex_14_4_1"
            pack_dir.mkdir(parents=True)
            triage_path = pack_dir / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "private_axiom_or_open_math_debt",
                        "prompt_path": str(pack_dir / "prepared_diagnoser_prompt.txt"),
                    }
                ),
                encoding="utf-8",
            )
            (pack_dir / "diagnoser_result_v2.json").write_text(
                json.dumps(
                    {
                        "diagnosis_verdict": "explicit_child_obligation_promotion",
                        "route_wrong": False,
                        "statement_mismatch": False,
                        "local_repair_allowed": False,
                        "recommended_next_action": "promote child obligations for the unresolved source bridges",
                        "forbidden_shortcuts": ["do not keep public bridge premises"],
                        "required_local_checks": [],
                        "rationale": "The route is right but the unresolved bridges must be split into child obligations.",
                    }
                ),
                encoding="utf-8",
            )
            obligation = {
                "id": "bridge",
                "kind": "source_step",
                "status": "blocked",
                "source_ref": "source bridge",
                "lean_landing": "bridge_landing",
                "notes": "promote this bridge",
                "depends_on": [],
                "scaffold_hypotheses": [],
                "source_output_alignment": {},
            }
            (pack_dir / "proof_obligations.json").write_text(
                json.dumps({"obligations": [obligation]}),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "ex_14_4_1": {
                        "block_id": "ex_14_4_1",
                        "type": "Exercise",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "source bridges are open debt",
                        "current_auto_loop_stop_reason": "diagnoser_required",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    }
                }
            )

            plan = plan_batch_from_ledger(
                ["ex_14_4_1"],
                ledger,
                settings,
                task_kinds=["exercise"],
                limit=1,
                worker_slots=1,
            )

        self.assertEqual(len(plan.actions), 1)
        self.assertEqual(plan.actions[0].action, "foundation_absorb_required")
        self.assertEqual(plan.actions[0].command, "")
        self.assertIn("diagnoser_result local_repair_allowed=false", plan.actions[0].reason)
        self.assertIn("obligation child promotion is disabled", plan.actions[0].reason)
        self.assertIn("absorb proof obligations into parent/support files", plan.actions[0].reason)

    def test_deeper_child_obligation_promotion_diagnosis_routes_to_absorption(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            task_id = "obl_obl_prob_14_12_obligation_5_obligation_5_limit_truncation_tail"
            pack_dir = root / "phase2_prompt_packs" / task_id
            pack_dir.mkdir(parents=True)
            triage_path = pack_dir / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "private_axiom_or_open_math_debt",
                        "prompt_path": str(pack_dir / "prepared_diagnoser_prompt.txt"),
                    }
                ),
                encoding="utf-8",
            )
            (pack_dir / "diagnoser_result_v1.json").write_text(
                json.dumps(
                    {
                        "diagnosis_kind": "deeper_child_obligation_promotion",
                        "diagnosis_verdict": "promotion_required_not_ordinary_local_repair",
                        "route_wrong": False,
                        "statement_mismatch": True,
                        "local_repair_allowed": False,
                        "recommended_next_action": (
                            "Promote or prove the missing bridge obligations before semantic review."
                        ),
                        "required_child_obligations": [
                            {
                                "id": "convergence_probability_extracts_ae_subsequence",
                                "status": "open",
                            }
                        ],
                        "forbidden_shortcuts": ["do not expose missing bridges as public hypotheses"],
                        "required_local_checks": [],
                        "rationale": "The source route is right but needs deeper child obligations.",
                    }
                ),
                encoding="utf-8",
            )
            obligation = {
                "id": "limit_truncation_tail_assembly",
                "kind": "source_step",
                "status": "blocked",
                "source_ref": "limit truncation tail route",
                "lean_landing": "prob_14_12_limit_truncation_tail_obligation",
                "notes": "promote deeper route obligations",
                "depends_on": [],
                "scaffold_hypotheses": [],
                "source_output_alignment": {},
            }
            (pack_dir / "proof_obligations.json").write_text(
                json.dumps({"obligations": [obligation]}),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    task_id: {
                        "block_id": task_id,
                        "type": "Phase2ObligationTask",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "limit truncation tail still exposes public bridge premises",
                        "current_auto_loop_stop_reason": "diagnoser_required",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    }
                }
            )

            plan = plan_batch_from_ledger(
                [task_id],
                ledger,
                settings,
                limit=1,
                worker_slots=1,
                include_legacy=True,
            )

        self.assertEqual(len(plan.actions), 1)
        self.assertEqual(plan.actions[0].action, "foundation_absorb_required")
        self.assertEqual(plan.actions[0].command, "")
        self.assertIn("deeper_child_obligation_promotion", plan.actions[0].reason)
        self.assertIn("obligation child promotion is disabled", plan.actions[0].reason)

    def test_existing_child_obligations_do_not_drive_parent_promotion(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = root / "phase2_prompt_packs" / "ex_14_4_1"
            pack_dir.mkdir(parents=True)
            triage_path = pack_dir / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "private_axiom_or_open_math_debt",
                    }
                ),
                encoding="utf-8",
            )
            (pack_dir / "diagnoser_result_v2.json").write_text(
                json.dumps(
                    {
                        "diagnosis_verdict": "explicit_child_obligation_promotion",
                        "route_wrong": False,
                        "statement_mismatch": False,
                        "local_repair_allowed": False,
                        "recommended_next_action": "promote child obligations",
                        "forbidden_shortcuts": [],
                        "required_local_checks": [],
                        "rationale": "Split the open debt into child tasks.",
                    }
                ),
                encoding="utf-8",
            )
            obligation = {
                "id": "bridge",
                "kind": "source_step",
                "status": "blocked",
                "source_ref": "source bridge",
                "lean_landing": "bridge_landing",
                "notes": "promote this bridge",
                "depends_on": [],
                "scaffold_hypotheses": [],
                "source_output_alignment": {},
            }
            (pack_dir / "proof_obligations.json").write_text(
                json.dumps({"obligations": [obligation]}),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "ex_14_4_1": {
                        "block_id": "ex_14_4_1",
                        "type": "Exercise",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "current_auto_loop_stop_reason": "diagnoser_required",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    },
                    "obl_ex_14_4_1_bridge": {
                        "block_id": "obl_ex_14_4_1_bridge",
                        "type": "Phase2ObligationTask",
                        "status": NONTERMINAL,
                        "parent_block_id": "ex_14_4_1",
                        "obligation_fingerprint": _obligation_fingerprint("ex_14_4_1", obligation),
                    },
                }
            )

            unfiltered = plan_batch_from_ledger(["ex_14_4_1"], ledger, settings)
            queued = plan_batch_from_ledger(
                ["ex_14_4_1"],
                ledger,
                settings,
                task_kinds=["exercise"],
                limit=1,
                worker_slots=1,
            )
            rendered = render_batch_runner_plan(queued)

        self.assertEqual(unfiltered.actions[0].action, "foundation_absorb_required")
        self.assertEqual(unfiltered.actions[0].command, "")
        self.assertIn("obligation child promotion is disabled", unfiltered.actions[0].reason)
        self.assertEqual(len(queued.actions), 1)
        self.assertEqual(queued.actions[0].action, "foundation_absorb_required")
        self.assertIn("| 1 | ex_14_4_1 | exercise", rendered)
        self.assertIn("| fail | fail | foundation_absorb_required |", rendered)

    def test_diagnoser_result_allowing_local_repair_routes_to_auto_loop(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = root / "phase2_prompt_packs" / "def_1_2"
            pack_dir.mkdir(parents=True)
            triage_path = pack_dir / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "unclear_semantic_failure",
                    }
                ),
                encoding="utf-8",
            )
            (pack_dir / "diagnoser_result.json").write_text(
                json.dumps(
                    {
                        "diagnosis_verdict": "ordinary_missing_step",
                        "route_wrong": False,
                        "statement_mismatch": False,
                        "local_repair_allowed": True,
                        "recommended_next_action": "continue ordinary local proof repair",
                        "forbidden_shortcuts": [],
                        "required_local_checks": ["verify the helper lemma name locally"],
                        "rationale": "The route is accepted; one local bridge lemma is missing.",
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "def_1_2": {
                        "block_id": "def_1_2",
                        "type": "Definition",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "missing accepted-route bridge lemma",
                        "current_auto_loop_stop_reason": "diagnoser_required",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    }
                }
            )

            plan = plan_batch_from_ledger(["def_1_2"], ledger, settings)

        self.assertEqual(plan.actions[0].action, "auto_loop")
        self.assertIn("--phase2-mode auto-loop", plan.actions[0].command)
        self.assertIn("diagnoser_result local_repair_allowed=true", plan.actions[0].reason)
        self.assertIn("ordinary repair", plan.actions[0].reason)

    def test_diagnoser_result_statement_mismatch_is_not_author_queue_action(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = root / "phase2_prompt_packs" / "prob_14_7"
            pack_dir.mkdir(parents=True)
            triage_path = pack_dir / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "public_premise_statement_weakened",
                        "prompt_path": str(pack_dir / "prepared_diagnoser_prompt.txt"),
                    }
                ),
                encoding="utf-8",
            )
            (pack_dir / "diagnoser_result_v1.json").write_text(
                json.dumps(
                    {
                        "diagnosis_verdict": "statement_mismatch",
                        "route_wrong": False,
                        "statement_mismatch": True,
                        "local_repair_allowed": False,
                        "recommended_next_action": "resolve source/statement decision before author repair",
                        "forbidden_shortcuts": ["do not keep repairing the strengthened public statement"],
                        "required_local_checks": [],
                        "rationale": "The theorem proves a corrected statement with an extra public premise.",
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "prob_14_7": {
                        "block_id": "prob_14_7",
                        "type": "Problem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "extra public premise on the limit objects",
                        "current_auto_loop_stop_reason": "diagnoser_required",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    }
                }
            )

            unfiltered = plan_batch_from_ledger(["prob_14_7"], ledger, settings)
            queued = plan_batch_from_ledger(
                ["prob_14_7"],
                ledger,
                settings,
                task_kinds=["problem"],
                limit=1,
                worker_slots=1,
            )
            rendered = render_batch_runner_plan(queued)

        self.assertEqual(unfiltered.actions[0].action, "source_statement_decision_required")
        self.assertEqual(unfiltered.actions[0].command, "")
        self.assertEqual(queued.actions, ())
        self.assertIn("source_statement_decision_required=1", rendered)

    def test_semantic_fail_diagnosis_result_routes_to_source_statement_decision(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = root / "phase2_prompt_packs" / "ex_8_2_1"
            pack_dir.mkdir(parents=True)
            triage_path = pack_dir / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "statement_mismatch",
                    }
                ),
                encoding="utf-8",
            )
            result_path = pack_dir / "semantic_fail_diagnosis_result_v1.json"
            result_path.write_text(
                json.dumps(
                    {
                        "diagnosis_verdict": "source_decision_required",
                        "route_wrong": True,
                        "statement_mismatch": True,
                        "local_repair_allowed": False,
                        "source_decision_needed": True,
                        "public_api_change": True,
                        "recommended_next_action": "obtain an explicit owner decision",
                    }
                ),
                encoding="utf-8",
            )
            (pack_dir / "diagnoser_result_v2.json").write_text(
                json.dumps({"diagnosis_verdict": "incomplete_newer_result"}),
                encoding="utf-8",
            )
            (pack_dir / "diagnoser_result.json").write_text(
                json.dumps(
                    {
                        "diagnosis_verdict": "ordinary_missing_step",
                        "route_wrong": False,
                        "statement_mismatch": False,
                        "local_repair_allowed": True,
                        "recommended_next_action": "continue ordinary local proof repair",
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "ex_8_2_1": {
                        "block_id": "ex_8_2_1",
                        "type": "Exercise",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "current_auto_loop_stop_reason": "diagnoser_required",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    }
                }
            )

            plan = plan_batch_from_ledger(["ex_8_2_1"], ledger, settings)

        self.assertEqual(plan.actions[0].action, "source_statement_decision_required")
        self.assertIn(result_path.name, plan.actions[0].reason)

    def test_child_obligation_is_blocked_by_parent_source_statement_decision(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            parent_pack = root / "phase2_prompt_packs" / "thm_7_8"
            parent_pack.mkdir(parents=True)
            triage_path = parent_pack / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "statement_mismatch",
                    }
                ),
                encoding="utf-8",
            )
            (parent_pack / "diagnoser_result_v2.json").write_text(
                json.dumps(
                    {
                        "diagnosis_verdict": "source_statement_decision_required",
                        "route_wrong": False,
                        "statement_mismatch": True,
                        "local_repair_allowed": False,
                        "recommended_next_action": "resolve source/statement decision before author repair",
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "thm_7_8": {
                        "block_id": "thm_7_8",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    },
                    "obl_thm_7_8_t7_8_rs_exists": {
                        "block_id": "obl_thm_7_8_t7_8_rs_exists",
                        "type": "Phase2ObligationTask",
                        "status": NONTERMINAL,
                        "parent_task_id": "thm_7_8",
                        "target_task_id": "thm_7_8",
                        "obligation_id": "t7_8_rs_exists",
                    },
                }
            )

            plan = plan_batch_from_ledger(
                ["obl_thm_7_8_t7_8_rs_exists"],
                ledger,
                settings,
                include_legacy=True,
            )

        self.assertEqual(plan.actions[0].action, "skip_blocked")
        self.assertIn("parent source/statement decision", plan.actions[0].reason)

    def test_source_decision_resolution_ignores_historical_obligation_absorption_route(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            parent_pack = root / "phase2_prompt_packs" / "thm_7_8"
            parent_pack.mkdir(parents=True)
            triage_path = parent_pack / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "statement_mismatch",
                    }
                ),
                encoding="utf-8",
            )
            (parent_pack / "diagnoser_result_v2.json").write_text(
                json.dumps(
                    {
                        "diagnosis_verdict": "source_statement_decision_required",
                        "route_wrong": False,
                        "statement_mismatch": True,
                        "local_repair_allowed": False,
                        "recommended_next_action": "resolve source/statement decision before author repair",
                    }
                ),
                encoding="utf-8",
            )
            (parent_pack / "source_decision_resolution.json").write_text(
                json.dumps(
                    {
                        "status": "resolved",
                        "decision": "Use the strict finite-interval route: require a < b under def_1_2.",
                        "resolves_diagnoser_result": "diagnoser_result_v2.json",
                    }
                ),
                encoding="utf-8",
            )
            (parent_pack / "proof_obligations.json").write_text(
                json.dumps(
                    {
                        "schema_version": "phase2.proof_obligations.v1",
                        "task_id": "thm_7_8",
                        "obligations": [
                            {
                                "id": "t7_8_rs_exists",
                                "status": "open",
                                "ledger_task_id": "obl_thm_7_8_t7_8_rs_exists",
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )
            (root / "phase2_prompt_packs" / "obl_thm_7_8_t7_8_rs_exists").mkdir(parents=True)
            ledger = FakeLedger(
                {
                    "thm_7_8": {
                        "block_id": "thm_7_8",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    },
                    "obl_thm_7_8_t7_8_rs_exists": {
                        "block_id": "obl_thm_7_8_t7_8_rs_exists",
                        "type": "Phase2ObligationTask",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "parent_task_id": "thm_7_8",
                        "target_task_id": "thm_7_8",
                        "obligation_id": "t7_8_rs_exists",
                    },
                }
            )

            parent_plan = plan_batch_from_ledger(["thm_7_8"], ledger, settings)
            child_plan = plan_batch_from_ledger(
                ["obl_thm_7_8_t7_8_rs_exists"],
                ledger,
                settings,
                include_legacy=True,
            )

        self.assertEqual(parent_plan.actions[0].action, "auto_loop")
        self.assertIn("--phase2-mode auto-loop", parent_plan.actions[0].command)
        self.assertNotIn("absorb remaining concrete obligations", parent_plan.actions[0].reason)
        self.assertEqual(child_plan.actions[0].action, "auto_loop")

    def test_default_plan_hides_legacy_obligation_noise_when_parent_passed(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            ledger = FakeLedger(
                {
                    "prob_14_1": {
                        "block_id": "prob_14_1",
                        "type": "Problem",
                        "status": COMPLETED,
                        "phase2_status": "pass",
                        "phase2_review_verdict": "pass",
                        "phase2_proof_class": "source_route_proof_completed",
                        "phase2_completion_class": "source_route_proof_completed",
                    },
                    "obl_prob_14_1_obligation_1": {
                        "block_id": "obl_prob_14_1_obligation_1",
                        "type": "Phase2ObligationTask",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "parent_block_id": "prob_14_1",
                    },
                    "thm_7_9": {
                        "block_id": "thm_7_9",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "missing source-facing bridge",
                    },
                }
            )

            plan = plan_batch_from_ledger(
                ["prob_14_1", "obl_prob_14_1_obligation_1", "thm_7_9"],
                ledger,
                settings,
                limit=20,
            )
            rendered = render_batch_runner_plan(plan)

        self.assertEqual([action.task_id for action in plan.actions], ["thm_7_9"])
        self.assertIn("hidden legacy/audit items", rendered)
        self.assertIn("legacy_obligation=1", rendered)
        self.assertNotIn("| obl_prob_14_1_obligation_1 |", rendered)

    def test_hidden_legacy_obligation_diagnoser_is_not_current_dispatch(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            ledger = FakeLedger(
                {
                    "obl_prob_14_1_obligation_1": {
                        "block_id": "obl_prob_14_1_obligation_1",
                        "type": "Phase2ObligationTask",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "current_auto_loop_stop_reason": "diagnoser_required",
                        "parent_block_id": "prob_14_1",
                    },
                }
            )

            plan = plan_batch_from_ledger(["obl_prob_14_1_obligation_1"], ledger, settings)
            rendered = render_batch_runner_plan(plan)

        self.assertEqual(plan.actions, ())
        self.assertIn("legacy_obligation=1", rendered)
        self.assertNotIn("subagent-dispatch-required", rendered)
        self.assertNotIn("diagnoser_required=1", rendered)

    def test_legacy_mode_can_show_obligation_items_explicitly(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            ledger = FakeLedger(
                {
                    "prob_14_1": {
                        "block_id": "prob_14_1",
                        "type": "Problem",
                        "status": COMPLETED,
                        "phase2_status": "pass",
                        "phase2_review_verdict": "pass",
                    },
                    "obl_prob_14_1_obligation_1": {
                        "block_id": "obl_prob_14_1_obligation_1",
                        "type": "Phase2ObligationTask",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "parent_block_id": "prob_14_1",
                    },
                }
            )

            plan = plan_batch_from_ledger(
                ["prob_14_1", "obl_prob_14_1_obligation_1"],
                ledger,
                settings,
                include_legacy=True,
            )
            rendered = render_batch_runner_plan(plan)

        self.assertIn("obl_prob_14_1_obligation_1", [action.task_id for action in plan.actions])
        self.assertIn("| obl_prob_14_1_obligation_1 |", rendered)
        self.assertIn("hidden legacy/audit items: `0`", rendered)

    def test_restore_or_rebuild_output_is_diagnostic_when_draft_can_be_built(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = settings.phase2_prompt_packs_dir / "thm_1_1"
            pack_dir.mkdir(parents=True)
            (pack_dir / "draft.lean").write_text("-- buildable candidate\n", encoding="utf-8")
            ledger = FakeLedger(
                {
                    "thm_1_1": {
                        "block_id": "thm_1_1",
                        "type": "Theorem",
                        "status": COMPLETED,
                    },
                    "thm_1_2": {
                        "block_id": "thm_1_2",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "phase2_status_reason": "ordinary parent-facing failure",
                    },
                }
            )

            plan = plan_batch_from_ledger(["thm_1_1", "thm_1_2"], ledger, settings, limit=20)
            rendered = render_batch_runner_plan(plan)

        self.assertEqual([action.task_id for action in plan.actions], ["thm_1_2"])
        self.assertIn("diagnostic_restore_or_rebuild_output=1", rendered)
        self.assertNotIn("| thm_1_1 |", rendered)

    def test_worker_queue_hides_section_intro_restore_rows(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = root / "phase2_prompt_packs" / "thm_7_9"
            pack_dir.mkdir(parents=True)
            triage_path = pack_dir / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "private_axiom_or_open_math_debt",
                    }
                ),
                encoding="utf-8",
            )
            (pack_dir / "diagnoser_result_v2.json").write_text(
                json.dumps(
                    {
                        "diagnosis_verdict": "explicit_child_obligation_promotion",
                        "route_wrong": False,
                        "statement_mismatch": False,
                        "local_repair_allowed": False,
                        "recommended_next_action": "absorb obligations into parent/support files",
                        "forbidden_shortcuts": [],
                        "required_local_checks": [],
                        "rationale": "Former obligation material must not be re-promoted.",
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "intro_9_1": {
                        "block_id": "intro_9_1",
                        "type": "Remark",
                        "status": COMPLETED,
                    },
                    "thm_7_9": {
                        "block_id": "thm_7_9",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "current_auto_loop_stop_reason": "diagnoser_required",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    },
                }
            )

            plan = plan_batch_from_ledger(["intro_9_1", "thm_7_9"], ledger, settings, limit=2)
            rendered = render_batch_runner_plan(plan)

        self.assertEqual([action.task_id for action in plan.actions], ["thm_7_9"])
        self.assertEqual(plan.actions[0].action, "foundation_absorb_required")
        self.assertIn("section_intro_remark=1", rendered)
        self.assertNotIn("| intro_9_1 |", rendered)

    def test_include_legacy_still_hides_section_intro_remarks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            ledger = FakeLedger(
                {
                    "intro_9_1": {
                        "block_id": "intro_9_1",
                        "type": "Remark",
                        "status": COMPLETED,
                    },
                    "obl_prob_14_1_obligation_1": {
                        "block_id": "obl_prob_14_1_obligation_1",
                        "type": "Phase2ObligationTask",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "parent_block_id": "prob_14_1",
                    },
                }
            )

            plan = plan_batch_from_ledger(
                ["intro_9_1", "obl_prob_14_1_obligation_1"],
                ledger,
                settings,
                include_legacy=True,
            )
            rendered = render_batch_runner_plan(plan)

        self.assertIn("obl_prob_14_1_obligation_1", [action.task_id for action in plan.actions])
        self.assertNotIn("intro_9_1", [action.task_id for action in plan.actions])
        self.assertIn("section_intro_remark=1", rendered)
        self.assertNotIn("| intro_9_1 |", rendered)

    def test_include_legacy_still_hides_skipped_source_statement_risks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            triage_path = root / "phase2_prompt_packs" / "ex_1_3_2" / "semantic_fail_triage.json"
            triage_path.parent.mkdir(parents=True)
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "statement_or_source_mismatch",
                        "prompt_path": str(triage_path.with_name("prepared_diagnoser_prompt.txt")),
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "thm_1_2": {
                        "block_id": "thm_1_2",
                        "type": "Theorem_Statement",
                        "status": NONTERMINAL,
                        "phase2_status": "blocked",
                        "phase2_status_reason": "proof_class dependency_blocked_pending_statement_decision",
                    },
                    "ex_1_3_2": {
                        "block_id": "ex_1_3_2",
                        "type": "Example_Proof",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    },
                }
            )

            plan = plan_batch_from_ledger(
                ["thm_1_2", "ex_1_3_2"],
                ledger,
                settings,
                include_legacy=True,
            )
            rendered = render_batch_runner_plan(plan)

        self.assertEqual(plan.actions, ())
        self.assertEqual({action.task_id for action in plan.hidden_actions}, {"thm_1_2", "ex_1_3_2"})
        self.assertIn("source_statement_risk=2", rendered)
        self.assertIn("ordinary_action_queue_clear: `true`", rendered)
        self.assertIn(
            "deferred_source_statement_risk_exceptions: `2` (`ex_1_3_2`, `thm_1_2`)",
            rendered,
        )
        self.assertNotIn("subagent-dispatch-required", rendered)
        self.assertNotIn("| thm_1_2 |", rendered)
        self.assertNotIn("| ex_1_3_2 |", rendered)

    def test_batch_run_skips_diagnoser_required_and_dispatches_next_executable_action(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            triage_path = root / "phase2_prompt_packs" / "def_1_2" / "semantic_fail_triage.json"
            triage_path.parent.mkdir(parents=True)
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "private_axiom_or_open_math_debt",
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "def_1_2": {
                        "block_id": "def_1_2",
                        "type": "Definition",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    },
                    "def_1_3": {
                        "block_id": "def_1_3",
                        "type": "Definition",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                    },
                }
            )

            with patch(
                "src.toy_apollo.phase2_review_loop.run_codex_auto_loop",
                new=AsyncMock(return_value=(True, "advanced")),
            ) as auto_loop_mock:
                result = asyncio.run(run_batch_actions(["def_1_2", "def_1_3"], ledger, settings, max_actions=1))

        auto_loop_mock.assert_awaited_once()
        self.assertEqual(len(result.executed), 1)
        self.assertEqual(result.executed[0].task_id, "def_1_3")

    def test_batch_run_skips_reviewer_required_and_dispatches_next_executable_action(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            ledger, settings, waiting_pack, _ = self._setup_trivial_phase2_task(
                root,
                "prob_14_2",
                completed=True,
            )
            with patch(
                "src.toy_apollo.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = asyncio.run(write_existing_output_review_pack("prob_14_2", ledger, settings))
            self.assertTrue(success, detail)
            ledger.ledger["tasks"]["def_1_3"] = {
                "block_id": "def_1_3",
                "type": "Definition",
                "status": NONTERMINAL,
                "phase2_status": "fail",
            }
            ledger.save()

            plan = plan_batch_from_ledger(["prob_14_2", "def_1_3"], ledger, settings)
            with patch(
                "src.toy_apollo.phase2_review_loop.run_codex_auto_loop",
                new=AsyncMock(return_value=(True, "advanced")),
            ) as auto_loop_mock:
                result = asyncio.run(run_batch_actions(["prob_14_2", "def_1_3"], ledger, settings, max_actions=1))

        actions = {action.task_id: action for action in plan.actions}
        self.assertEqual(actions["prob_14_2"].action, "reviewer_required")
        self.assertIn("semantic_review_result_v1.json", actions["prob_14_2"].reason)
        auto_loop_mock.assert_awaited_once()
        self.assertEqual(len(result.executed), 1)
        self.assertEqual(result.executed[0].task_id, "def_1_3")

    def test_batch_run_does_not_execute_obligation_promotion_action(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = root / "phase2_prompt_packs" / "ex_14_4_1"
            pack_dir.mkdir(parents=True)
            triage_path = pack_dir / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "private_axiom_or_open_math_debt",
                    }
                ),
                encoding="utf-8",
            )
            (pack_dir / "diagnoser_result_v2.json").write_text(
                json.dumps(
                    {
                        "diagnosis_verdict": "explicit_child_obligation_promotion",
                        "route_wrong": False,
                        "statement_mismatch": False,
                        "local_repair_allowed": False,
                        "recommended_next_action": "promote child obligations",
                        "forbidden_shortcuts": [],
                        "required_local_checks": [],
                        "rationale": "Split the open debt into child tasks.",
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "ex_14_4_1": {
                        "block_id": "ex_14_4_1",
                        "type": "Exercise",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "current_auto_loop_stop_reason": "diagnoser_required",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    }
                }
            )

            with patch(
                "src.toy_apollo.phase2_obligation_tasks.promote_all_obligation_tasks",
                return_value={
                    "parents_scanned": ["ex_14_4_1"],
                    "created": ["obl_ex_14_4_1_bridge"],
                    "updated": [],
                    "skipped": [],
                    "created_count": 1,
                    "updated_count": 0,
                },
            ) as promote_mock:
                result = asyncio.run(run_batch_actions(["ex_14_4_1"], ledger, settings, max_actions=1))

        promote_mock.assert_not_called()
        self.assertEqual(len(result.executed), 0)
        self.assertEqual(result.details, ())
        self.assertEqual(result.plan.actions[0].action, "foundation_absorb_required")

    def test_invalid_pending_review_request_routes_to_fresh_existing_review(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = settings.phase2_prompt_packs_dir / "thm_11_6"
            pack_dir.mkdir(parents=True)
            (settings.toyapollo_output_dir / "thm_11_6.lean").write_text(
                "import Mathlib\n\ntheorem thm_11_6 : True := by trivial\n",
                encoding="utf-8",
            )
            request_path = pack_dir / "semantic_review_request_v29.json"
            result_path = pack_dir / "semantic_review_result_v29.json"
            request_path.write_text("{}", encoding="utf-8")
            ledger = FakeLedger(
                {
                    "thm_11_6": {
                        "block_id": "thm_11_6",
                        "type": "Theorem",
                        "status": COMPLETED,
                        "current_review_request_file": str(request_path),
                        "current_review_expected_result_file": str(result_path),
                    }
                }
            )

            plan = plan_batch_from_ledger(["thm_11_6"], ledger, settings)

        self.assertEqual(plan.actions[0].action, "review_existing")
        self.assertIn("--review-subject existing", plan.actions[0].command)

    def test_failed_task_with_stale_pending_request_refreshes_before_old_triage(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            task_id = "thm_3_stale_pending_after_fail"
            (settings.toyapollo_output_dir / f"{task_id}.lean").write_text(
                "import Mathlib\n\ntheorem thm_3_stale_pending_after_fail : True := by trivial\n",
                encoding="utf-8",
            )
            pack_dir = settings.phase2_prompt_packs_dir / task_id
            pack_dir.mkdir(parents=True)
            request_path = pack_dir / "semantic_review_request_v2.json"
            result_path = pack_dir / "semantic_review_result_v2.json"
            request_path.write_text("{}", encoding="utf-8")
            triage_path = pack_dir / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "mathlib_adapter",
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    task_id: {
                        "block_id": task_id,
                        "type": "Theorem",
                        "status": COMPLETED,
                        "phase2_status": "fail",
                        "current_review_request_file": str(request_path),
                        "current_review_expected_result_file": str(result_path),
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                        "latest_semantic_fail_triage_local_repair_allowed": False,
                        "latest_semantic_fail_triage_category": "mathlib_adapter",
                    }
                }
            )

            plan = plan_batch_from_ledger([task_id], ledger, settings)

        self.assertEqual(plan.actions[0].action, "review_existing")
        self.assertIn("--review-subject existing", plan.actions[0].command)
        self.assertIn("stale", plan.actions[0].reason.lower())

    def test_fresh_pending_review_request_requires_reviewer(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            task_id = "thm_11_fresh_pending_review"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(
                root,
                task_id,
                completed=True,
            )
            with patch(
                "src.toy_apollo.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = asyncio.run(write_existing_output_review_pack(task_id, ledger, settings))
            self.assertTrue(success, detail)

            plan = plan_batch_from_ledger([task_id], ledger, settings)

        self.assertEqual(plan.actions[0].action, "reviewer_required")
        self.assertEqual(plan.actions[0].command, "")
        self.assertIn("semantic_review_result_v1.json", plan.actions[0].reason)

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

    def test_ledger_final_import_union_feeds_dependency_projection(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            pack_dir = settings.phase2_prompt_packs_dir / "ex_14_4_3"
            pack_dir.mkdir(parents=True)
            (pack_dir / "metadata.json").write_text(
                json.dumps({"final_import_union": ["thm_14_8"]}),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "thm_14_8": {
                        "block_id": "thm_14_8",
                        "type": "Theorem",
                        "status": "COMPLETED_WITH_PROOF_DEBT",
                    },
                    "ex_14_4_3": {
                        "block_id": "ex_14_4_3",
                        "type": "Exercise",
                        "status": NONTERMINAL,
                        "final_import_union": ["thm_14_8"],
                    },
                }
            )

            plan = plan_batch_from_ledger(["thm_14_8", "ex_14_4_3"], ledger, settings)

        actions = {action.task_id: action for action in plan.actions}
        self.assertEqual(actions["ex_14_4_3"].action, "skip_blocked")
        self.assertIn("thm_14_8", actions["ex_14_4_3"].reason)

    def test_diagnoser_required_dependency_blocks_downstream_from_ledger_imports(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            upstream_pack = settings.phase2_prompt_packs_dir / "prob_14_8"
            downstream_pack = settings.phase2_prompt_packs_dir / "prob_14_10"
            upstream_pack.mkdir(parents=True)
            downstream_pack.mkdir(parents=True)
            triage_path = upstream_pack / "semantic_fail_triage.json"
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "private_axiom_or_open_math_debt",
                    }
                ),
                encoding="utf-8",
            )
            (downstream_pack / "metadata.json").write_text(
                json.dumps({"final_import_union": ["prob_14_8"]}),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "prob_14_8": {
                        "block_id": "prob_14_8",
                        "type": "Problem",
                        "status": NONTERMINAL,
                        "current_auto_loop_stop_reason": "diagnoser_required",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    },
                    "prob_14_10": {
                        "block_id": "prob_14_10",
                        "type": "Problem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "latest_verify_result_file": str(downstream_pack / "verify_result_v1.json"),
                        "final_import_union": ["prob_14_8"],
                    },
                }
            )

            plan = plan_batch_from_ledger(["prob_14_8", "prob_14_10"], ledger, settings)
            external_dependency_plan = plan_batch_from_ledger(["prob_14_10"], ledger, settings)

        actions = {action.task_id: action for action in plan.actions}
        self.assertEqual(actions["prob_14_8"].action, "diagnoser_required")
        self.assertEqual(actions["prob_14_10"].action, "skip_blocked")
        self.assertIn("prob_14_8", actions["prob_14_10"].reason)
        self.assertIn("diagnoser", actions["prob_14_10"].reason)
        external_actions = {action.task_id: action for action in external_dependency_plan.actions}
        self.assertEqual(external_actions["prob_14_10"].action, "skip_blocked")
        self.assertIn("prob_14_8", external_actions["prob_14_10"].reason)

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
        self.assertEqual(state["tasks"][0]["phase2_status"], "needs_fresh_review")
        self.assertEqual(ledger.ledger["tasks"]["prob_11_6"]["phase2_status"], "pass")

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

    def test_completed_missing_status_with_verify_build_failure_routes_to_auto_loop_before_review(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            (settings.toyapollo_output_dir / "thm_13_3.lean").write_text("-- stale official output\n", encoding="utf-8")
            verify_path = root / "phase2_prompt_packs" / "thm_13_3" / "verify_result_v1.json"
            verify_path.parent.mkdir(parents=True)
            verify_path.write_text(
                json.dumps(
                    {
                        "success": False,
                        "disposition": "review_existing_build_failed_no_review",
                        "primary_failure_kind": "type_mismatch",
                        "diagnostics": [
                            {
                                "kind": "type_mismatch",
                                "message": "l2Norm now requires an L2Function proof argument",
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    "thm_13_3": {
                        "block_id": "thm_13_3",
                        "type": "Theorem",
                        "status": COMPLETED,
                        "latest_verify_result_file": str(verify_path),
                    }
                }
            )

            plan = plan_batch_from_ledger(["thm_13_3"], ledger, settings)

        self.assertEqual(plan.report.rows[0].report_status, "needs_fresh_review")
        self.assertEqual(plan.actions[0].action, "auto_loop")
        self.assertIn("--phase2-mode auto-loop", plan.actions[0].command)
        self.assertIn("type_mismatch", plan.actions[0].reason)

    def test_stale_pass_with_review_existing_required_verify_disposition_routes_to_review_existing(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            task_id = "def_2_1"
            (settings.toyapollo_output_dir / f"{task_id}.lean").write_text(
                "import Mathlib\n\ndef def_2_1 : Prop := True\n",
                encoding="utf-8",
            )
            pack_dir = settings.phase2_prompt_packs_dir / task_id
            pack_dir.mkdir(parents=True)
            verify_path = pack_dir / "verify_result_v1.json"
            verify_path.write_text(
                json.dumps(
                    {
                        "success": False,
                        "disposition": "review_existing_required",
                        "primary_failure_kind": "",
                        "diagnostics": [],
                    }
                ),
                encoding="utf-8",
            )
            legacy_result_path = pack_dir / "semantic_review_result_v1.json"
            legacy_result_path.write_text(
                json.dumps(
                    {
                        "schema_version": "phase2.semantic_review.result.v1",
                        "task_id": task_id,
                        "verdict": "pass",
                        "proof_class": "textbook_definition_completed",
                        "completion_class": "textbook_definition_completed",
                    }
                ),
                encoding="utf-8",
            )
            ledger = FakeLedger(
                {
                    task_id: {
                        "block_id": task_id,
                        "type": "Definition",
                        "status": COMPLETED,
                        "phase2_status": "pass",
                        "latest_semantic_review_result_file": str(legacy_result_path),
                        "latest_verify_result_file": str(verify_path),
                    }
                }
            )

            plan = plan_batch_from_ledger([task_id], ledger, settings)

        self.assertEqual(plan.report.rows[0].report_status, "needs_fresh_review")
        self.assertEqual(plan.actions[0].action, "review_existing")
        self.assertIn("--review-subject existing", plan.actions[0].command)
        self.assertIn("review_existing_required", plan.actions[0].reason)

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

    def test_empty_worker_queue_reports_subagent_dispatch_required(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            triage_path = root / "phase2_prompt_packs" / "thm_root" / "semantic_fail_triage.json"
            triage_path.parent.mkdir(parents=True)
            triage_path.write_text(
                json.dumps(
                    {
                        "needs_diagnoser": True,
                        "local_repair_allowed": False,
                        "category": "mathlib_adapter",
                    }
                ),
                encoding="utf-8",
            )
            review_pack = settings.phase2_prompt_packs_dir / "thm_review"
            review_pack.mkdir(parents=True)
            request_path = review_pack / "semantic_review_request_v1.json"
            result_path = review_pack / "semantic_review_result_v1.json"
            request_path.write_text("{}", encoding="utf-8")
            ledger = FakeLedger(
                {
                    "thm_root": {
                        "block_id": "thm_root",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "phase2_status": "fail",
                        "latest_semantic_fail_triage_file": str(triage_path),
                        "latest_semantic_fail_triage_needs_diagnoser": True,
                    },
                    "thm_review": {
                        "block_id": "thm_review",
                        "type": "Theorem",
                        "status": NONTERMINAL,
                        "current_review_request_file": str(request_path),
                        "current_review_expected_result_file": str(result_path),
                    },
                }
            )

            plan = plan_batch_from_ledger(
                ["thm_root", "thm_review"],
                ledger,
                settings,
                task_kinds=["theorem"],
                limit=5,
                worker_slots=2,
            )
            rendered = render_batch_runner_plan(plan)

        self.assertEqual(plan.actions, ())
        self.assertIn("subagent-dispatch-required", rendered)
        self.assertNotIn("reviewer_required=1", rendered)
        self.assertIn("diagnoser_required=1", rendered)


if __name__ == "__main__":
    unittest.main()
