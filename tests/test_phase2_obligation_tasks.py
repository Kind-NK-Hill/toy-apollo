import json
import shutil
import sys
import unittest
from pathlib import Path
from unittest.mock import AsyncMock, patch

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.ledger_manager import LedgerManager, TaskStatus  # noqa: E402
from src.toy_apollo.phase2_obligation_tasks import (  # noqa: E402
    OBLIGATION_TASK_TYPE,
    promote_all_obligation_tasks,
    promote_obligation_tasks_for_task,
    reconcile_obligation_tasks_for_task,
)
from src.toy_apollo.phase2_output_binding import resolve_phase2_output_binding  # noqa: E402
from src.toy_apollo.phase2_prompt_pack import resolve_phase2_task  # noqa: E402
from src.toy_apollo.phase2_prompt_pack import build_check_prompt_pack_candidate  # noqa: E402
from src.toy_apollo.phase2_prompt_pack import write_codex_review_pack  # noqa: E402
from src.toy_apollo.phase2_prompt_pack import write_prompt_pack  # noqa: E402
from src.toy_apollo.phase2_review_apply import apply_codex_review_result  # noqa: E402
from tests.phase2_review_test_support import Phase2ReviewTestSupport  # noqa: E402


class Phase2ObligationTaskTests(Phase2ReviewTestSupport, unittest.TestCase):
    def _setup_parent_with_debt(self, root: Path):
        self._clean_root(root)
        plans_dir = root / "plans"
        plans_dir.mkdir(parents=True, exist_ok=True)
        (plans_dir / "chapter10-continuous-mapping_plan.json").write_text(
            json.dumps(
                [
                    {
                        "block_id": "def_10_7",
                        "type": "Definition",
                        "title": "Upstream support",
                        "content": "Existing upstream support.",
                        "dependencies": [],
                    },
                    {
                        "block_id": "thm_10_8",
                        "type": "Theorem",
                        "title": "Skorokhod representation",
                        "content": "Prove the theorem using the textbook quantile construction.",
                        "dependencies": ["def_10_7"],
                    },
                ],
                indent=2,
            ),
            encoding="utf-8",
        )
        settings = self._make_settings(root, plans_dir)
        ledger = LedgerManager(ledger_path=str(root / "project_ledger.json"))
        ledger.add_or_update_task(
            {
                "block_id": "def_10_7",
                "type": "Definition",
                "title": "Upstream support",
                "content": "Existing upstream support.",
                "source_plan": "chapter10-continuous-mapping",
                "dependencies": [],
            }
        )
        ledger.add_or_update_task(
            {
                "block_id": "thm_10_8",
                "type": "Theorem",
                "title": "Skorokhod representation",
                "content": "Prove the theorem using the textbook quantile construction.",
                "source_plan": "chapter10-continuous-mapping",
                "dependencies": ["def_10_7"],
            }
        )
        ledger.update_status("def_10_7", TaskStatus.COMPLETED)
        ledger.update_status("thm_10_8", TaskStatus.COMPLETED_WITH_PROOF_DEBT)

        pack_dir = settings.phase2_prompt_packs_dir / "thm_10_8"
        pack_dir.mkdir(parents=True, exist_ok=True)
        (pack_dir / "proof_obligations.json").write_text(
            json.dumps(
                {
                    "schema_version": "phase2.proof_obligations.v1",
                    "task_id": "thm_10_8",
                    "generated_at": "2026-05-19T00:00:00Z",
                    "classification": {"requires_decomposition": True},
                    "obligations": [
                        {
                            "id": "already_done",
                            "title": "Already done",
                            "kind": "source_step",
                            "source_ref": "textbook prior line",
                            "depends_on": [],
                            "lean_landing": "already_done",
                            "status": "proved",
                            "review_status": "accepted",
                            "blocking": True,
                            "scaffold_hypotheses": [],
                            "notes": "",
                        },
                        {
                            "id": "quantile_event_measurability",
                            "title": "Quantile event measurability",
                            "kind": "proof_debt_support",
                            "source_ref": "Chapter 10 proof of Theorem 10.8, quantile construction step",
                            "depends_on": ["already_done"],
                            "lean_landing": "SkorokhodQuantileSupport.Yn_measurable, SkorokhodQuantileSupport.Y_measurable",
                            "status": "accepted_as_proof_debt",
                            "review_status": "accepted",
                            "blocking": True,
                            "scaffold_hypotheses": [
                                {
                                    "name": "Yn_measurable",
                                    "category": "proof_debt_support",
                                    "obligation_id": "quantile_event_measurability",
                                    "discharge_plan": "replace support field with local theorem evidence",
                                    "status": "accepted_as_proof_debt",
                                }
                            ],
                            "notes": "Needs the textbook event calculation rather than a support-field assumption.",
                            "source_output_alignment": {
                                "audit_class": "C_support_field_gap_no_decl",
                                "family": "cdf/weak/law",
                                "missing_landing_names": ["SkorokhodQuantileSupport.Yn_measurable"],
                                "next_action": "Replace support predicate with theorem-level evidence.",
                            },
                        },
                    ],
                    "scaffold_hypotheses": [],
                    "review_history": [],
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        return ledger, settings, pack_dir

    def test_promotes_accepted_debt_obligation_to_ledger_child_task(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_obligation_promote"
        try:
            ledger, settings, pack_dir = self._setup_parent_with_debt(root)

            report = promote_obligation_tasks_for_task("thm_10_8", ledger, settings)

            self.assertEqual(len(report.created), 1)
            child_id = report.created[0]
            child = ledger.ledger["tasks"][child_id]
            self.assertEqual(child["type"], OBLIGATION_TASK_TYPE)
            self.assertEqual(child["parent_task_id"], "thm_10_8")
            self.assertEqual(child["parent_block_id"], "thm_10_8")
            self.assertEqual(child["obligation_id"], "quantile_event_measurability")
            self.assertEqual(child["target_task_id"], "thm_10_8")
            self.assertTrue(child["target_file"].endswith("ToyApollo/Output/thm_10_8.lean"))
            self.assertEqual(child["source_plan"], "chapter10-continuous-mapping")
            self.assertEqual(child["dependencies"], ["def_10_7"])
            self.assertEqual(child["phase2_build_fail_counter"], 0)
            self.assertEqual(child["phase2_review_fail_counter"], 0)
            self.assertIn("Chapter 10 proof of Theorem 10.8", child["content"])
            self.assertIn("SkorokhodQuantileSupport.Yn_measurable", child["content"])
            self.assertIn("C_support_field_gap_no_decl", child["content"])

            resolved = resolve_phase2_task(child_id, ledger, settings)
            self.assertEqual(resolved["block_id"], child_id)
            self.assertEqual(resolved["type"], OBLIGATION_TASK_TYPE)
            self.assertIn("quantile_event_measurability", resolved["content"])

            updated = json.loads((pack_dir / "proof_obligations.json").read_text(encoding="utf-8"))
            by_id = {item["id"]: item for item in updated["obligations"]}
            self.assertEqual(by_id["quantile_event_measurability"]["ledger_task_id"], child_id)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_promoted_child_inherits_parent_candidate_soft_imports(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_obligation_soft_imports"
        try:
            ledger, settings, _pack_dir = self._setup_parent_with_debt(root)
            ledger.update_candidate_soft_imports("thm_10_8", ["thm_10_9"])
            ledger.mark_soft_imports_confirmed("thm_10_8", ["thm_10_9"])

            report = promote_obligation_tasks_for_task("thm_10_8", ledger, settings)

            child_id = report.created[0]
            child = ledger.ledger["tasks"][child_id]
            self.assertEqual(child["candidate_snapshot"]["soft_imports"], ["thm_10_9"])
            resolved = resolve_phase2_task(child_id, ledger, settings)
            self.assertEqual(resolved["soft_imports"], ["thm_10_9"])
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_promoted_child_merges_plan_and_runtime_soft_imports(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_obligation_soft_import_merge"
        try:
            ledger, settings, _pack_dir = self._setup_parent_with_debt(root)
            plan_path = settings.plans_dir / "chapter10-continuous-mapping_plan.json"
            plan = json.loads(plan_path.read_text(encoding="utf-8"))
            for task in plan:
                if task["block_id"] == "thm_10_8":
                    task["soft_imports"] = ["def_10_7"]
            plan_path.write_text(json.dumps(plan, indent=2), encoding="utf-8")
            ledger.update_candidate_soft_imports("thm_10_8", ["def_10_7", "thm_10_9"])
            ledger.mark_soft_imports_confirmed("thm_10_8", ["def_10_7", "thm_10_9"])

            report = promote_obligation_tasks_for_task("thm_10_8", ledger, settings)

            child_id = report.created[0]
            child = ledger.ledger["tasks"][child_id]
            self.assertEqual(child["candidate_snapshot"]["soft_imports"], ["def_10_7", "thm_10_9"])
            resolved = resolve_phase2_task(child_id, ledger, settings)
            self.assertIn("def_10_7", resolved["dependencies"])
            self.assertEqual(resolved["soft_imports"], ["thm_10_9"])

            child_pack_dir = settings.phase2_prompt_packs_dir / child_id
            child_pack_dir.mkdir(parents=True, exist_ok=True)
            stale_pack_task = dict(child)
            stale_pack_task["soft_imports"] = ["def_10_7"]
            stale_pack_task["final_import_union"] = ["def_10_7"]
            (child_pack_dir / "task.json").write_text(
                json.dumps(stale_pack_task, indent=2, ensure_ascii=False),
                encoding="utf-8",
            )

            resolved_with_stale_pack = resolve_phase2_task(child_id, ledger, settings)
            self.assertIn("def_10_7", resolved_with_stale_pack["dependencies"])
            self.assertEqual(resolved_with_stale_pack["soft_imports"], ["thm_10_9"])
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_promote_all_scans_existing_pack_dirs(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_obligation_promote_all"
        try:
            ledger, settings, _pack_dir = self._setup_parent_with_debt(root)

            report = promote_all_obligation_tasks(ledger, settings)

            self.assertEqual(report["parents_scanned"], ["thm_10_8"])
            self.assertEqual(len(report["created"]), 1)
            child_id = report["created"][0]
            self.assertEqual(ledger.ledger["tasks"][child_id]["type"], OBLIGATION_TASK_TYPE)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_promotion_is_idempotent_and_preserves_attempt_counters(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_obligation_idempotent"
        try:
            ledger, settings, _pack_dir = self._setup_parent_with_debt(root)
            first = promote_obligation_tasks_for_task("thm_10_8", ledger, settings)
            child_id = first.created[0]
            ledger.update_runtime_metadata(
                child_id,
                phase2_build_fail_counter=14,
                phase2_review_fail_counter=2,
            )
            ledger.update_status(child_id, TaskStatus.PACKED)

            second = promote_obligation_tasks_for_task("thm_10_8", ledger, settings)

            self.assertEqual(second.created, [])
            self.assertEqual(second.updated, [child_id])
            child = ledger.ledger["tasks"][child_id]
            self.assertEqual(child["status"], TaskStatus.PACKED.value)
            self.assertEqual(child["phase2_build_fail_counter"], 14)
            self.assertEqual(child["phase2_review_fail_counter"], 2)
            obligation_children = [
                task_id
                for task_id, task in ledger.ledger["tasks"].items()
                if task.get("type") == OBLIGATION_TASK_TYPE
                and task.get("parent_task_id") == "thm_10_8"
                and task.get("obligation_id") == "quantile_event_measurability"
            ]
            self.assertEqual(obligation_children, [child_id])
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_completed_child_task_reconciles_parent_obligation_and_keeps_child(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_obligation_reconcile"
        try:
            ledger, settings, pack_dir = self._setup_parent_with_debt(root)
            report = promote_obligation_tasks_for_task("thm_10_8", ledger, settings)
            child_id = report.created[0]
            ledger.update_status(child_id, TaskStatus.COMPLETED)

            reconciliation = reconcile_obligation_tasks_for_task("thm_10_8", ledger, settings)

            self.assertEqual(reconciliation["proved"], [child_id])
            self.assertIn(child_id, ledger.ledger["tasks"])
            self.assertEqual(ledger.ledger["tasks"][child_id]["status"], TaskStatus.COMPLETED.value)
            self.assertEqual(ledger.ledger["tasks"][child_id]["obligation_task_state"], "closed")
            child_summary = ledger.ledger["tasks"][child_id]["proof_obligation_summary"]
            self.assertEqual(child_summary["status_counts"].get("proved"), 1)
            self.assertEqual(child_summary["open_blocking_ids"], [])
            self.assertFalse(child_summary["needs_concrete_decomposition"])
            self.assertEqual(ledger.ledger["tasks"]["thm_10_8"]["status"], TaskStatus.COMPLETED.value)
            summary = ledger.ledger["tasks"]["thm_10_8"]["proof_obligation_summary"]
            self.assertEqual(summary["status_counts"].get("accepted_as_proof_debt", 0), 0)
            self.assertEqual(summary["status_counts"].get("proved", 0), 2)

            updated = json.loads((pack_dir / "proof_obligations.json").read_text(encoding="utf-8"))
            by_id = {item["id"]: item for item in updated["obligations"]}
            obligation = by_id["quantile_event_measurability"]
            self.assertEqual(obligation["status"], "proved")
            self.assertEqual(obligation["review_status"], "accepted")
            self.assertEqual(obligation["discharged_by_task"], child_id)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_child_pack_keeps_child_pack_dir_but_targets_parent_output_owner(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_obligation_output_binding"
        try:
            ledger, settings, _pack_dir = self._setup_parent_with_debt(root)
            parent_output = settings.toyapollo_output_dir / "thm_10_8.lean"
            parent_output.parent.mkdir(parents=True, exist_ok=True)
            parent_output.write_text(
                "import Mathlib\n\n"
                "-- WRITE FINAL LEAN CODE BELOW\n\n"
                "def thm_10_8_support : True := True.intro\n\n"
                "theorem thm_10_8 : True := by\n  trivial\n",
                encoding="utf-8",
            )
            report = promote_obligation_tasks_for_task("thm_10_8", ledger, settings)
            child_id = report.created[0]
            child_task = resolve_phase2_task(child_id, ledger, settings)

            binding = resolve_phase2_output_binding(child_task, ledger, settings)
            child_pack_dir = write_prompt_pack(child_id, ledger, settings, task=child_task)

            self.assertEqual(child_pack_dir, settings.phase2_prompt_packs_dir / child_id)
            self.assertEqual(binding.pack_task_id, child_id)
            self.assertEqual(binding.output_owner_task_id, "thm_10_8")
            self.assertEqual(binding.output_module, "ToyApollo.Output.thm_10_8")
            self.assertEqual(binding.proof_obligations_file, settings.phase2_prompt_packs_dir / "thm_10_8" / "proof_obligations.json")
            self.assertEqual(binding.focus_obligation_ids, ["quantile_event_measurability"])

            metadata = json.loads((child_pack_dir / "metadata.json").read_text(encoding="utf-8"))
            self.assertEqual(metadata["task_id"], child_id)
            self.assertEqual(metadata["output_owner_task_id"], "thm_10_8")
            self.assertEqual(metadata["output_module"], "ToyApollo.Output.thm_10_8")
            self.assertTrue(metadata["official_output_targets"][0].endswith("ToyApollo/Output/thm_10_8.lean"))

            target_stub = (child_pack_dir / "target_stub.lean").read_text(encoding="utf-8")
            draft = (child_pack_dir / "draft.lean").read_text(encoding="utf-8")
            self.assertIn("def thm_10_8_support", target_stub)
            self.assertIn("theorem thm_10_8", target_stub)
            self.assertNotIn(f"theorem {child_id}", target_stub)
            self.assertIn("def thm_10_8_support", draft)
            self.assertIn("theorem thm_10_8", draft)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_child_build_check_stages_parent_output_owner_but_counts_child_attempt(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_obligation_build_binding"
        try:
            ledger, settings, _pack_dir = self._setup_parent_with_debt(root)
            report = promote_obligation_tasks_for_task("thm_10_8", ledger, settings)
            child_id = report.created[0]
            child_task = resolve_phase2_task(child_id, ledger, settings)
            child_pack_dir = write_prompt_pack(child_id, ledger, settings, task=child_task)
            (child_pack_dir / "draft.lean").write_text(
                "import Mathlib\n\ntheorem thm_10_8 : True := by\n  trivial\n",
                encoding="utf-8",
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
            ) as staged:
                success, detail = __import__("asyncio").run(
                    build_check_prompt_pack_candidate(child_id, ledger, settings)
                )

            self.assertTrue(success, detail)
            staged.assert_called_once()
            self.assertEqual(staged.call_args.args[0], child_id)
            self.assertEqual(staged.call_args.kwargs["output_owner_task_id"], "thm_10_8")
            child = ledger.ledger["tasks"][child_id]
            self.assertEqual(child["status"], TaskStatus.PACKED.value)
            self.assertEqual(child["phase2_build_fail_counter"], 0)
            self.assertEqual(child["latest_build_ready_candidate_kind"], "draft")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_child_build_check_allows_repl_timeout_when_temp_and_final_build_pass(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_obligation_repl_timeout"
        try:
            ledger, settings, _pack_dir = self._setup_parent_with_debt(root)
            report = promote_obligation_tasks_for_task("thm_10_8", ledger, settings)
            child_id = report.created[0]
            child_task = resolve_phase2_task(child_id, ledger, settings)
            child_pack_dir = write_prompt_pack(child_id, ledger, settings, task=child_task)
            (child_pack_dir / "draft.lean").write_text(
                "import Mathlib\n\ntheorem thm_10_8 : True := by\n  trivial\n",
                encoding="utf-8",
            )

            with patch(
                "src.toy_apollo.phase2_prompt_pack.LeanCompiler.validate_with_repl_async",
                new=AsyncMock(return_value=(False, "REPL System Error: timed out after 300 seconds")),
            ), patch(
                "src.toy_apollo.phase2_prompt_pack.LeanCompiler.build_module_async",
                new=AsyncMock(return_value=(True, "temp build ok")),
            ), patch(
                "src.toy_apollo.phase2_prompt_pack._run_staged_official_build",
                return_value=(True, "final build ok"),
            ) as staged:
                success, detail = __import__("asyncio").run(
                    build_check_prompt_pack_candidate(child_id, ledger, settings)
                )

            self.assertTrue(success, detail)
            staged.assert_called_once()
            child = ledger.ledger["tasks"][child_id]
            self.assertEqual(child["phase2_build_fail_counter"], 0)
            build_result = json.loads(Path(child["latest_build_result_file"]).read_text(encoding="utf-8"))
            self.assertTrue(build_result["success"])
            self.assertIn("treated as non-blocking", build_result["repl"]["output"])
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_child_review_pack_uses_parent_obligation_ledger_with_focus_id(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_obligation_review_binding"
        try:
            ledger, settings, _pack_dir = self._setup_parent_with_debt(root)
            report = promote_obligation_tasks_for_task("thm_10_8", ledger, settings)
            child_id = report.created[0]
            child_task = resolve_phase2_task(child_id, ledger, settings)
            child_pack_dir = write_prompt_pack(child_id, ledger, settings, task=child_task)
            (child_pack_dir / "draft.lean").write_text(
                "import Mathlib\n\ntheorem thm_10_8 : True := by\n  trivial\n",
                encoding="utf-8",
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
                build_success, build_detail = __import__("asyncio").run(
                    build_check_prompt_pack_candidate(child_id, ledger, settings)
                )
            self.assertTrue(build_success, build_detail)

            success, detail = __import__("asyncio").run(write_codex_review_pack(child_id, ledger, settings))

            self.assertTrue(success, detail)
            review_input = json.loads((child_pack_dir / "semantic_review_input_v1.json").read_text(encoding="utf-8"))
            basis = review_input["review_basis"]
            self.assertEqual(basis["task"]["block_id"], child_id)
            self.assertEqual(basis["output_owner_task_id"], "thm_10_8")
            self.assertEqual(basis["output_module"], "ToyApollo.Output.thm_10_8")
            self.assertEqual(basis["focus_obligation_ids"], ["quantile_event_measurability"])
            self.assertTrue(basis["proof_obligations_file"].endswith("phase2_prompt_packs/thm_10_8/proof_obligations.json"))
            self.assertEqual(basis["proof_obligations"]["task_id"], "thm_10_8")

            review_context = (child_pack_dir / "semantic_review_context_v1.md").read_text(encoding="utf-8")
            self.assertIn("Output owner task: `thm_10_8`", review_context)
            self.assertIn("Focused obligation ids: `quantile_event_measurability`", review_context)
            self.assertIn("quantile_event_measurability", review_context)
            self.assertNotIn("source_proof_spine", review_context)
            self.assertIn("ToyApollo\\Output\\thm_10_8.lean", review_context)
            self.assertNotIn(f"ToyApollo\\Output\\{child_id}.lean", review_context)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_child_review_apply_updates_parent_obligation_and_closes_child_task(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_obligation_review_apply"
        try:
            ledger, settings, pack_dir = self._setup_parent_with_debt(root)
            report = promote_obligation_tasks_for_task("thm_10_8", ledger, settings)
            child_id = report.created[0]
            child_task = resolve_phase2_task(child_id, ledger, settings)
            child_pack_dir = write_prompt_pack(child_id, ledger, settings, task=child_task)
            (child_pack_dir / "draft.lean").write_text(
                "import Mathlib\n\ntheorem thm_10_8 : True := by\n  trivial\n",
                encoding="utf-8",
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
                build_success, build_detail = __import__("asyncio").run(
                    build_check_prompt_pack_candidate(child_id, ledger, settings)
                )
            self.assertTrue(build_success, build_detail)
            review_success, review_detail = __import__("asyncio").run(write_codex_review_pack(child_id, ledger, settings))
            self.assertTrue(review_success, review_detail)
            result_path = self._write_codex_review_result(
                child_pack_dir,
                verdict="pass",
                obligation_review={
                    "status": "covered",
                    "summary": "focused obligation covered",
                    "items": [
                        {
                            "obligation_id": "quantile_event_measurability",
                            "status": "covered",
                            "evidence": "local theorem-level event measurability evidence",
                        }
                    ],
                    "open_blockers": [],
                    "scaffold_assessment": [],
                },
            )

            with patch(
                "src.toy_apollo.phase2_review_apply.run_staged_official_build",
                return_value=(True, "final build ok"),
            ) as staged:
                success, detail = __import__("asyncio").run(
                    apply_codex_review_result(child_id, ledger, settings, str(result_path))
                )

            self.assertTrue(success, detail)
            staged.assert_called_once()
            self.assertEqual(staged.call_args.args[0], child_id)
            self.assertEqual(staged.call_args.kwargs["output_owner_task_id"], "thm_10_8")
            self.assertEqual(ledger.ledger["tasks"][child_id]["status"], TaskStatus.COMPLETED.value)
            self.assertEqual(ledger.ledger["tasks"][child_id]["obligation_task_state"], "closed")
            self.assertEqual(ledger.ledger["tasks"]["thm_10_8"]["status"], TaskStatus.COMPLETED.value)

            updated = json.loads((pack_dir / "proof_obligations.json").read_text(encoding="utf-8"))
            by_id = {item["id"]: item for item in updated["obligations"]}
            self.assertEqual(by_id["quantile_event_measurability"]["status"], "proved")
            self.assertEqual(by_id["quantile_event_measurability"]["discharged_by_task"], child_id)
        finally:
            shutil.rmtree(root, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
