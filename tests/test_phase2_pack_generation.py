import asyncio
import json
import os
import shutil
import sys
import unittest
from pathlib import Path
from unittest.mock import AsyncMock, patch

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.toy_apollo.phase2_pack_generation import (  # noqa: E402
    build_check_prompt_pack_candidate,
    write_codex_review_pack,
    write_existing_output_review_pack,
    write_existing_output_review_queue,
    write_prompt_pack,
)
from src.toy_apollo.phase2_prompt_pack import validate_candidate_hard_checks  # noqa: E402
from src.ledger_manager import LedgerManager, TaskStatus  # noqa: E402
from src.toy_apollo.phase2_semantic_review import (  # noqa: E402
    SEMANTIC_REVIEW_PROMPT_VERSION,
    SEMANTIC_REVIEW_RUBRIC_VERSION,
)
from tests.phase2_review_test_support import Phase2ReviewTestSupport  # noqa: E402


class Phase2PackGenerationTests(Phase2ReviewTestSupport, unittest.TestCase):
    def _setup_proof_debt_dependency_task(self, root: Path, *, legacy_completed_debt: bool = False):
        self._clean_root(root)
        plans_dir = root / "plans"
        plans_dir.mkdir(parents=True, exist_ok=True)
        dep_id = "thm_10_8"
        task_id = "prob_10_10"
        (plans_dir / "chapter10-problems_plan.json").write_text(
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
                        "type": "Problem",
                        "title": "Downstream problem",
                        "content": "Downstream task that depends on the upstream theorem.",
                        "dependencies": [dep_id],
                    },
                ],
                indent=2,
            ),
            encoding="utf-8",
        )
        ledger = LedgerManager(ledger_path=str(root / "project_ledger.json"))
        for block_id, dependencies in ((dep_id, []), (task_id, [dep_id])):
            ledger.add_or_update_task(
                {
                    "block_id": block_id,
                    "type": "Theorem" if block_id == dep_id else "Problem",
                    "title": block_id,
                    "content": "test task",
                    "source_plan": "chapter10-problems",
                    "dependencies": dependencies,
                }
            )
        if legacy_completed_debt:
            ledger.update_status(dep_id, TaskStatus.COMPLETED)
        else:
            ledger.update_status(dep_id, TaskStatus.COMPLETED_WITH_PROOF_DEBT)
        ledger.update_runtime_metadata(
            dep_id,
            proof_obligation_summary={"status_counts": {"proved": 4, "accepted_as_proof_debt": 1}},
        )
        settings = self._make_settings(root, plans_dir)
        return ledger, settings, task_id, dep_id

    def _seed_build_failures(self, pack_dir: Path, task_id: str, count: int) -> None:
        (pack_dir / "attempt_history.json").write_text(
            json.dumps(
                {
                    "task_id": task_id,
                    "attempts": [
                        {
                            "attempt": index + 1,
                            "candidate_file": str(pack_dir / f"candidate_seed_{index + 1}.lean"),
                            "candidate_hash": f"build-fail-{index + 1}",
                            "success": False,
                            "primary_failure_kind": "repl_failed",
                            "stage": "build",
                            "disposition": "build_check_temp_build_failed",
                        }
                        for index in range(count)
                    ],
                },
                indent=2,
                ensure_ascii=False,
            ),
            encoding="utf-8",
        )

    def test_write_prompt_pack_creates_intent_contract_file(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_intent_contract"
        try:
            self._clean_root(root)
            plans_dir = root / "plans"
            plans_dir.mkdir(parents=True, exist_ok=True)
            (plans_dir / "14_chap5_discrete_continuous_type_plan.json").write_text(
                """
[
  {
    "block_id": "ex_5_2_2",
    "type": "Example_Proof",
    "title": "Example 5.2.2",
    "content": "The converse of Theorem 5.2 is false. X and Y are not independent. Their joint density is 1/4(1+xy), but X^2 and Y^2 are independent.",
    "dependencies": []
  }
]
                """.strip(),
                encoding="utf-8",
            )
            from src.toy_apollo.core import LedgerManager

            ledger = LedgerManager(ledger_path=str(root / "project_ledger.json"))
            ledger.add_or_update_task(
                {
                    "block_id": "ex_5_2_2",
                    "type": "Example_Proof",
                    "title": "Example 5.2.2",
                    "content": "The converse of Theorem 5.2 is false. X and Y are not independent. Their joint density is 1/4(1+xy), but X^2 and Y^2 are independent.",
                    "source_plan": "14_chap5_discrete_continuous_type",
                    "dependencies": [],
                }
            )
            settings = self._make_settings(root, plans_dir)
            pack_dir = write_prompt_pack("ex_5_2_2", ledger, settings)
            contract = json.loads((pack_dir / "intent_contract.json").read_text(encoding="utf-8"))
            self.assertEqual(contract["task_role"], "counterexample_example")
            self.assertEqual(contract["coverage_mode"], "strict_source_alignment")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_pack_generates_handoff_artifacts_without_reviewer_config(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_codex_review_pack"
        try:
            self._clean_root(root)
            task_id = "thm_4_pack_generation_codex_review_pack"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(root, task_id)

            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            with patch.dict(os.environ, {"TOY_APOLLO_PHASE2_REVIEWER_ARGV_JSON": ""}, clear=False), patch(
                "src.toy_apollo.phase2_prompt_pack.LeanCompiler.validate_with_repl_async",
                new=AsyncMock(return_value=(True, "unexpected")),
            ) as repl_mock, patch(
                "src.toy_apollo.phase2_prompt_pack.LeanCompiler.build_module_async",
                new=AsyncMock(return_value=(True, "unexpected")),
            ) as build_mock:
                success, detail = asyncio.run(write_codex_review_pack(task_id, ledger, settings))

            self.assertTrue(success, detail)
            self.assertEqual(repl_mock.await_count, 0)
            self.assertEqual(build_mock.await_count, 0)
            self.assertTrue((pack_dir / "candidate_v1.lean").exists())
            self.assertTrue((pack_dir / "semantic_review_input_v1.json").exists())
            self.assertTrue((pack_dir / "semantic_review_prompt_v1.md").exists())
            self.assertTrue((pack_dir / "semantic_review_result_template_v1.json").exists())
            self.assertTrue((pack_dir / "semantic_review_request_v1.json").exists())
            self.assertTrue((pack_dir / "semantic_review_request.json").exists())
            self.assertTrue((pack_dir / "semantic_review_input.json").exists())
            self.assertTrue((pack_dir / "semantic_review_prompt.md").exists())
            self.assertFalse((pack_dir / "proof_obligations.json").exists())
            self.assertFalse(output_path.exists())

            review_input = json.loads((pack_dir / "semantic_review_input_v1.json").read_text(encoding="utf-8"))
            self.assertEqual(review_input["mode"], "review-pack")
            self.assertEqual(review_input["prompt_version"], SEMANTIC_REVIEW_PROMPT_VERSION)
            self.assertEqual(review_input["rubric_version"], SEMANTIC_REVIEW_RUBRIC_VERSION)
            self.assertEqual(review_input["review_basis"]["proof_obligations"], {})
            self.assertEqual(review_input["review_basis"]["proof_obligations_file"], "")
            self.assertEqual(review_input["review_basis"]["proof_obligation_summary"], {})

            review_template = json.loads((pack_dir / "semantic_review_result_template_v1.json").read_text(encoding="utf-8"))
            schema_hints = review_template["reviewer_schema_hints"]
            self.assertEqual(schema_hints["section_status_values"], ["covered", "partial", "missing", "violated", "unclear"])
            self.assertEqual(
                schema_hints["downstream_consumer_entry_shape"],
                {
                    "block_id": "<direct downstream block_id>",
                    "status": "covered | not_applicable | blocked",
                    "evidence": "<why this exported interface is adequate or not applicable>",
                },
            )
            self.assertEqual(schema_hints["forbidden_weakening_status_values"], ["not_present", "present", "not_applicable"])

            review_prompt = (pack_dir / "semantic_review_prompt_v1.md").read_text(encoding="utf-8")
            self.assertIn("Status enum fields", review_prompt)
            self.assertIn("downstream_adequacy.consumers_checked entries must be objects", review_prompt)
            self.assertIn("forbidden_weakenings entries use status not_present/present/not_applicable", review_prompt)

            review_context = (pack_dir / "semantic_review_context_v1.md").read_text(encoding="utf-8")
            self.assertIn("Proof obligation tracking: `Level 0", review_context)
            self.assertNotIn("## Proof Obligation Ledger", review_context)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_complex_pack_still_creates_proof_obligations_file(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_complex_obligations"
        try:
            self._clean_root(root)
            plans_dir = root / "plans"
            plans_dir.mkdir(parents=True, exist_ok=True)
            task_id = "thm_10_8"
            complex_content = "Proof. Construct the representation, split the cases, pass to the limit, and show convergence. " * 40
            (plans_dir / "chapter10-problems_plan.json").write_text(
                json.dumps(
                    [
                        {
                            "block_id": task_id,
                            "type": "Theorem_with_Proof",
                            "title": "Complex proof",
                            "content": complex_content,
                            "dependencies": ["def_10_4", "prob_3_5"],
                        }
                    ],
                    indent=2,
                ),
                encoding="utf-8",
            )
            ledger = LedgerManager(ledger_path=str(root / "project_ledger.json"))
            ledger.add_or_update_task(
                {
                    "block_id": task_id,
                    "type": "Theorem_with_Proof",
                    "title": "Complex proof",
                    "content": complex_content,
                    "source_plan": "chapter10-problems",
                    "dependencies": ["def_10_4", "prob_3_5"],
                }
            )
            settings = self._make_settings(root, plans_dir)

            pack_dir = write_prompt_pack(task_id, ledger, settings)

            obligations_path = pack_dir / "proof_obligations.json"
            self.assertTrue(obligations_path.exists())
            obligation_ledger = json.loads(obligations_path.read_text(encoding="utf-8"))
            self.assertEqual(obligation_ledger["task_id"], task_id)
            self.assertTrue(obligation_ledger["classification"]["requires_decomposition"])
            self.assertEqual(obligation_ledger["obligations"][0]["id"], "source_proof_spine")
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_write_prompt_pack_rejects_hard_dependency_with_proof_debt(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_proof_debt_dep"
        try:
            ledger, settings, task_id, dep_id = self._setup_proof_debt_dependency_task(root)

            with self.assertRaisesRegex(ValueError, f"{dep_id}.*proof debt"):
                write_prompt_pack(task_id, ledger, settings)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_build_check_rejects_existing_pack_when_hard_dependency_has_legacy_proof_debt(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_legacy_proof_debt_dep"
        try:
            ledger, settings, task_id, dep_id = self._setup_proof_debt_dependency_task(
                root,
                legacy_completed_debt=True,
            )
            pack_dir = settings.phase2_prompt_packs_dir / task_id
            pack_dir.mkdir(parents=True, exist_ok=True)
            (pack_dir / "draft.lean").write_text("import Mathlib\n\ntheorem prob_10_10 : True := by\n  trivial\n", encoding="utf-8")

            success, detail = asyncio.run(build_check_prompt_pack_candidate(task_id, ledger, settings))

            self.assertFalse(success)
            self.assertIn(dep_id, detail)
            self.assertIn("proof debt", detail.lower())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_codex_review_pack_reflects_pack_soft_imports(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_pack_soft_import"
        try:
            self._clean_root(root)
            task_id = "thm_4_pack_generation_pack_soft_import"
            dep_id = "thm_4_pack_generation_soft_dep"
            stale_dep_id = "thm_4_pack_generation_stale_soft_dep"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)

            for local_dep_id in [dep_id, stale_dep_id]:
                dep_code = f"import Mathlib\n\ntheorem {local_dep_id} : True := by\n  trivial\n"
                dep_path = settings.toyapollo_output_dir / f"{local_dep_id}.lean"
                dep_path.parent.mkdir(parents=True, exist_ok=True)
                dep_path.write_text(dep_code, encoding="utf-8")
                ledger.add_or_update_task(
                    {
                        "block_id": local_dep_id,
                        "type": "Theorem",
                        "title": "Soft dependency",
                        "content": "A previously completed local output.",
                        "source_plan": "08_chap4_measurable_functions",
                        "dependencies": [],
                    }
                )
                ledger.register_success(local_dep_id, dep_code, ledger._hash_text(dep_code))
            ledger.update_candidate_soft_imports(task_id, [stale_dep_id])

            task_json_path = pack_dir / "task.json"
            task_payload = json.loads(task_json_path.read_text(encoding="utf-8"))
            task_payload["soft_imports"] = [dep_id]
            task_payload["final_import_union"] = [dep_id]
            task_json_path.write_text(json.dumps(task_payload, indent=2, ensure_ascii=False), encoding="utf-8")
            (pack_dir / "draft.lean").write_text(
                f"import Mathlib\nimport ToyApollo.Output.{dep_id}\n\ntheorem {task_id} : True := by\n  exact {dep_id}\n",
                encoding="utf-8",
            )

            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)
            self.assertTrue(build_success, build_detail)
            with patch.dict(os.environ, {"TOY_APOLLO_PHASE2_REVIEWER_ARGV_JSON": ""}, clear=False):
                review_success, review_detail = asyncio.run(write_codex_review_pack(task_id, ledger, settings))

            self.assertTrue(review_success, review_detail)
            review_input = json.loads((pack_dir / "semantic_review_input_v1.json").read_text(encoding="utf-8"))
            self.assertIn(dep_id, review_input["task"]["soft_imports"])
            self.assertIn(dep_id, review_input["review_basis"]["task"]["soft_imports"])
            self.assertNotIn(stale_dep_id, review_input["task"]["soft_imports"])
            self.assertNotIn(stale_dep_id, review_input["review_basis"]["task"]["soft_imports"])
            self.assertIn(f"import ToyApollo.Output.{dep_id}", review_input["imports"])
            self.assertNotIn(f"import ToyApollo.Output.{stale_dep_id}", review_input["imports"])
            self.assertIn(dep_id, {entry["task_id"] for entry in review_input["dependencies"]})
            self.assertNotIn(stale_dep_id, {entry["task_id"] for entry in review_input["dependencies"]})
            review_context = (pack_dir / "semantic_review_context_v1.md").read_text(encoding="utf-8")
            self.assertIn(dep_id, review_context)
            self.assertNotIn(stale_dep_id, review_context)
            self.assertIn("Soft imports", review_context)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_build_check_failure_before_15_keeps_task_packed(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_build_fail_before_15"
        try:
            self._clean_root(root)
            task_id = "thm_4_pack_generation_build_fail_before_15"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)

            with patch(
                "src.toy_apollo.phase2_prompt_pack.LeanCompiler.validate_with_repl_async",
                new=AsyncMock(return_value=(False, "repl failed")),
            ), patch(
                "src.toy_apollo.phase2_prompt_pack.LeanCompiler.build_module_async",
                new=AsyncMock(return_value=(False, "temp build failed")),
            ):
                success, detail = asyncio.run(build_check_prompt_pack_candidate(task_id, ledger, settings))

            self.assertFalse(success)
            self.assertIn("repl failed", detail.lower())
            task = ledger.ledger["tasks"][task_id]
            self.assertEqual(task["status"], "PACKED")
            self.assertEqual(task["pack_candidate_state"], "build_failed")
            self.assertEqual(task["phase2_build_fail_counter"], 1)
            self.assertEqual(task["phase2_review_fail_counter"], 0)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_build_check_failure_fails_only_after_15_consecutive_build_failures(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_build_fail_after_15"
        try:
            self._clean_root(root)
            task_id = "thm_4_pack_generation_build_fail_after_15"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            self._seed_build_failures(pack_dir, task_id, 14)

            with patch(
                "src.toy_apollo.phase2_prompt_pack.LeanCompiler.validate_with_repl_async",
                new=AsyncMock(return_value=(False, "repl failed")),
            ), patch(
                "src.toy_apollo.phase2_prompt_pack.LeanCompiler.build_module_async",
                new=AsyncMock(return_value=(False, "temp build failed")),
            ):
                success, detail = asyncio.run(build_check_prompt_pack_candidate(task_id, ledger, settings))

            self.assertFalse(success)
            self.assertIn("repl failed", detail.lower())
            task = ledger.ledger["tasks"][task_id]
            self.assertEqual(task["status"], "FAILED_LOCAL")
            self.assertEqual(task["phase2_build_fail_counter"], 15)
            self.assertEqual(task["phase2_review_fail_counter"], 0)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_successful_build_check_resets_build_failure_counter(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_build_success_resets_counter"
        try:
            self._clean_root(root)
            task_id = "thm_4_pack_generation_build_success_resets_counter"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id)
            self._seed_build_failures(pack_dir, task_id, 14)

            build_success, build_detail = self._run_successful_build_check(task_id, ledger, settings)

            self.assertTrue(build_success, build_detail)
            task = ledger.ledger["tasks"][task_id]
            self.assertEqual(task["status"], "PACKED")
            self.assertEqual(task["pack_candidate_state"], "build_ready")
            self.assertEqual(task["phase2_build_fail_counter"], 0)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_hard_check_allows_auxiliary_output_module_with_task_prefix(self):
        task = {"block_id": "thm_10_8", "type": "Theorem_with_Proof", "dependencies": []}
        candidate = """
import Mathlib
import ToyApollo.Output.thm_10_8_quantile_defs

theorem thm_10_8 : True := by
  trivial
""".strip()

        success, diagnostics, detail = validate_candidate_hard_checks(task, candidate)

        self.assertTrue(success, detail)
        self.assertEqual(diagnostics, [])

    def test_hard_check_still_rejects_exact_self_import(self):
        task = {"block_id": "thm_10_8", "type": "Theorem_with_Proof", "dependencies": []}
        candidate = """
import Mathlib
import ToyApollo.Output.thm_10_8

theorem thm_10_8 : True := by
  trivial
""".strip()

        success, diagnostics, detail = validate_candidate_hard_checks(task, candidate)

        self.assertFalse(success)
        self.assertIn("self-imports", detail)
        self.assertEqual(diagnostics[0]["kind"], "self_import")

    def test_hard_check_still_rejects_undeclared_task_import(self):
        task = {"block_id": "thm_10_8", "type": "Theorem_with_Proof", "dependencies": []}
        candidate = """
import Mathlib
import ToyApollo.Output.prob_10_10

theorem thm_10_8 : True := by
  trivial
""".strip()

        success, diagnostics, detail = validate_candidate_hard_checks(task, candidate)

        self.assertFalse(success)
        self.assertIn("prob_10_10", detail)
        self.assertEqual(diagnostics[0]["kind"], "undeclared_local_import")

    def test_review_existing_success_generates_official_snapshot_and_review_artifacts(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_review_existing_success"
        try:
            self._clean_root(root)
            task_id = "thm_4_pack_generation_review_existing_success"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(root, task_id, completed=True)
            self.assertTrue(output_path.exists())

            with patch(
                "src.toy_apollo.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = asyncio.run(write_existing_output_review_pack(task_id, ledger, settings))

            self.assertTrue(success, detail)
            self.assertTrue((pack_dir / "official_snapshot_v1.lean").exists())
            self.assertTrue((pack_dir / "semantic_review_input_v1.json").exists())
            self.assertTrue((pack_dir / "semantic_review_request_v1.json").exists())
            self.assertTrue((pack_dir / "verify_result_v1.json").exists())
            task = ledger.ledger["tasks"][task_id]
            self.assertEqual(task["latest_operation_kind"], "review-existing")
            self.assertTrue(str(task["latest_verify_result_file"]).endswith("verify_result_v1.json"))
            self.assertEqual(task["pack_candidate_state"], "draft")
            self.assertTrue(str(task["current_review_request_file"]).endswith("semantic_review_request_v1.json"))
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_existing_queue_reuses_matching_attempt_with_existing_result(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_pack_generation_existing_queue_reuse"
        try:
            self._clean_root(root)
            task_id = "thm_4_pack_generation_existing_queue_reuse"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id, completed=True)

            with patch(
                "src.toy_apollo.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = asyncio.run(write_existing_output_review_pack(task_id, ledger, settings))
            self.assertTrue(success, detail)
            result_path = self._write_codex_review_result(pack_dir, verdict="pass")
            result_payload = json.loads(result_path.read_text(encoding="utf-8"))
            result_payload["review_input_file"] = str(pack_dir / "semantic_review_input_v1.json")
            result_path.write_text(json.dumps(result_payload, indent=2, ensure_ascii=False), encoding="utf-8")

            with patch(
                "src.toy_apollo.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = asyncio.run(write_existing_output_review_queue([], ledger, settings))

            self.assertTrue(success, detail)
            report_path = next((settings.phase2_prompt_packs_dir / "_reports").glob("review_existing_queue_*.json"))
            report = json.loads(report_path.read_text(encoding="utf-8"))
            task_report = report["tasks"][0]
            self.assertEqual(task_report["queue_status"], "review_result_present")
            self.assertEqual(task_report["next_action"], "inspect_existing_result")
            self.assertTrue(str(task_report["latest_matching_review_result_file"]).endswith("semantic_review_result_v1.json"))
            self.assertFalse((pack_dir / "semantic_review_input_v2.json").exists())
            task_record = ledger.ledger["tasks"][task_id]
            self.assertTrue(str(task_record["current_review_input_file"]).endswith("semantic_review_input_v1.json"))
            self.assertEqual(task_record["current_review_origin"], "review-existing-queue")
        finally:
            shutil.rmtree(root, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
