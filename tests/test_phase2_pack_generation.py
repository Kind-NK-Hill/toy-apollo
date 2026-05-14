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
    write_codex_review_pack,
    write_existing_output_review_pack,
    write_existing_output_review_queue,
    write_prompt_pack,
)
from src.toy_apollo.phase2_semantic_review import (  # noqa: E402
    SEMANTIC_REVIEW_PROMPT_VERSION,
    SEMANTIC_REVIEW_RUBRIC_VERSION,
)
from tests.phase2_review_test_support import Phase2ReviewTestSupport  # noqa: E402


class Phase2PackGenerationTests(Phase2ReviewTestSupport, unittest.TestCase):
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
            self.assertFalse(output_path.exists())

            review_input = json.loads((pack_dir / "semantic_review_input_v1.json").read_text(encoding="utf-8"))
            self.assertEqual(review_input["mode"], "review-pack")
            self.assertEqual(review_input["prompt_version"], SEMANTIC_REVIEW_PROMPT_VERSION)
            self.assertEqual(review_input["rubric_version"], SEMANTIC_REVIEW_RUBRIC_VERSION)
        finally:
            shutil.rmtree(root, ignore_errors=True)

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
