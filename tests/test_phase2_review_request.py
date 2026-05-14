import asyncio
import shutil
import sys
import unittest
from pathlib import Path
from unittest.mock import AsyncMock, patch

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.toy_apollo.phase2_review_loop import run_codex_review_now  # noqa: E402
from src.toy_apollo.phase2_prompt_pack import write_existing_output_review_pack  # noqa: E402
from tests.phase2_review_test_support import Phase2ReviewTestSupport  # noqa: E402


class Phase2ReviewRequestTests(Phase2ReviewTestSupport, unittest.TestCase):
    def test_review_now_current_rejects_stale_basis_request(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_now_stale_basis"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_now_stale_basis"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(root, task_id, completed=True)
            self.assertTrue(output_path.exists())

            with patch(
                "src.toy_apollo.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = asyncio.run(write_existing_output_review_pack(task_id, ledger, settings))
            self.assertTrue(success, detail)
            self._append_direct_downstream_consumer(settings.plans_dir, task_id, "thm_4_review_now_stale_basis_consumer")

            success, detail = asyncio.run(run_codex_review_now(task_id, ledger, settings, review_subject="current"))

            self.assertFalse(success)
            self.assertIn("basis", detail.lower())
            self.assertFalse((pack_dir / "semantic_review_request_v2.json").exists())
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_now_existing_ignores_broken_draft_when_official_output_is_valid(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_now_existing_ignores_broken_draft"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_now_existing_ignores_broken_draft"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(root, task_id, completed=True)
            self.assertTrue(output_path.exists())
            draft_path = pack_dir / "draft.lean"
            draft_path.write_text("import Missing.Module\n#check impossible_name\n", encoding="utf-8")

            with patch(
                "src.toy_apollo.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = asyncio.run(run_codex_review_now(task_id, ledger, settings, review_subject="existing"))

            self.assertTrue(success, detail)
            self.assertIn("request is ready", detail.lower())
            task_record = ledger.ledger["tasks"][task_id]
            self.assertEqual(task_record["current_review_subject_kind"], "official_output")
            self.assertTrue(str(task_record["current_review_request_file"]).endswith("semantic_review_request_v1.json"))
            request_payload = (pack_dir / "semantic_review_request.json").read_text(encoding="utf-8")
            self.assertIn('"review_subject_kind": "official_output"', request_payload)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_now_current_reprepares_existing_subject_after_result_exists(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_now_reprepare_existing"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_now_reprepare_existing"
            ledger, settings, pack_dir, output_path = self._setup_trivial_phase2_task(root, task_id, completed=True)
            self.assertTrue(output_path.exists())

            with patch(
                "src.toy_apollo.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = asyncio.run(write_existing_output_review_pack(task_id, ledger, settings))
            self.assertTrue(success, detail)
            first_request = pack_dir / "semantic_review_request_v1.json"
            self.assertTrue(first_request.exists())
            self._write_codex_review_result(pack_dir, verdict="pass")

            with patch(
                "src.toy_apollo.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = asyncio.run(run_codex_review_now(task_id, ledger, settings, review_subject="current"))

            self.assertTrue(success, detail)
            self.assertTrue((pack_dir / "semantic_review_request_v2.json").exists())
            current_request = (pack_dir / "semantic_review_request.json").read_text(encoding="utf-8")
            self.assertIn('"review_subject_kind": "official_output"', current_request)
        finally:
            shutil.rmtree(root, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
