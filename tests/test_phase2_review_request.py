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

from src.toy_apollo.phase2_review_loop import run_codex_review_now  # noqa: E402
from src.toy_apollo.phase2_pack_shared.artifacts import select_latest_existing_task_file  # noqa: E402
from src.toy_apollo.phase2_pack_shared.io import sha256_text  # noqa: E402
from src.toy_apollo.phase2_pack_generation import resolve_phase2_task  # noqa: E402
from src.toy_apollo.phase2_prompt_pack import write_existing_output_review_pack  # noqa: E402
from src.toy_apollo.phase2_review_request import (  # noqa: E402
    _validate_review_input_freshness,
    build_semantic_review_basis,
)
from tests.phase2_review_test_support import Phase2ReviewTestSupport  # noqa: E402


class Phase2ReviewRequestTests(Phase2ReviewTestSupport, unittest.TestCase):
    def test_existing_output_selection_prefers_canonical_target_over_newer_shadow(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_canonical_output_selection"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_canonical_output_selection"
            _, settings, _, canonical_output = self._setup_trivial_phase2_task(root, task_id, completed=True)
            shadow_output = settings.output_lean_files_dir / "general" / f"{task_id}.lean"
            shadow_output.parent.mkdir(parents=True, exist_ok=True)
            shadow_output.write_text("import Mathlib\n\ntheorem stale_shadow : False := by sorry\n", encoding="utf-8")

            selected = select_latest_existing_task_file(task_id, "08_chap4_measurable_functions", settings)

            self.assertEqual(selected, canonical_output)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_existing_output_selection_does_not_fall_back_when_canonical_is_missing(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_canonical_output_required"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_canonical_output_required"
            _, settings, _, canonical_output = self._setup_trivial_phase2_task(root, task_id, completed=False)
            self.assertFalse(canonical_output.exists())
            shadow_output = settings.output_lean_files_dir / "general" / f"{task_id}.lean"
            shadow_output.parent.mkdir(parents=True, exist_ok=True)
            shadow_output.write_text("import Mathlib\n\ntheorem legacy_shadow : True := by trivial\n", encoding="utf-8")

            selected = select_latest_existing_task_file(task_id, "08_chap4_measurable_functions", settings)

            self.assertIsNone(selected)
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_review_basis_hashes_real_source_tex_separately_from_task_content(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_real_source_tex_basis"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_real_source_tex_basis"
            ledger, settings, _, output_path = self._setup_trivial_phase2_task(root, task_id, completed=True)
            source_tex = root / "inputs" / "08_chap4_measurable_functions.tex"
            source_tex.parent.mkdir(parents=True, exist_ok=True)
            tex_content = "\\begin{theorem}A source theorem changed independently.\\end{theorem}\n"
            source_tex.write_text(tex_content, encoding="utf-8")
            task = resolve_phase2_task(task_id, ledger, settings)

            basis = build_semantic_review_basis(
                task,
                ledger,
                settings,
                review_subject_kind="official_output",
                review_subject_hash=sha256_text(output_path.read_text(encoding="utf-8")),
                review_subject_file=output_path,
            )

            self.assertEqual(Path(basis["source_evidence"]["tex_file"]), source_tex)
            self.assertTrue(basis["source_evidence"]["tex_exists"])
            self.assertEqual(basis["source_evidence"]["tex_hash"], sha256_text(tex_content))
            self.assertEqual(basis["source_evidence"]["task_content_hash"], sha256_text(task["content"]))
            self.assertNotEqual(basis["source_evidence"]["tex_hash"], basis["source_evidence"]["task_content_hash"])
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_source_tex_change_invalidates_existing_review_request(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_review_source_tex_freshness"
        try:
            self._clean_root(root)
            task_id = "thm_4_review_source_tex_freshness"
            ledger, settings, pack_dir, _ = self._setup_trivial_phase2_task(root, task_id, completed=True)
            source_tex = root / "inputs" / "08_chap4_measurable_functions.tex"
            source_tex.parent.mkdir(parents=True, exist_ok=True)
            source_tex.write_text("original source theorem\n", encoding="utf-8")
            with patch(
                "src.toy_apollo.phase2_prompt_pack._run_official_module_build",
                return_value=(True, "build ok"),
            ):
                success, detail = asyncio.run(write_existing_output_review_pack(task_id, ledger, settings))
            self.assertTrue(success, detail)
            review_input = json.loads((pack_dir / "semantic_review_input_v1.json").read_text(encoding="utf-8"))
            source_tex.write_text("materially changed source theorem\n", encoding="utf-8")

            error, _ = _validate_review_input_freshness(
                task=resolve_phase2_task(task_id, ledger, settings),
                ledger=ledger,
                settings=settings,
                pack_dir=pack_dir,
                review_input=review_input,
            )

            self.assertIn("basis changed", error)
        finally:
            shutil.rmtree(root, ignore_errors=True)

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
