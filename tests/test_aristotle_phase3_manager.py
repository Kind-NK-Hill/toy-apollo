import asyncio
import shutil
import sys
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.aristotle_phase3 import AristotlePhase3Manager  # noqa: E402
from src.toy_apollo.core.settings import Settings  # noqa: E402


def make_settings(root: Path) -> Settings:
    return Settings(
        runtime_root=root,
        artifact_root=root,
        plans_dir=root / "plans",
        reports_dir=root / "reports",
        formalized_chapters_dir=root / "formalized_chapters",
        output_lean_files_dir=root / "output_lean_files",
        phase2_prompt_packs_dir=root / "phase2_prompt_packs",
        phase3_softdep_packs_dir=root / "phase3_softdep_packs",
        phase3_execution_batches_dir=root / "phase3_execution_batches",
        phase3_post_harvest_packs_dir=root / "phase3_post_harvest_packs",
        error_logs_dir=root / "error_logs",
        toyapollo_output_dir=root / "ToyApollo" / "Output",
        aristotle_outbox_dir=root / "aristotle_outbox",
        aristotle_archives_dir=root / "aristotle_archives",
        mathlib_index_file=root / "mathlib_index.faiss",
        mathlib_corpus_file=root / "mathlib_corpus.json",
        project_ledger_file=root / "project_ledger.json",
        lab_notebook_file=root / "lab_notebook.json",
        mathlib_path=root / ".lake" / "packages" / "mathlib" / "Mathlib",
    )


class AristotlePhase3ManagerTests(unittest.TestCase):
    def test_harvest_offload_uses_supplied_project_id(self):
        root = REPO_ROOT / "tests" / "_tmp_aristotle_phase3_manager"
        try:
            if root.exists():
                shutil.rmtree(root, ignore_errors=True)
            manager = object.__new__(AristotlePhase3Manager)
            manager.settings = make_settings(root)

            called = {}

            def fake_run(cmd, capture_output, text):
                called["cmd"] = cmd
                self.assertTrue(capture_output)
                self.assertTrue(text)
                return SimpleNamespace(returncode=1, stdout="", stderr="boom")

            with patch("src.aristotle_phase3.subprocess.run", side_effect=fake_run):
                result = asyncio.run(manager.harvest_offload("prob_1_1", "cloud-123"))

            self.assertEqual(called["cmd"][2], "cloud-123")
            self.assertEqual(result["cloud_project_id"], "cloud-123")
            self.assertIn("aristotle_result_cli_failed", result["error"])
        finally:
            shutil.rmtree(root, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
