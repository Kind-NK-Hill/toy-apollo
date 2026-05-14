import asyncio
import shutil
import sys
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.aristotle_offloader import AristotleDirectOffloader  # noqa: E402


class AristotleOffloaderTests(unittest.TestCase):
    def test_problem_requires_operator_confirmed_soft_imports(self):
        root = REPO_ROOT / "tests" / "_tmp_aristotle_missing_soft_imports"
        try:
            shutil.rmtree(root, ignore_errors=True)
            offloader = AristotleDirectOffloader()
            offloader.outbox_root = root / "aristotle_outbox"
            candidate = {
                "block_id": "prob_4_11",
                "type": "Problem",
                "title": "prob_4_11",
                "content": "Prove the stated chapter problem.",
                "source_plan": "test",
                "dependencies": [],
                "soft_imports": [],
                "soft_imports_confirmed_at": "",
                "depth": 0,
                "status": "PACKED",
            }

            with self.assertRaisesRegex(RuntimeError, "missing_soft_imports_selection"):
                asyncio.run(offloader.prepare_package(candidate))
        finally:
            shutil.rmtree(root, ignore_errors=True)

    def test_confirmed_empty_soft_imports_are_accepted_without_selection_fallback(self):
        root = REPO_ROOT / "tests" / "_tmp_aristotle_confirmed_empty_soft_imports"
        try:
            shutil.rmtree(root, ignore_errors=True)
            offloader = AristotleDirectOffloader()
            offloader.outbox_root = root / "aristotle_outbox"
            candidate = {
                "block_id": "prob_4_11",
                "type": "Problem",
                "title": "prob_4_11",
                "content": "Prove the stated chapter problem.",
                "source_plan": "test",
                "dependencies": [],
                "soft_imports": [],
                "soft_imports_confirmed_at": "2026-05-11T00:00:00Z",
                "depth": 0,
                "status": "PACKED",
            }

            asyncio.run(offloader.prepare_package(candidate))

            target_file = root / "aristotle_outbox" / "prob_4_11" / "ToyApollo" / "Output" / "prob_4_11.lean"
            self.assertTrue(target_file.exists())
            self.assertIn("theorem prob_4_11 : sorry := by sorry", target_file.read_text(encoding="utf-8"))
        finally:
            shutil.rmtree(root, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
