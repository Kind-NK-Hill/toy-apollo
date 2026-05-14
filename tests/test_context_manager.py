import shutil
import sys
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.context_manager import ContextManager  # noqa: E402


class ContextManagerTests(unittest.TestCase):
    def test_legacy_current_task_id_uses_canonical_dependency_index(self):
        root = REPO_ROOT / "tests" / "_tmp_context_manager"
        shutil.rmtree(root, ignore_errors=True)
        try:
            root.mkdir(parents=True)
            (root / "def_4_3_sup_inf.lean").write_text(
                "theorem dep : True := by trivial\n",
                encoding="utf-8",
            )

            manager = ContextManager(output_dir=str(root))
            context = manager.get_context_for(
                {"block_id": "def_inverse_image", "dependencies": ["def_sup_inf"], "title": "Current"},
                [
                    {"block_id": "def_sup_inf", "dependencies": [], "title": "Sup Inf"},
                    {"block_id": "def_inverse_image", "dependencies": ["def_sup_inf"], "title": "Current"},
                ],
            )

            self.assertIn("-- Context from: Sup Inf", context)
            self.assertIn("theorem dep", context)
        finally:
            shutil.rmtree(root, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()
