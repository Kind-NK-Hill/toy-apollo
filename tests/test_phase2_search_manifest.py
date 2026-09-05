import subprocess
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formalization_engine.phase2_prompt_pack import _search_top_level_decls  # noqa: E402


class Phase2SearchManifestTests(unittest.TestCase):
    def test_top_level_decl_search_uses_rg_before_python_tree_scan(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_search_manifest"
        source = root / "Foo.lean"
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text("theorem Cauchy : True := by trivial\n", encoding="utf-8")
        try:
            with patch(
                "formalization_engine.phase2_prompt_pack.subprocess.run",
                return_value=subprocess.CompletedProcess(
                    args=[],
                    returncode=0,
                    stdout=f"{source}:1:theorem Cauchy : True := by trivial\n",
                    stderr="",
                ),
            ), patch(
                "formalization_engine.phase2_prompt_pack._iter_lean_files",
                side_effect=AssertionError("full Python scan should be fallback-only"),
            ):
                hits = _search_top_level_decls(root, "Cauchy", max_results=3, file_cache={})

            self.assertEqual(len(hits), 1)
            self.assertEqual(hits[0]["path"], str(source))
            self.assertEqual(hits[0]["line_no"], 1)
            self.assertIn("theorem Cauchy", hits[0]["line"])
        finally:
            source.unlink(missing_ok=True)
            root.rmdir()

    def test_top_level_decl_search_returns_empty_rg_miss_without_python_tree_scan(self):
        root = REPO_ROOT / "tests" / "_tmp_phase2_search_manifest_miss"
        root.mkdir(parents=True, exist_ok=True)
        try:
            with patch(
                "formalization_engine.phase2_prompt_pack.subprocess.run",
                return_value=subprocess.CompletedProcess(args=[], returncode=1, stdout="", stderr=""),
            ), patch(
                "formalization_engine.phase2_prompt_pack._iter_lean_files",
                side_effect=AssertionError("rg miss should not trigger full Python scan"),
            ):
                hits = _search_top_level_decls(root, "Chebyshev", max_results=3, file_cache={})

            self.assertEqual(hits, [])
        finally:
            root.rmdir()


if __name__ == "__main__":
    unittest.main()
