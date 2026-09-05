from __future__ import annotations

import csv
import tempfile
import unittest
from pathlib import Path

from formalization_engine.core.canonical_resolver import (
    CanonicalLeanResolver,
    CanonicalResolverError,
)


class CanonicalLeanResolverTests(unittest.TestCase):
    def _root(self) -> tempfile.TemporaryDirectory[str]:
        return tempfile.TemporaryDirectory()

    @staticmethod
    def _write_manifest(root: Path) -> None:
        path = root / "ProbabilityTheory" / "chapter_01" / "thm_1_1.lean"
        path.parent.mkdir(parents=True)
        path.write_text("theorem thm_1_1 : True := by trivial\n", encoding="utf-8")
        with (root / "manifest_by_chapter.csv").open("w", encoding="utf-8", newline="") as handle:
            writer = csv.DictWriter(
                handle,
                fieldnames=["basename", "file_path", "module_name"],
            )
            writer.writeheader()
            writer.writerow(
                {
                    "basename": "thm_1_1",
                    "file_path": "ProbabilityTheory/chapter_01/thm_1_1.lean",
                    "module_name": "ProbabilityTheory.chapter_01.thm_1_1",
                }
            )

    def test_resolves_exact_path_and_module(self) -> None:
        with self._root() as raw_root:
            root = Path(raw_root)
            self._write_manifest(root)
            resolver = CanonicalLeanResolver.load(root)
            self.assertEqual(
                resolver.path_for_basename("thm_1_1"),
                root / "ProbabilityTheory" / "chapter_01" / "thm_1_1.lean",
            )
            self.assertEqual(
                resolver.module_for_basename("thm_1_1"),
                "ProbabilityTheory.chapter_01.thm_1_1",
            )

    def test_unknown_basename_fails_closed(self) -> None:
        with self._root() as raw_root:
            root = Path(raw_root)
            self._write_manifest(root)
            resolver = CanonicalLeanResolver.load(root)
            with self.assertRaises(CanonicalResolverError):
                resolver.path_for_basename("thm_9_9")


if __name__ == "__main__":
    unittest.main()
