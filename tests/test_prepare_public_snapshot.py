from __future__ import annotations

import unittest

from tools.prepare_public_snapshot import (
    PUBLIC_SOURCE_NOTICE,
    sanitize_source_comments,
    sanitize_task_header,
)


class PreparePublicSnapshotTest(unittest.TestCase):
    def test_sanitizes_source_excerpt_and_preserves_metadata_and_code(self) -> None:
        original = """import Mathlib

/-
TASK ID: def_8_5
TYPE: Definition
SOURCE PLAN: chapter8
TASK CONTENT:
private source text
-/

def answer : Nat := 42
"""

        result = sanitize_task_header(original)

        self.assertTrue(result.changed)
        self.assertNotIn("private source text", result.text)
        self.assertIn("TASK ID: def_8_5", result.text)
        self.assertIn("TYPE: Definition", result.text)
        self.assertIn("SOURCE PLAN: chapter8", result.text)
        self.assertIn(PUBLIC_SOURCE_NOTICE, result.text)
        self.assertIn("def answer : Nat := 42", result.text)

    def test_leaves_non_task_support_module_unchanged(self) -> None:
        original = "import Mathlib\n\ndef helper : Nat := 1\n"

        result = sanitize_task_header(original)

        self.assertFalse(result.changed)
        self.assertEqual(result.text, original)

    def test_rejects_unclosed_task_header(self) -> None:
        with self.assertRaisesRegex(ValueError, "closed Lean comment"):
            sanitize_task_header("/-\nTASK CONTENT:\nprivate source")

    def test_sanitizes_multiple_absorbed_task_headers(self) -> None:
        original = """/-
TASK ID: first
TASK CONTENT:
first private source
-/
def first : Nat := 1
/-
TASK ID: second
TASK CONTENT:
second private source
-/
def second : Nat := 2
"""

        result = sanitize_task_header(original)

        self.assertTrue(result.changed)
        self.assertNotIn("TASK CONTENT", result.text)
        self.assertNotIn("private source", result.text)
        self.assertEqual(result.text.count(PUBLIC_SOURCE_NOTICE), 2)

    def test_sanitizes_legacy_source_comment(self) -> None:
        original = """import Mathlib
/-
\\begin{thmbox}{2.1}
private theorem and proof text
\\end{thmbox}
-/
theorem public_code : True := by trivial
"""

        result = sanitize_source_comments(original)

        self.assertTrue(result.changed)
        self.assertNotIn("private theorem", result.text)
        self.assertIn(PUBLIC_SOURCE_NOTICE, result.text)
        self.assertIn("theorem public_code", result.text)


if __name__ == "__main__":
    unittest.main()
