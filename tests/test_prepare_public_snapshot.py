from __future__ import annotations

import unittest

from tools.prepare_public_snapshot import (
    PUBLIC_SOURCE_NOTICE,
    block_comments,
    sanitize_source_comments,
    sanitize_task_parent,
    sanitize_task_header,
    task_parent_is_public,
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

    def test_task_parent_sanitizer_removes_unclassified_and_nested_block_comments(self) -> None:
        original = '''import Mathlib

/-!
TASK ID: thm_1_1
Unmarked source prose that the legacy marker list missed.
/- nested source note -/
-/

/-- A second textbook statement. -/
def marker : String := "/- this is string data, not a comment -/"
theorem public_code : True := by trivial
'''

        result = sanitize_task_parent(original, task_id="thm_1_1")

        self.assertTrue(result.changed)
        self.assertNotIn("Unmarked source prose", result.text)
        self.assertNotIn("textbook statement", result.text)
        self.assertIn('"/- this is string data, not a comment -/"', result.text)
        self.assertTrue(result.text.startswith("/-\n"))
        self.assertEqual(len(block_comments(result.text)), 1)
        self.assertNotIn("\n\n\n", result.text)
        self.assertTrue(task_parent_is_public(result.text))

    def test_task_parent_policy_fails_closed(self) -> None:
        missing_notice = "import Mathlib\n\ntheorem answer : True := by trivial\n"
        extra_comment = f"""/-!
TASK ID: thm_1_1
{PUBLIC_SOURCE_NOTICE}
-/
/-- Extra prose. -/
theorem answer : True := by trivial
"""

        self.assertFalse(task_parent_is_public(missing_notice))
        self.assertFalse(task_parent_is_public(extra_comment))


if __name__ == "__main__":
    unittest.main()
