import json
import unittest
from pathlib import Path

from tools.validate_phase2_completion_classification import (
    DEFAULT_CLASSIFICATION,
    validate_classification,
)


class Phase2CompletionClassificationTests(unittest.TestCase):
    def test_classification_artifact_is_valid(self) -> None:
        errors = validate_classification(DEFAULT_CLASSIFICATION)
        self.assertEqual(errors, [])

    def test_beyond_book_exception_is_unique(self) -> None:
        payload = json.loads(Path(DEFAULT_CLASSIFICATION).read_text(encoding="utf-8"))
        beyond_book_tasks = [
            task["task_id"]
            for task in payload["tasks"]
            if task["primary_class"] == "beyond_book_exception"
        ]
        self.assertEqual(beyond_book_tasks, ["thm_14_8"])

    def test_open_debt_entries_have_reasons(self) -> None:
        payload = json.loads(Path(DEFAULT_CLASSIFICATION).read_text(encoding="utf-8"))
        open_debt_tasks = [
            task for task in payload["tasks"] if task["primary_class"] == "open_math_debt"
        ]
        self.assertGreater(len(open_debt_tasks), 0)
        for task in open_debt_tasks:
            self.assertIn("open", task["classification_reason"].lower())
            self.assertTrue(task["next_action"])


if __name__ == "__main__":
    unittest.main()
