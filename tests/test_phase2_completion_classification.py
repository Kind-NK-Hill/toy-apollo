import json
import tempfile
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

    def test_classification_evidence_freshness_is_explicit_diagnostic(self) -> None:
        payload = json.loads(Path(DEFAULT_CLASSIFICATION).read_text(encoding="utf-8"))
        payload["tasks"][0]["evidence"][0]["text"] = "definitely-not-at-this-line"
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "classification.json"
            path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
            default_errors = validate_classification(path)
            freshness_errors = validate_classification(path, require_fresh_evidence=True)

        self.assertEqual(default_errors, [])
        self.assertTrue(any("definitely-not-at-this-line" in error for error in freshness_errors))

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

    def test_textbook_completed_requires_proof_contract_or_level0_reason(self) -> None:
        payload = json.loads(Path(DEFAULT_CLASSIFICATION).read_text(encoding="utf-8"))
        for item in payload["tasks"]:
            if item["primary_class"] == "textbook_proof_completed":
                item["validation"] = ["python tools/validate_phase2_obligation_contracts.py --task " + item["task_id"]]
        task = next(item for item in payload["tasks"] if item["primary_class"] == "textbook_proof_completed")
        task["validation"] = []
        task["evidence"] = [item for item in task["evidence"] if item.get("kind") != "proof_contract"]
        task["classification_reason"] = "textbook proof complete without explicit contract evidence"
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "classification.json"
            path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
            errors = validate_classification(path, require_textbook_contract=True)

        self.assertTrue(any("requires proof_contract evidence" in error for error in errors))

        task["classification_reason"] = "no task-local proof obligations are in scope because Level 0 direct proof"
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "classification.json"
            path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
            errors = validate_classification(path, require_textbook_contract=True)

        self.assertFalse(any("requires proof_contract evidence" in error for error in errors))

    def test_adapter_evidence_does_not_satisfy_textbook_contract(self) -> None:
        payload = json.loads(Path(DEFAULT_CLASSIFICATION).read_text(encoding="utf-8"))
        for item in payload["tasks"]:
            if item["primary_class"] == "textbook_proof_completed":
                item["validation"] = ["python tools/validate_phase2_obligation_contracts.py --task " + item["task_id"]]
        task = next(item for item in payload["tasks"] if item["primary_class"] == "textbook_proof_completed")
        task["validation"] = []
        task["evidence"] = [item for item in task["evidence"] if item.get("kind") != "proof_contract"]
        task["classification_reason"] = "textbook proof complete without explicit contract evidence"
        task["evidence"][0]["kind"] = "mathlib_adapter"
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "classification.json"
            path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
            errors = validate_classification(path, require_textbook_contract=True)

        self.assertTrue(any("requires proof_contract evidence" in error for error in errors))


if __name__ == "__main__":
    unittest.main()
