import json
import tempfile
import unittest
from pathlib import Path

from tools.validate_phase2_completion_classification import (
    ALLOWED_FLAGS,
    ALLOWED_PRIMARY_CLASSES,
    DEFAULT_CLASSIFICATION,
    validate_classification,
)


class Phase2CompletionClassificationTests(unittest.TestCase):
    def _private_payload(self) -> dict:
        if not Path(DEFAULT_CLASSIFICATION).is_file():
            self.skipTest("requires private Phase 2 classification fixture")
        return json.loads(Path(DEFAULT_CLASSIFICATION).read_text(encoding="utf-8"))

    @staticmethod
    def _fixture_payload(root: Path) -> dict:
        evidence_path = root / "fixture.lean"
        evidence_path.write_text("theorem fixture : True := by trivial\n", encoding="utf-8")
        tasks = []
        for task_id, chapter, classification in (
            ("thm_1_1", 1, "textbook_proof_completed"),
            ("thm_14_8", 14, "beyond_book_exception"),
        ):
            tasks.append({
                "task_id": task_id,
                "chapter": chapter,
                "lean_file": str(evidence_path),
                "declarations": ["fixture"],
                "primary_class": classification,
                "flags": [],
                "evidence": [{
                    "file": str(evidence_path), "line": 1,
                    "kind": "theorem", "text": "theorem fixture",
                }],
                "validation": [],
                "classification_reason": "isolated validator fixture",
                "next_action": "inspect the fixture",
            })
        return {
            "schema_version": 1,
            "created": "fixture",
            "scope": "isolated validator test; not a corpus completion report",
            "allowed_primary_classes": sorted(ALLOWED_PRIMARY_CLASSES),
            "allowed_flags": sorted(ALLOWED_FLAGS),
            "tasks": tasks,
        }

    def test_classification_artifact_is_valid(self) -> None:
        self._private_payload()
        errors = validate_classification(DEFAULT_CLASSIFICATION)
        self.assertEqual(errors, [])

    def test_classification_evidence_freshness_is_explicit_diagnostic(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            payload = self._fixture_payload(Path(tmp))
            path = Path(tmp) / "classification.json"
            path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
            self.assertEqual(validate_classification(path, require_fresh_evidence=True), [])
            payload["tasks"][0]["evidence"][0]["text"] = "definitely-not-at-this-line"
            path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
            default_errors = validate_classification(path)
            freshness_errors = validate_classification(path, require_fresh_evidence=True)

        self.assertEqual(default_errors, [])
        self.assertTrue(any("definitely-not-at-this-line" in error for error in freshness_errors))

    def test_beyond_book_exception_is_unique(self) -> None:
        payload = self._private_payload()
        beyond_book_tasks = [
            task["task_id"]
            for task in payload["tasks"]
            if task["primary_class"] == "beyond_book_exception"
        ]
        self.assertEqual(beyond_book_tasks, ["thm_14_8"])

    def test_open_debt_entries_have_reasons(self) -> None:
        payload = self._private_payload()
        open_debt_tasks = [
            task for task in payload["tasks"] if task["primary_class"] == "open_math_debt"
        ]
        self.assertGreater(len(open_debt_tasks), 0)
        for task in open_debt_tasks:
            self.assertIn("open", task["classification_reason"].lower())
            self.assertTrue(task["next_action"])

    def test_textbook_completed_requires_proof_contract_or_level0_reason(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            payload = self._fixture_payload(Path(tmp))
            task = payload["tasks"][0]
            path = Path(tmp) / "classification.json"
            path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
            self.assertEqual(validate_classification(path), [])
            errors = validate_classification(path, require_textbook_contract=True)
            self.assertTrue(any("requires proof_contract evidence" in error for error in errors))
            task["classification_reason"] = "no task-local proof obligations are in scope because Level 0 direct proof"
            path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
            errors = validate_classification(path, require_textbook_contract=True)

        self.assertEqual(errors, [])

    def test_adapter_evidence_does_not_satisfy_textbook_contract(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            payload = self._fixture_payload(Path(tmp))
            task = payload["tasks"][0]
            task["evidence"][0]["kind"] = "mathlib_adapter"
            path = Path(tmp) / "classification.json"
            path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
            self.assertEqual(validate_classification(path), [])
            errors = validate_classification(path, require_textbook_contract=True)

        self.assertTrue(any("requires proof_contract evidence" in error for error in errors))


if __name__ == "__main__":
    unittest.main()
