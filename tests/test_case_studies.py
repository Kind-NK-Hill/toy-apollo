from __future__ import annotations

import json
import shutil
import tempfile
import unittest
from pathlib import Path

from tools.check_case_studies import validate_case_studies, validate_timeline


class CaseStudyTests(unittest.TestCase):
    def test_public_case_collection_is_consistent(self) -> None:
        root = Path(__file__).resolve().parents[1] / "examples" / "case-studies"
        self.assertEqual(validate_case_studies(root), [])

    def test_timeline_counts_fail_closed(self) -> None:
        payload = {
            "schema_version": 1,
            "case_id": "fixture",
            "failure_modes": ["domain_drift"],
            "statement_drift": True,
            "curation": {
                "snapshot_kind": "sanitized_interface_slice",
                "full_pack_tracked_publicly": False,
            },
            "counts": {
                "semantic_review_results": 2,
                "review_failures": 0,
                "review_passes": 2,
            },
            "private_evidence_sha256": {"attempt.json": "a" * 64},
            "reviews": [
                {
                    "round": 1,
                    "verdict": "fail",
                    "candidate_hash": "b" * 64,
                    "private_review_sha256": "c" * 64,
                    "finding": "fixture finding",
                }
            ],
        }

        errors = validate_timeline(payload, case_id="fixture")

        self.assertTrue(any("semantic_review_results" in error for error in errors))
        self.assertTrue(any("review_failures" in error for error in errors))
        self.assertTrue(any("review_passes" in error for error in errors))

    def test_catalog_cannot_lower_the_public_diversity_policy(self) -> None:
        source = Path(__file__).resolve().parents[1] / "examples" / "case-studies"
        with tempfile.TemporaryDirectory() as temporary:
            copied = Path(temporary) / "case-studies"
            shutil.copytree(source, copied)
            catalog_path = copied / "cases.json"
            catalog = json.loads(catalog_path.read_text(encoding="utf-8"))
            catalog["selection_policy"]["minimum_cases"] = 1
            catalog_path.write_text(json.dumps(catalog), encoding="utf-8")

            errors = validate_case_studies(copied)

        self.assertTrue(any("minimum_cases must be 7" in error for error in errors))


if __name__ == "__main__":
    unittest.main()
