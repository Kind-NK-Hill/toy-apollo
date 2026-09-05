from copy import deepcopy
import unittest

from formalization_engine.phase2_pack_shared.io import sha256_json
from formalization_engine.review_basis_diagnostics import (
    compare_review_bases,
    frozen_target_pilot_fingerprints,
    review_basis_fingerprints,
)
from tools.review_basis_pilot import run_identity_pilot


class ReviewBasisDiagnosticsTests(unittest.TestCase):
    def test_diagnostics_preserve_original_basis_and_hash(self):
        basis = {"task": {"content": "source"}, "ledger_status": {"status": "pass"},
                 "dependency_status": [{"task_id": "d", "official_output_hash": "h", "ledger_status": "pass"}]}
        original = deepcopy(basis)
        original_hash = sha256_json(basis)
        report = review_basis_fingerprints(basis)
        self.assertEqual(basis, original)
        self.assertEqual(report["authority_basis_hash"], original_hash)
        self.assertEqual(sum(report["field_counts"].values()), 5)
        self.assertFalse(report["target_context_is_frozen_goal"])

    def test_ledger_only_change_does_not_look_like_target_change(self):
        before = {"task": {"content": "source", "soft_imports_confirmed_at": "t1"},
                  "dependency_status": [{"task_id": "d", "official_output_hash": "h", "ledger_status": "pass"}]}
        after = deepcopy(before)
        after["dependency_status"][0]["ledger_status"] = "review_requested"
        after["task"]["soft_imports_confirmed_at"] = "t2"
        report = compare_review_bases(before, after)
        self.assertEqual(report["changed_dimensions"], ["runtime_mirrors"])
        self.assertTrue(report["exact_basis_changed"])
        self.assertEqual(len(report["changes"]), 2)

    def test_dependency_bytes_are_bundle_identity_not_claimed_definition_identity(self):
        before = {"dependency_status": [{"official_output_hash": "original"}]}
        after = {"dependency_status": [{"official_output_hash": "changed"}]}
        self.assertEqual(compare_review_bases(before, after)["changed_dimensions"], ["dependency_bundle"])

    def test_unknown_fields_empty_containers_and_type_changes_remain_visible(self):
        before = {"new/~field": {}, "extra": True}
        after = {"new/~field": [], "extra": 1, "new_field": None}
        report = compare_review_bases(before, after)
        self.assertEqual(report["changed_dimensions"], ["unclassified"])
        self.assertEqual(len(report["changes"]), 3)
        self.assertIn("/new~1~0field", [row["path"] for row in report["changes"]])

    def test_key_order_does_not_invalidate_fingerprints(self):
        report = compare_review_bases({"task": {"a": 1, "b": 2}}, {"task": {"b": 2, "a": 1}})
        self.assertEqual(report["changed_dimensions"], [])
        self.assertFalse(report["exact_basis_changed"])

    def test_array_and_numeric_object_keys_cannot_alias(self):
        report = compare_review_bases({"unknown": {"0": 1}}, {"unknown": [1]})
        self.assertEqual(report["changed_dimensions"], ["unclassified"])
        self.assertEqual(report["changes"][0]["path"], "/unknown/0")

    def test_explicit_target_manifest_probes_only_expected_identities(self):
        report = run_identity_pilot()
        self.assertTrue(report["all_checks_passed"])
        self.assertEqual(len(report["scenarios"]), 7)
        self.assertEqual(report["authority_effect"], "none")

    def test_target_manifest_requires_explicit_dependency_closure_and_environment(self):
        snapshot = run_identity_pilot()["baseline"]
        del snapshot["target"]["definition_dependencies"]
        with self.assertRaisesRegex(ValueError, "definition_dependencies"):
            frozen_target_pilot_fingerprints(snapshot)


if __name__ == "__main__":
    unittest.main()
