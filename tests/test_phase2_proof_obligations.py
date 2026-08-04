import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.toy_apollo.phase2_proof_obligations import (  # noqa: E402
    default_proof_obligations,
    needs_concrete_decomposition,
    normalize_proof_obligations,
    render_proof_obligations_markdown,
    should_track_proof_obligations,
    summarize_proof_obligations,
    validate_obligation_review_for_pass,
)


class Phase2ProofObligationsTests(unittest.TestCase):
    def test_level0_does_not_create_new_obligation_tracking_even_for_complex_task(self):
        task = {
            "block_id": "thm_10_8",
            "type": "Theorem_with_Proof",
            "content": "Proof. Construct the representation, split cases, pass to limits, and show convergence. " * 40,
            "dependencies": ["def_10_4", "prob_3_5"],
        }
        with tempfile.TemporaryDirectory() as tmp:
            pack_dir = Path(tmp)
            self.assertFalse(should_track_proof_obligations(pack_dir, task, tracking_level=0))

    def test_level2_tracks_only_complex_or_existing_obligation_ledgers(self):
        normal_task = {
            "block_id": "prob_11_4",
            "type": "Problem",
            "content": "Show a direct calculation.",
            "dependencies": [],
        }
        complex_task = {
            "block_id": "thm_10_8",
            "type": "Theorem_with_Proof",
            "content": "Proof. Construct the representation, split cases, pass to limits, and show convergence. " * 40,
            "dependencies": ["def_10_4", "prob_3_5"],
        }
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            normal_pack = root / "normal"
            complex_pack = root / "complex"
            legacy_pack = root / "legacy"
            normal_pack.mkdir()
            complex_pack.mkdir()
            legacy_pack.mkdir()
            (legacy_pack / "proof_obligations.json").write_text("{}", encoding="utf-8")

            self.assertFalse(should_track_proof_obligations(normal_pack, normal_task, tracking_level=2))
            self.assertTrue(should_track_proof_obligations(complex_pack, complex_task, tracking_level=2))
            self.assertTrue(should_track_proof_obligations(legacy_pack, normal_task, tracking_level=0))

    def test_placeholder_spine_requires_concrete_decomposition(self):
        task = {
            "block_id": "thm_10_8",
            "type": "Theorem_with_Proof",
            "content": "Proof. Construct the objects, take limits, and show convergence. " * 40,
            "dependencies": ["def_10_4", "prob_3_5"],
        }

        payload = default_proof_obligations(task)
        summary = summarize_proof_obligations(payload)

        self.assertTrue(summary["requires_decomposition"])
        self.assertTrue(summary["needs_concrete_decomposition"])
        self.assertTrue(needs_concrete_decomposition(payload))
        self.assertEqual(summary["placeholder_obligation_ids"], ["source_proof_spine"])

    def test_new_translation_and_proof_debt_support_labels_are_preserved(self):
        task = {
            "block_id": "thm_10_8",
            "type": "Theorem_with_Proof",
            "content": "Proof. Construct a quantile representation and pass to the limit.",
        }
        payload = normalize_proof_obligations(
            {
                "task_id": "thm_10_8",
                "classification": {"requires_decomposition": True},
                "obligations": [
                    {
                        "id": "cdf_interface",
                        "kind": "translation",
                        "status": "open",
                        "scaffold_hypotheses": [
                            {
                                "name": "cdf_notation",
                                "category": "interface_translation",
                                "obligation_id": "cdf_interface",
                            }
                        ],
                    },
                    {
                        "id": "quantile_support",
                        "kind": "proof_debt_support",
                        "status": "blocked",
                        "scaffold_hypotheses": [
                            {
                                "name": "skorokhod_quantile_support",
                                "category": "proof_debt_support",
                                "obligation_id": "quantile_support",
                            }
                        ],
                    },
                ],
                "scaffold_hypotheses": [
                    {"name": "global_cdf_translation", "category": "interface_translation"},
                    {"name": "global_quantile_support", "category": "proof_debt_support"},
                ],
            },
            task,
        )

        self.assertEqual([item["kind"] for item in payload["obligations"]], ["translation", "proof_debt_support"])
        self.assertEqual(
            [item["category"] for item in payload["scaffold_hypotheses"]],
            ["interface_translation", "proof_debt_support"],
        )
        self.assertEqual(
            [item["scaffold_hypotheses"][0]["category"] for item in payload["obligations"]],
            ["interface_translation", "proof_debt_support"],
        )

    def test_non_debt_scaffold_categories_are_preserved(self):
        task = {
            "block_id": "thm_9_5",
            "type": "Theorem_with_Proof",
            "content": "Proof. Assemble already proved support constructors into the final theorem.",
        }
        payload = normalize_proof_obligations(
            {
                "task_id": "thm_9_5",
                "classification": {"requires_decomposition": True},
                "obligations": [
                    {
                        "id": "assemble_internal_support",
                        "kind": "assembly",
                        "status": "open",
                        "scaffold_hypotheses": [
                            {"name": "local_spine", "category": "assembly_scaffold"},
                            {"name": "proved_fields", "category": "support_package"},
                            {"name": "mk_support", "category": "support_constructor"},
                        ],
                    }
                ],
            },
            task,
        )

        categories = [
            item["category"]
            for item in payload["obligations"][0]["scaffold_hypotheses"]
        ]
        self.assertEqual(categories, ["assembly_scaffold", "support_package", "support_constructor"])

    def test_accepted_proof_debt_support_is_auditable_and_nonblocking(self):
        task = {
            "block_id": "thm_10_8",
            "type": "Theorem_with_Proof",
            "content": "Proof. Construct a generalized inverse quantile representation.",
        }
        payload = normalize_proof_obligations(
            {
                "task_id": "thm_10_8",
                "classification": {"requires_decomposition": True},
                "obligations": [
                    {
                        "id": "quantile_support",
                        "kind": "proof_debt_support",
                        "status": "accepted_as_proof_debt",
                        "review_status": "accepted",
                        "lean_landing": "h_skorokhod_support",
                        "blocking": True,
                        "source_output_alignment": {
                            "audit_class": "C_support_field_gap_no_decl",
                            "family": "quantile/skorokhod",
                            "existing_local_declarations": [],
                            "missing_landing_names": ["h_skorokhod_support"],
                            "next_action": "Replace the support field with theorem-level evidence.",
                        },
                    }
                ],
            },
            task,
        )

        summary = summarize_proof_obligations(payload)

        self.assertEqual(summary["open_blocking_ids"], [])
        self.assertEqual(summary["source_output_alignment_counts"], {"C_support_field_gap_no_decl": 1})
        self.assertFalse(summary["needs_concrete_decomposition"])
        rendered = render_proof_obligations_markdown(payload)
        self.assertIn("Source-output alignment", rendered)
        self.assertIn("h_skorokhod_support", rendered)

    def test_normalize_obligation_preserves_contract_fields(self):
        task = {
            "block_id": "thm_10_8",
            "type": "Theorem_with_Proof",
            "content": "Proof. Construct a quantile representation and pass to the limit.",
        }
        payload = normalize_proof_obligations(
            {
                "task_id": "thm_10_8",
                "classification": {"requires_decomposition": True},
                "obligations": [
                    {
                        "id": "quantile_support",
                        "kind": "source_step",
                        "status": "proved",
                        "lean_landing": "thm_10_8_quantile_law_preservation",
                        "expected_theorem_signature": "theorem thm_10_8_quantile_law_preservation : ...",
                        "landing_kind": "theorem",
                        "proof_contract_status": "verified",
                        "proof_contract_notes": "reviewed against source route",
                        "body_reassumption_check": "passed",
                        "signature_match": "passed",
                        "public_premise_check": "passed",
                    }
                ],
            },
            task,
        )

        item = payload["obligations"][0]
        self.assertEqual(item["expected_theorem_signature"], "theorem thm_10_8_quantile_law_preservation : ...")
        self.assertEqual(item["landing_kind"], "theorem")
        self.assertEqual(item["proof_contract_status"], "verified")
        self.assertEqual(item["body_reassumption_check"], "passed")
        self.assertIn("Proof contract", render_proof_obligations_markdown(payload))

    def test_pass_review_can_mark_obligation_accepted_as_proof_debt(self):
        review_input = {
            "review_basis": {
                "proof_obligations": {
                    "task_id": "prob_10_10",
                    "classification": {"requires_decomposition": True},
                    "obligations": [
                        {
                            "id": "slutsky_perturbation_support",
                            "kind": "proof_debt_support",
                            "status": "open",
                            "review_status": "unreviewed",
                            "lean_landing": "h_slutsky_add_support, h_slutsky_mul_support",
                            "blocking": True,
                        }
                    ],
                }
            }
        }
        result = {
            "obligation_review": {
                "status": "covered",
                "items": [
                    {
                        "obligation_id": "slutsky_perturbation_support",
                        "status": "accepted_as_proof_debt",
                        "evidence": "Explicit proof-debt support assumptions cover the deferred reusable lemma.",
                    }
                ],
                "open_blockers": [],
                "scaffold_assessment": [],
            }
        }

        self.assertEqual(validate_obligation_review_for_pass(review_input, result), "")

    def test_pass_review_requires_verified_contract_for_covered_obligation(self):
        review_input = {
            "review_basis": {
                "proof_obligations": {
                    "task_id": "thm_10_8",
                    "classification": {"requires_decomposition": True},
                    "obligations": [
                        {
                            "id": "source_step",
                            "kind": "source_step",
                            "status": "open",
                            "review_status": "unreviewed",
                            "lean_landing": "source_step_thm",
                            "blocking": True,
                        }
                    ],
                }
            }
        }
        result = {
            "obligation_review": {
                "status": "covered",
                "items": [{"obligation_id": "source_step", "status": "covered", "evidence": "local theorem"}],
                "open_blockers": [],
                "scaffold_assessment": [],
            }
        }

        self.assertIn(
            "pass verdict requires verified proof contract for covered obligations",
            validate_obligation_review_for_pass(review_input, result),
        )

        result["obligation_review"]["items"][0].update(
            {
                "expected_theorem_signature": "theorem source_step_thm : ...",
                "lean_landing": "source_step_thm",
                "landing_kind": "theorem",
                "proof_contract_status": "verified",
                "proof_contract_notes": "signature and body checked",
                "body_reassumption_check": "passed",
                "signature_match": "passed",
                "public_premise_check": "passed",
            }
        )
        self.assertEqual(validate_obligation_review_for_pass(review_input, result), "")

    def test_focused_obligation_review_only_requires_focus_ids(self):
        review_input = {
            "review_basis": {
                "focus_obligation_ids": ["event_measurability"],
                "proof_obligations": {
                    "task_id": "thm_10_8",
                    "classification": {"requires_decomposition": True},
                    "obligations": [
                        {
                            "id": "event_measurability",
                            "kind": "proof_debt_support",
                            "status": "accepted_as_proof_debt",
                            "review_status": "accepted",
                            "lean_landing": "event_measurable",
                            "blocking": True,
                        },
                        {
                            "id": "as_convergence",
                            "kind": "source_step",
                            "status": "blocked",
                            "review_status": "rejected",
                            "lean_landing": "as_convergence",
                            "blocking": True,
                        },
                    ],
                },
            }
        }
        result = {
            "obligation_review": {
                "status": "covered",
                "items": [
                    {
                        "obligation_id": "event_measurability",
                        "status": "covered",
                        "evidence": "Local theorem-level event measurability has been supplied.",
                    }
                ],
                "open_blockers": [],
                "scaffold_assessment": [],
            }
        }

        self.assertEqual(validate_obligation_review_for_pass(review_input, result), "")


if __name__ == "__main__":
    unittest.main()
