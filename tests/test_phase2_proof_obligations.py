import sys
import json
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
    summarize_proof_obligations,
    validate_obligation_review_for_pass,
)


class Phase2ProofObligationsTests(unittest.TestCase):
    def test_thm_10_8_quantile_law_debt_uses_local_bridge(self):
        lean_path = REPO_ROOT / "ToyApollo" / "Output" / "thm_10_8.lean"
        obligations_path = REPO_ROOT / "phase2_prompt_packs" / "thm_10_8" / "proof_obligations.json"

        lean = lean_path.read_text(encoding="utf-8")
        obligations = json.loads(obligations_path.read_text(encoding="utf-8"))
        by_id = {item["id"]: item for item in obligations["obligations"]}

        self.assertNotIn("quantile_law_preservation :", lean)
        self.assertIn("thm_10_8_quantile_law_preservation_seq_of_Iic", lean)
        self.assertIn("thm_10_8_quantile_law_preservation_of_Iic", lean)
        self.assertEqual(by_id["quantile_law_preservation"]["status"], "proved")
        self.assertEqual(by_id["quantile_law_preservation"]["kind"], "source_step")
        self.assertEqual(by_id["quantile_event_measurability"]["status"], "accepted_as_proof_debt")
        self.assertIn("event calculation", by_id["quantile_event_measurability"]["notes"])

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
