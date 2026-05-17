import sys
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.toy_apollo.phase2_proof_obligations import (  # noqa: E402
    default_proof_obligations,
    needs_concrete_decomposition,
    normalize_proof_obligations,
    summarize_proof_obligations,
)


class Phase2ProofObligationsTests(unittest.TestCase):
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


if __name__ == "__main__":
    unittest.main()
