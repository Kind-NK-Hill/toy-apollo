import sys
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.toy_apollo.phase2_proof_obligations import (  # noqa: E402
    default_proof_obligations,
    needs_concrete_decomposition,
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


if __name__ == "__main__":
    unittest.main()
