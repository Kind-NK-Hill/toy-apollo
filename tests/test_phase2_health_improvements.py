import json
import sys
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


class Phase2HealthImprovementTests(unittest.TestCase):
    def test_coupon_active_obligation_metadata_does_not_repeat_superseded_private_axiom_debt(self):
        stale_phrases = [
            "private axiom",
            "open_math_debt",
            "has no theorem-level landing",
            "Do not count the private axiom",
            "Reopened on 2026-05-21",
        ]
        for task_id in ["ex_14_4_3", "prob_14_11"]:
            path = REPO_ROOT / "phase2_prompt_packs" / task_id / "proof_obligations.json"
            payload = json.loads(path.read_text(encoding="utf-8"))
            active_text = json.dumps(payload.get("obligations", []), ensure_ascii=False)
            for phrase in stale_phrases:
                self.assertNotIn(phrase, active_text, f"{task_id} active obligation metadata is stale")

    def test_dirichlet_gamma_support_wrapper_is_thin_reexport(self):
        wrapper = REPO_ROOT / "ToyApollo" / "Output" / "ex_1_2_2_dirichlet_gamma_support.lean"
        source = wrapper.read_text(encoding="utf-8")
        self.assertIn("import ToyApollo.Output.ex_1_2_2_dirichlet_gamma_beta", source)
        self.assertLessEqual(len(source.splitlines()), 20)
        for marker in ["def ", "theorem ", "lemma ", "axiom ", "structure "]:
            self.assertNotIn(marker, source)

    def test_chapter13_stopping_support_is_shared_by_prob_13_10_family(self):
        shared = REPO_ROOT / "ToyApollo" / "Output" / "chapter13_stopping_support.lean"
        self.assertTrue(shared.exists())
        shared_source = shared.read_text(encoding="utf-8")
        for name in [
            "chapter13_stoppedNatSum",
            "chapter13_oneIndexedNaturalFiltration",
            "chapter13_stoppedSum_centered_eq",
        ]:
            self.assertIn(name, shared_source)

        for relative in [
            "ToyApollo/Output/prob_13_10_stopped_sum_support.lean",
            "ToyApollo/Output/prob_13_10_centered_wald_support.lean",
        ]:
            source = (REPO_ROOT / relative).read_text(encoding="utf-8")
            self.assertIn("import ToyApollo.Output.chapter13_stopping_support", source)


if __name__ == "__main__":
    unittest.main()
