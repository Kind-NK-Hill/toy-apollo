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

    def test_prob_14_11_parent_delegates_large_support_body(self):
        parent = REPO_ROOT / "ToyApollo" / "Output" / "prob_14_11.lean"
        support = REPO_ROOT / "ToyApollo" / "Output" / "prob_14_11_support.lean"
        self.assertTrue(support.exists())

        parent_source = parent.read_text(encoding="utf-8")
        support_source = support.read_text(encoding="utf-8")
        self.assertIn("import ToyApollo.Output.prob_14_11_support", parent_source)
        self.assertLessEqual(len(parent_source.splitlines()), 80)
        self.assertRegex(parent_source, r"(?m)^theorem prob_14_11\b")
        self.assertNotRegex(support_source, r"(?m)^theorem prob_14_11\b")

        support_markers = [
            "structure prob_14_11_CouponRatioTriangularArraySetup",
            "def prob_14_11_couponProbabilitySpace",
            "def prob_14_11_exactStandardizedRowSumLaws",
            "def prob_14_11_theoremSetupExact",
            "theorem prob_14_11_generalized_lyapunov_condition",
            "def prob_14_11_ExactStandardizedConvergence",
        ]
        for marker in support_markers:
            self.assertIn(marker, support_source)
            self.assertNotIn(marker, parent_source)

    def test_ex_14_4_2_does_not_export_nested_obligation_landings(self):
        source = (REPO_ROOT / "ToyApollo" / "Output" / "ex_14_4_2.lean").read_text(
            encoding="utf-8"
        )
        self.assertNotRegex(
            source,
            r"(?m)^(?:theorem|lemma|def|structure|axiom)\s+obl_obl_ex_14_4_2_",
        )

    def test_thm_7_8_does_not_export_legacy_obligation_landings(self):
        source = (REPO_ROOT / "ToyApollo" / "Output" / "thm_7_8.lean").read_text(
            encoding="utf-8"
        )
        self.assertNotRegex(
            source,
            r"(?m)^(?:theorem|lemma|def|structure|axiom)\s+obl_thm_7_8_",
        )

    def test_current_obligation_landings_do_not_use_retired_health_prefixes(self):
        retired_prefixes = {
            "ex_14_4_2": "obl_obl_ex_14_4_2_",
            "thm_7_8": "obl_thm_7_8_",
        }
        for task_id, prefix in retired_prefixes.items():
            path = REPO_ROOT / "phase2_prompt_packs" / task_id / "proof_obligations.json"
            payload = json.loads(path.read_text(encoding="utf-8"))
            for obligation in payload.get("obligations", []):
                landing = obligation.get("lean_landing", "")
                self.assertNotIn(prefix, landing)


if __name__ == "__main__":
    unittest.main()
