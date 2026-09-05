import json
import re
import sys
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


def canonical_file(basename: str) -> Path:
    matches = list((REPO_ROOT / "ProbabilityTheory").rglob(f"{basename}.lean"))
    if len(matches) != 1:
        raise AssertionError(f"expected one canonical module for {basename}, found {matches}")
    return matches[0]


class Phase2HealthImprovementTests(unittest.TestCase):
    def _private_obligations(self, task_id: str) -> dict:
        path = REPO_ROOT / "phase2_prompt_packs" / task_id / "proof_obligations.json"
        if not path.is_file():
            self.skipTest("requires private prompt-pack obligation fixture")
        return json.loads(path.read_text(encoding="utf-8"))

    def test_coupon_active_obligation_metadata_does_not_repeat_superseded_private_axiom_debt(self):
        stale_phrases = [
            "private axiom",
            "open_math_debt",
            "has no theorem-level landing",
            "Do not count the private axiom",
            "Reopened on 2026-05-21",
        ]
        for task_id in ["ex_14_4_3", "prob_14_11"]:
            payload = self._private_obligations(task_id)
            active_text = json.dumps(payload.get("obligations", []), ensure_ascii=False)
            for phrase in stale_phrases:
                self.assertNotIn(phrase, active_text, f"{task_id} active obligation metadata is stale")

    def test_dirichlet_gamma_support_wrapper_is_thin_reexport(self):
        wrapper = canonical_file("ex_1_2_2_dirichlet_gamma_support")
        source = wrapper.read_text(encoding="utf-8")
        self.assertIn(
            "import ProbabilityTheory.chapter_01.ex_1_2_2_dirichlet_gamma_beta",
            source,
        )
        self.assertLessEqual(len(source.splitlines()), 20)
        for marker in ["def ", "theorem ", "lemma ", "axiom ", "structure "]:
            self.assertNotIn(marker, source)

    def test_chapter13_stopping_support_is_shared_by_prob_13_10_family(self):
        shared = canonical_file("chapter13_stopping_support")
        self.assertTrue(shared.exists())
        shared_source = shared.read_text(encoding="utf-8")
        for name in [
            "chapter13_stoppedNatSum",
            "chapter13_oneIndexedNaturalFiltration",
            "chapter13_stoppedSum_centered_eq",
        ]:
            self.assertIn(name, shared_source)

        for basename in [
            "prob_13_10_stopped_sum_support",
            "prob_13_10_centered_wald_support",
        ]:
            source = canonical_file(basename).read_text(encoding="utf-8")
            self.assertIn(
                "import ProbabilityTheory.common_support.chapter13_stopping_support",
                source,
            )

    def test_prob_14_11_parent_delegates_large_support_body(self):
        parent = canonical_file("prob_14_11")
        support = canonical_file("prob_14_11_support")
        self.assertTrue(support.exists())

        parent_source = parent.read_text(encoding="utf-8")
        support_source = support.read_text(encoding="utf-8")
        self.assertIn("import ProbabilityTheory.chapter_14.prob_14_11_support", parent_source)
        self.assertLessEqual(len(parent_source.splitlines()), 80)
        self.assertRegex(parent_source, r"(?m)^theorem prob_14_11\b")
        self.assertNotRegex(support_source, r"(?m)^theorem prob_14_11\b")

        support_markers = [
            "structure prob_14_11_CouponRatioTriangularArraySetup",
            "def prob_14_11_couponProbabilitySpace",
            "def prob_14_11_exactStandardizedRowSumLaws",
            "def prob_14_11_theoremSetup",
            "theorem prob_14_11_generalized_lyapunov_condition",
            "def prob_14_11_ExactStandardizedConvergence",
        ]
        for marker in support_markers:
            self.assertIn(marker, support_source)
            self.assertNotIn(marker, parent_source)

    def test_ex_14_4_2_does_not_export_nested_obligation_landings(self):
        source = canonical_file("ex_14_4_2").read_text(encoding="utf-8")
        self.assertNotRegex(
            source,
            r"(?m)^(?:theorem|lemma|def|structure|axiom)\s+obl_obl_ex_14_4_2_",
        )

    def test_thm_7_8_does_not_export_legacy_obligation_landings(self):
        source = canonical_file("thm_7_8").read_text(encoding="utf-8")
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
            payload = self._private_obligations(task_id)
            for obligation in payload.get("obligations", []):
                landing = obligation.get("lean_landing", "")
                self.assertNotIn(prefix, landing)

    def test_rs_step_support_replaces_chapter1_public_axioms_with_theorems(self):
        source = canonical_file("rs_stieltjes_step_support").read_text(encoding="utf-8")
        for name in [
            "rsIntegrable_of_bounded_finite_discontinuities",
            "rsIntegral_sqrt_floor_add_id_0_2",
        ]:
            self.assertNotRegex(source, rf"(?m)^axiom\s+{name}\b")
            self.assertRegex(source, rf"(?m)^theorem\s+{name}\b")

    def test_rs_legacy_bridge_does_not_reexport_chapter7_debt_to_chapter1(self):
        output_dir = REPO_ROOT / "ProbabilityTheory"
        self.assertEqual(list(output_dir.rglob("rs_stieltjes_bridge.lean")), [])
        for path in output_dir.rglob("*.lean"):
            source = path.read_text(encoding="utf-8")
            self.assertNotIn("import ProbabilityTheory.rs_stieltjes_bridge", source)
        self.assertIn(
            "import ProbabilityTheory.chapter_01.rs_stieltjes_step_support",
            canonical_file("prob_1_8").read_text(encoding="utf-8"),
        )

    def test_retired_distribution_bridges_do_not_export_public_axioms(self):
        output_dir = REPO_ROOT / "ProbabilityTheory"
        official_sources = [
            path
            for path in output_dir.rglob("*.lean")
            if path.name not in {"gamma_beta_bridge.lean", "cantor_distribution_bridge.lean"}
        ]
        for module in ["gamma_beta_bridge", "cantor_distribution_bridge"]:
            import_line = f"import ProbabilityTheory.{module}"
            for path in official_sources:
                self.assertNotIn(import_line, path.read_text(encoding="utf-8"))

            matches = list(output_dir.rglob(f"{module}.lean"))
            if matches:
                self.assertEqual(len(matches), 1)
                self.assertNotRegex(matches[0].read_text(encoding="utf-8"), r"(?m)^axiom\s+")

    def test_official_output_exports_no_public_axioms(self):
        output_dir = REPO_ROOT / "ProbabilityTheory"
        axiom_decl = re.compile(
            r"(?m)^\s*(?:@[^\n]*\n\s*)*(?:noncomputable\s+)?"
            r"(?:private\s+)?axiom\s+"
        )
        axiom_sites = []
        for path in sorted(output_dir.rglob("*.lean")):
            source = path.read_text(encoding="utf-8")
            for match in axiom_decl.finditer(source):
                line_number = source.count("\n", 0, match.start()) + 1
                line = source.splitlines()[line_number - 1].strip()
                axiom_sites.append(f"{path.relative_to(REPO_ROOT)}:{line_number}:{line}")
        self.assertEqual([], axiom_sites)

    def test_official_output_exports_no_legacy_obligation_declarations(self):
        output_dir = REPO_ROOT / "ProbabilityTheory"
        legacy_decl = re.compile(
            r"(?m)^\s*(?:@[^\n]*\n\s*)*(?:noncomputable\s+)?"
            r"(?:private\s+)?(?:theorem|lemma|def|structure|axiom)\s+obl_"
        )
        legacy_sites = []
        for path in sorted(output_dir.rglob("*.lean")):
            source = path.read_text(encoding="utf-8")
            for match in legacy_decl.finditer(source):
                line_number = source.count("\n", 0, match.start()) + 1
                line = source.splitlines()[line_number - 1].strip()
                legacy_sites.append(f"{path.relative_to(REPO_ROOT)}:{line_number}:{line}")
        self.assertEqual([], legacy_sites)

    def test_retired_rs_ls_bridge_names_do_not_reenter_official_output(self):
        output_dir = REPO_ROOT / "ProbabilityTheory"
        tombstones = {
            "rs_stieltjes_ch7_bridge_debt.lean",
            "rs_stieltjes_future_ls_bridge_debt.lean",
        }
        retired_modules = [
            "ProbabilityTheory.rs_stieltjes_ch7_bridge_debt",
            "ProbabilityTheory.rs_stieltjes_future_ls_bridge_debt",
        ]
        retired_names = [
            "lsIntegral_eq_rsIntegral_stieltjesFunction",
            "improperRS_abs_iff_integrable_abs_stieltjes",
            "expectation_eq_integral_density_of_stieltjes_deriv",
            "rsIntegrable_iff_ae_continuous_stieltjes",
            "rsIntegrable_completion_integral_eq",
        ]
        for path in sorted(output_dir.rglob("*.lean")):
            if path.name in tombstones:
                continue
            source = path.read_text(encoding="utf-8")
            for module in retired_modules:
                self.assertNotIn(f"import {module}", source, str(path))
            for name in retired_names:
                self.assertNotRegex(source, rf"\b{name}\b", str(path))

    def test_retired_prob_14_1_cdf_interface_names_do_not_reenter_official_output(self):
        output_dir = REPO_ROOT / "ProbabilityTheory"
        retired_names = [
            "prob_14_1_riemannSumCdfLimitInterface",
            "prob_14_1_continuity_point_interface",
            "prob_14_1_cdfConvergence_of_riemannSumInterface",
        ]
        for path in sorted(output_dir.rglob("prob_14_1_*.lean")):
            source = path.read_text(encoding="utf-8")
            for name in retired_names:
                self.assertNotRegex(source, rf"\b{name}\b", str(path))


if __name__ == "__main__":
    unittest.main()
