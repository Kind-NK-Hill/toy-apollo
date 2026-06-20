/-
TASK ID: prob_14_1_tail_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.prob_14_1_tail_endpoint_support

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators ENNReal Asymptotics

noncomputable section

theorem prob_14_1_gridCdfLimit_standardBeta
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b) :
    prob_14_1_gridCdfLimit w b (prob_14_1_standardBetaLawData hw hb) := by
  exact
    prob_14_1_gridCdfLimit_of_interior
      (w := w) (b := b) hw hb (prob_14_1_standardBetaLawData hw hb)
      (fun x hx0 hx1 hxcont =>
        prob_14_1_interior_gridCdf_tendsto
          (w := w) (b := b) hw hb hx0 hx1 hxcont)

theorem prob_14_1_gridCdfLimit_setup
    (S : prob_14_1_PolyaUrnBetaSetup) :
    prob_14_1_gridCdfLimit S.w S.b S.beta := by
  simpa [prob_14_1_PolyaUrnBetaSetup.beta] using
    prob_14_1_gridCdfLimit_standardBeta S.w_pos S.b_pos

theorem prob_14_1_stirling_beta_cdf_convergence
    (S : prob_14_1_PolyaUrnBetaSetup) :
    prob_14_1_cdfConvergence
      (prob_14_1_whiteFractionLaws S.whiteCountLaws) S.beta.law :=
  by
    simpa [prob_14_1_stirlingBetaCdfConvergence] using
      prob_14_1_stirling_beta_cdf_convergence_from_gridCdfLimit
        S (prob_14_1_gridCdfLimit_setup S)

theorem prob_14_1_white_fraction_converges_to_beta
    (S : prob_14_1_PolyaUrnBetaSetup) :
    Tendsto (prob_14_1_whiteFractionLaws S.whiteCountLaws) atTop (𝓝 S.beta.law) :=
  prob_14_1_cdfConvergence_to_weak
    (prob_14_1_stirling_beta_cdf_convergence S)

theorem prob_14_1_support_result
    (S : prob_14_1_PolyaUrnBetaSetup) :
    (∀ i k : ℕ, 1 ≤ i → k ≤ i →
      (S.whiteCountLaws i : Measure ℝ) {x : ℝ | x = (k : ℝ)} =
        ENNReal.ofReal (prob_14_1_polyaWhiteMassFormula S.w S.b i k)) ∧
      Tendsto (prob_14_1_whiteFractionLaws S.whiteCountLaws) atTop (𝓝 S.beta.law) ∧
        def_14_1 (prob_14_1_whiteFractionLaws S.whiteCountLaws) S.beta.law := by
  have hWeak := prob_14_1_white_fraction_converges_to_beta S
  exact ⟨
    (fun i k hi hk => prob_14_1_white_count_mass S hi hk),
    hWeak,
    (def_14_1_iff_tendsto).2 hWeak⟩
