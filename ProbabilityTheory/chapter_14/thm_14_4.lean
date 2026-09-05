/-
TASK ID: thm_14_4
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter14-weak-convergence
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_14.def_14_1
import ProbabilityTheory.chapter_10.ex_10_3_1
import ProbabilityTheory.chapter_14.thm_14_4_density_support




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set Metric
open scoped Topology ENNReal

noncomputable section



def thm_14_4_totalVariationConvergence
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ) : Prop :=
  Tendsto
    (fun n : ℕ => totalVariationDistance (Pseq n : Measure ℝ) (P : Measure ℝ))
    atTop (𝓝 (0 : ℝ))



theorem thm_14_4_of_boundedContinuousTestDifferenceBound
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ)
    (hTV : thm_14_4_totalVariationConvergence Pseq P)
    (hBound : thm_14_4_boundedContinuousTestDifferenceBound Pseq P) :
    def_14_1 Pseq P := by
  intro h
  let L : ℝ := ∫ x, h x ∂(P : Measure ℝ)
  have hRhs :
      Tendsto
        (fun n : ℕ =>
          (2 * ‖h‖) * totalVariationDistance (Pseq n : Measure ℝ) (P : Measure ℝ))
        atTop (𝓝 (0 : ℝ)) := by
    simpa using hTV.const_mul (2 * ‖h‖)
  have hAbs :
      Tendsto
        (fun n : ℕ => |(∫ x, h x ∂(Pseq n : Measure ℝ)) - L|)
        atTop (𝓝 (0 : ℝ)) := by
    refine squeeze_zero (fun n => abs_nonneg _) ?_ hRhs
    intro n
    simpa [L] using hBound n h
  have hSub :
      Tendsto
        (fun n : ℕ => (∫ x, h x ∂(Pseq n : Measure ℝ)) - L)
        atTop (𝓝 (0 : ℝ)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Real.norm_eq_abs] using hAbs
  have hConst : Tendsto (fun _n : ℕ => L) atTop (𝓝 L) :=
    tendsto_const_nhds
  have hAdd :
      Tendsto
        (fun n : ℕ => ((∫ x, h x ∂(Pseq n : Measure ℝ)) - L) + L)
        atTop (𝓝 (0 + L)) :=
    hSub.add hConst
  simpa [L, sub_add_cancel] using hAdd



theorem thm_14_4
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ)
    (hTV : thm_14_4_totalVariationConvergence Pseq P) :
    def_14_1 Pseq P := by
  exact thm_14_4_of_boundedContinuousTestDifferenceBound Pseq P hTV
    (thm_14_4_boundedContinuousTestDifferenceBound_from_rn Pseq P)



theorem thm_14_4_converseFailure_weakConvergence :
    def_14_1 ex_10_3_1_empiricalLaw ex_10_3_1_uniformLaw := by
  apply (def_14_1_iff_tendsto).2
  simpa [MeasuresConvergeInDistribution] using
    ex_10_3_1_distribution_convergence



theorem thm_14_4_converseFailure_not_totalVariation
    : ¬ thm_14_4_totalVariationConvergence
      ex_10_3_1_empiricalLaw ex_10_3_1_uniformLaw := by
  intro hTV
  rw [thm_14_4_totalVariationConvergence] at hTV
  have hlt :
      ∀ᶠ n : ℕ in atTop,
        totalVariationDistance
          (ex_10_3_1_empiricalLaw n : Measure ℝ)
          (ex_10_3_1_uniformLaw : Measure ℝ) < (1 / 2 : ℝ) := by
    exact hTV (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hge :
      ∀ᶠ n : ℕ in atTop,
        (1 : ℝ) ≤
        (fun n : ℕ =>
          totalVariationDistance
            (ex_10_3_1_empiricalLaw n : Measure ℝ)
            (ex_10_3_1_uniformLaw : Measure ℝ)) n := by
    filter_upwards with n
    simpa [ex_10_3_1_empiricalLaw, ex_10_3_1_uniformLaw] using
      ex_10_3_1_totalVariationDistance_ge_one n
  rcases (hlt.and hge).exists with ⟨_n, hnlt, hnge⟩
  linarith



theorem thm_14_4_converseFailure_note
    : def_14_1 ex_10_3_1_empiricalLaw ex_10_3_1_uniformLaw ∧
      ¬ thm_14_4_totalVariationConvergence
        ex_10_3_1_empiricalLaw ex_10_3_1_uniformLaw :=
  ⟨thm_14_4_converseFailure_weakConvergence,
    thm_14_4_converseFailure_not_totalVariation⟩
