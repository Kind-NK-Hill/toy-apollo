/-
TASK ID: thm_8_6
TYPE: Theorem_with_Proof
SOURCE PLAN: 34_chap8_total_variation_distance
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_8_5
import ToyApollo.Output.tv_distance_core

open MeasureTheory Set
open TVCore

noncomputable section

theorem thm_8_6_discrete_pmf (p q : PMF ℕ) :
    totalVariationDistance p.toMeasure q.toMeasure
      = (1 / 2 : ℝ) * ∑' n, |(p n).toReal - (q n).toReal| := by
  simpa [TVCore.pmfDiff, TVCore.pmfReal] using
    TVCore.discrete_totalVariationDistance_eq_half_tsum_abs p q

theorem thm_8_6_discrete (P Q : Measure ℕ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    totalVariationDistance P Q
      = (1 / 2 : ℝ) * ∑' n, |P.real {n} - Q.real {n}| := by
  simpa [Measure.toPMF_apply, Measure.real_def] using
    thm_8_6_discrete_pmf P.toPMF Q.toPMF

theorem thm_8_6_continuous
    {f g : ℝ → ℝ} (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_int : Integrable f volume) (hg_int : Integrable g volume)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x)
    (hf_prob : ∫ x, f x = 1) (hg_prob : ∫ x, g x = 1) :
    @totalVariationDistance ℝ _ (densityMeasure f) (densityMeasure g)
      (densityMeasure_isProbabilityMeasure hf_int hf_nonneg hf_prob)
      (densityMeasure_isProbabilityMeasure hg_int hg_nonneg hg_prob)
      = (1 / 2 : ℝ) * ∫ x, |densityDiff f g x| := by
  exact TVCore.continuous_totalVariationDistance_eq_half_integral_abs
    hf_meas hg_meas hf_int hg_int hf_nonneg hg_nonneg hf_prob hg_prob

theorem thm_8_6 :
    (∀ (P Q : Measure ℕ) (hP : IsProbabilityMeasure P) (hQ : IsProbabilityMeasure Q),
      @totalVariationDistance ℕ _ P Q hP hQ
        = (1 / 2 : ℝ) * ∑' n, |P.real {n} - Q.real {n}|) ∧
    (∀ (f g : ℝ → ℝ),
      (hf_meas : Measurable f) →
      (hg_meas : Measurable g) →
      (hf_int : Integrable f volume) →
      (hg_int : Integrable g volume) →
      (hf_nonneg : ∀ x, 0 ≤ f x) →
      (hg_nonneg : ∀ x, 0 ≤ g x) →
      (hf_prob : ∫ x, f x = 1) →
      (hg_prob : ∫ x, g x = 1) →
      @totalVariationDistance ℝ _ (densityMeasure f) (densityMeasure g)
        (densityMeasure_isProbabilityMeasure hf_int hf_nonneg hf_prob)
        (densityMeasure_isProbabilityMeasure hg_int hg_nonneg hg_prob)
        = (1 / 2 : ℝ) * ∫ x, |densityDiff f g x|) := by
  constructor
  · intro P Q hP hQ
    letI := hP
    letI := hQ
    exact thm_8_6_discrete P Q
  · intro f g hf_meas hg_meas hf_int hg_int hf_nonneg hg_nonneg hf_prob hg_prob
    exact thm_8_6_continuous hf_meas hg_meas hf_int hg_int hf_nonneg hg_nonneg hf_prob hg_prob
