/-
TASK ID: thm_8_6
TYPE: Theorem_with_Proof
SOURCE PLAN: 34_chap8_total_variation_distance
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Tactic
import ProbabilityTheory.chapter_08.def_8_5
import ProbabilityTheory.common_support.tv_distance_core





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
  calc
    totalVariationDistance P Q
        = totalVariationDistance P.toPMF.toMeasure Q.toPMF.toMeasure := by
            rw [Measure.toPMF_toMeasure, Measure.toPMF_toMeasure]
    _ = (1 / 2 : ℝ) * ∑' n, |((P.toPMF n).toReal - (Q.toPMF n).toReal)| := by
            exact thm_8_6_discrete_pmf P.toPMF Q.toPMF
    _ = (1 / 2 : ℝ) * ∑' n, |P.real {n} - Q.real {n}| := by
            simp [Measure.toPMF_apply, Measure.real_def]



theorem thm_8_6_continuous
    {f g : ℝ → ℝ} (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_int : Integrable f volume) (hg_int : Integrable g volume)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x)
    (hf_prob : ∫ x, f x = 1) (hg_prob : ∫ x, g x = 1) :
    totalVariationDistance (densityMeasure f) (densityMeasure g)
      = (1 / 2 : ℝ) * ∫ x, |densityDiff f g x| := by
  exact TVCore.continuous_totalVariationDistance_eq_half_integral_abs
    hf_meas hg_meas hf_int hg_int hf_nonneg hg_nonneg hf_prob hg_prob

 
theorem thm_8_6 :
    (∀ (P Q : Measure ℕ) (_ : IsProbabilityMeasure P) (_ : IsProbabilityMeasure Q),
      totalVariationDistance P Q = (1 / 2 : ℝ) * ∑' n, |P.real {n} - Q.real {n}|) ∧
    (∀ (f g : ℝ → ℝ),
      Measurable f →
      Measurable g →
      Integrable f volume →
      Integrable g volume →
      (∀ x, 0 ≤ f x) →
      (∀ x, 0 ≤ g x) →
      (∫ x, f x = 1) →
      (∫ x, g x = 1) →
      totalVariationDistance (densityMeasure f) (densityMeasure g)
        = (1 / 2 : ℝ) * ∫ x, |densityDiff f g x|) := by
  constructor
  · intro P Q hP hQ
    letI := hP
    letI := hQ
    exact thm_8_6_discrete P Q
  · intro f g hf_meas hg_meas hf_int hg_int hf_nonneg hg_nonneg hf_prob hg_prob
    exact thm_8_6_continuous hf_meas hg_meas hf_int hg_int hf_nonneg hg_nonneg hf_prob hg_prob
