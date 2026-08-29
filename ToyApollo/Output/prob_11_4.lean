/-
TASK ID: prob_11_4
TYPE: Problem
SOURCE PLAN: chapter11-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_11_6

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory

noncomputable def prob_11_4_pdf (x : ℝ) : ℝ :=
  if 1 ≤ x then 2 * x ^ (-(3 : ℝ)) else 0

noncomputable def prob_11_4_densityMeasure : Measure ℝ :=
  (volume : Measure ℝ).withDensity fun x => ENNReal.ofReal (prob_11_4_pdf x)

lemma prob_11_4_pdf_nonneg (x : ℝ) : 0 ≤ prob_11_4_pdf x := by
  by_cases hx : 1 ≤ x
  · have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    simp [prob_11_4_pdf, hx]
    positivity
  · simp [prob_11_4_pdf, hx]

lemma prob_11_4_pdf_measurable : Measurable prob_11_4_pdf := by
  unfold prob_11_4_pdf
  exact Measurable.ite measurableSet_Ici
    ((measurable_id.pow_const _).const_mul _) measurable_const

theorem prob_11_4_pdf_first_moment :
    ∫ x, x * prob_11_4_pdf x = (2 : ℝ) := by
  have h_point :
      (fun x => x * prob_11_4_pdf x) =
        (Set.Ici (1 : ℝ)).indicator (fun x => 2 * x ^ (-(2 : ℝ))) := by
    funext x
    by_cases hx : 1 ≤ x
    · have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
      simp [prob_11_4_pdf, hx]
      field_simp [hxpos.ne']
    · simp [prob_11_4_pdf, hx]
  rw [h_point, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)]
  norm_num

theorem prob_11_4_mean_of_density {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (hInt : Integrable (X 0) P)
    (hDensity : Measure.map (X 0) P = prob_11_4_densityMeasure) :
    P[X 0] = (2 : ℝ) := by
  change (∫ ω, X 0 ω ∂P) = (2 : ℝ)
  calc
    ∫ ω, X 0 ω ∂P = ∫ x, x ∂Measure.map (X 0) P := by
      exact
        (MeasureTheory.integral_map hInt.aestronglyMeasurable.aemeasurable
          (f := fun x : ℝ => x) (by fun_prop)).symm
    _ = ∫ x, x ∂prob_11_4_densityMeasure := by
      rw [hDensity]
    _ = ∫ x, x ∂((volume : Measure ℝ).withDensity
        fun x => ENNReal.ofReal (prob_11_4_pdf x)) := rfl
    _ = ∫ x, x * prob_11_4_pdf x := by
      rw [integral_withDensity_eq_integral_toReal_smul
        prob_11_4_pdf_measurable.ennreal_ofReal]
      · apply integral_congr_ae
        filter_upwards with x
        rw [ENNReal.toReal_ofReal (prob_11_4_pdf_nonneg x)]
        simp [smul_eq_mul, mul_comm]
      · filter_upwards with x
        exact ENNReal.ofReal_lt_top
    _ = 2 := prob_11_4_pdf_first_moment

theorem prob_11_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hInt : Integrable (X 0) P)
    (hMeas : ∀ i, Measurable (X i))
    (hDensity : Measure.map (X 0) P = prob_11_4_densityMeasure)
    (hInd : def_5_10_randomVariables P X)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ConvergesInProbability P (fun n => thm_11_5_sampleMean X n)
      (fun _ => (2 : ℝ)) := by
  have hMean : P[X 0] = (2 : ℝ) :=
    prob_11_4_mean_of_density P X hInt hDensity
  exact thm_11_6 P X 2 hInt hMeas hInd hIdent hMean
