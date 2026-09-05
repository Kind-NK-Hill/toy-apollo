/-
TASK ID: prob_8_5
TYPE: Problem
SOURCE PLAN: 35_chap8_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.common_support.tv_distance_core




open MeasureTheory MeasurableSpace Set ENNReal

noncomputable section

open TVCore

private lemma integral_diff_eq (f g h : ℝ → ℝ)
    (hf_int : Integrable f volume) (hg_int : Integrable g volume)
    (hbounded : ∃ M, ∀ x, |h x| ≤ M) (hmeas : Measurable h)
    (B : Set ℝ) (hBmeas : MeasurableSet B) :
    (∫ x in B, h x * f x) - (∫ x in B, h x * g x) =
    ∫ x in B, h x * (f x - g x) := by
  simp +decide only [mul_sub]
  rw [MeasureTheory.integral_sub]
  · refine' MeasureTheory.Integrable.mono' _ _ _
    refine' fun x => hbounded.choose * |f x|
    · exact MeasureTheory.Integrable.const_mul (hf_int.norm.restrict) _
    · exact hmeas.aestronglyMeasurable.mul
        (hf_int.1.mono_measure <| MeasureTheory.Measure.restrict_le_self)
    · filter_upwards [] with x using by
        simpa only [Real.norm_eq_abs, abs_mul] using
          mul_le_mul_of_nonneg_right (hbounded.choose_spec x) (abs_nonneg _)
  · refine' MeasureTheory.Integrable.mono' _ _ _
    refine' fun x => hbounded.choose * |g x|
    · exact MeasureTheory.Integrable.const_mul (hg_int.norm.restrict) _
    · exact hmeas.aestronglyMeasurable.mul
        (hg_int.1.mono_measure <| MeasureTheory.Measure.restrict_le_self)
    · filter_upwards [] using fun x => by
        simpa [abs_mul] using
          mul_le_mul_of_nonneg_right (hbounded.choose_spec x) (abs_nonneg (g x))

private lemma abs_integral_le_integral_abs_mul_abs (f g h : ℝ → ℝ)
    (hf_int : Integrable f volume) (hg_int : Integrable g volume)
    (hbounded : ∃ M, ∀ x, |h x| ≤ M) (hmeas : Measurable h)
    (B : Set ℝ) (hBmeas : MeasurableSet B) :
    |∫ x in B, h x * (f x - g x)| ≤ ∫ x in B, |h x| * |f x - g x| := by
  refine' le_trans (MeasureTheory.norm_integral_le_integral_norm (_ : ℝ → ℝ)) _
  norm_num [abs_mul]

private lemma integral_abs_mul_le_sup_abs_mul (f g h : ℝ → ℝ)
    (hf_int : Integrable f volume) (hg_int : Integrable g volume)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hbounded : ∃ M, ∀ x, |h x| ≤ M) (hmeas : Measurable h)
    (B : Set ℝ) (hBmeas : MeasurableSet B) :
    ∫ x in B, |h x| * |f x - g x| ≤
      (⨆ x ∈ B, |h x|) * ∫ x in B, |f x - g x| := by
  have h_abs_le_sup : ∀ x ∈ B, |h x| ≤ ⨆ x ∈ B, |h x| := by
    intros x hx
    apply le_csSup
    · obtain ⟨M, hM⟩ := hbounded
      have hM_nonneg : 0 ≤ M := (abs_nonneg (h x)).trans (hM x)
      use M
      rintro _ ⟨y, rfl⟩
      by_cases hy : y ∈ B <;> simp +decide [*, hM y]
    · exact ⟨x, by aesop⟩
  rw [← MeasureTheory.integral_const_mul]
  refine' MeasureTheory.integral_mono_of_nonneg _ _ _
  · exact Filter.Eventually.of_forall fun x =>
      mul_nonneg (abs_nonneg (h x)) (abs_nonneg _)
  · exact MeasureTheory.Integrable.const_mul
      (MeasureTheory.Integrable.abs
        (hf_int.sub hg_int |> MeasureTheory.Integrable.mono_measure <|
          MeasureTheory.Measure.restrict_le_self)) _
  · filter_upwards [MeasureTheory.ae_restrict_mem hBmeas] with x hx using
      mul_le_mul_of_nonneg_right (h_abs_le_sup x hx) (abs_nonneg _)

private lemma integral_abs_restrict_le (f g : ℝ → ℝ)
    (hf_int : Integrable f volume) (hg_int : Integrable g volume)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x)
    (B : Set ℝ) (hBmeas : MeasurableSet B) :
    ∫ x in B, |f x - g x| ≤ ∫ x, |f x - g x| := by
  apply_rules [MeasureTheory.setIntegral_le_integral]
  · exact MeasureTheory.Integrable.abs (hf_int.sub hg_int)
  · exact Filter.Eventually.of_forall fun x => abs_nonneg _

private lemma tv_eq_half_integral_abs (μ ν : Measure ℝ)
    (f g : ℝ → ℝ) (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x)
    (hf_int : Integrable f volume) (hg_int : Integrable g volume)
    (hf_prob : ∫ x, f x = 1) (hg_prob : ∫ x, g x = 1)
    (hμ : μ = densityMeasure f) (hν : ν = densityMeasure g) :
    totalVariationDistance μ ν = (1 / 2) * ∫ x, |f x - g x| := by
  rw [hμ, hν]
  simpa [densityDiff] using
    (continuous_totalVariationDistance_eq_half_integral_abs
      hf_meas hg_meas hf_int hg_int hf_nonneg hg_nonneg hf_prob hg_prob)



theorem prob_8_5 (μ ν : MeasureTheory.Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f g : ℝ → ℝ)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x)
    (hf_int : Integrable f volume) (hg_int : Integrable g volume)
    (hf_prob : ∫ x, f x = 1) (hg_prob : ∫ x, g x = 1)
    (hμpdf : μ = densityMeasure f) (hνpdf : ν = densityMeasure g)
    (h : ℝ → ℝ) (hbounded : ∃ M : ℝ, ∀ x, |h x| ≤ M)
    (hmeas : Measurable h)
    (B : Set ℝ) (hBmeas : MeasurableSet B) :
    |(∫ x in B, h x * f x ∂volume) - (∫ x in B, h x * g x ∂volume)| ≤
    2 * totalVariationDistance μ ν * (⨆ x ∈ B, |h x|) := by
  have step1 := integral_diff_eq f g h hf_int hg_int hbounded hmeas B hBmeas
  have step2 := abs_integral_le_integral_abs_mul_abs f g h hf_int hg_int hbounded
    hmeas B hBmeas
  have step3 := integral_abs_mul_le_sup_abs_mul f g h hf_int hg_int hf_meas hg_meas
    hbounded hmeas B hBmeas
  have step4 := integral_abs_restrict_le f g hf_int hg_int hf_nonneg hg_nonneg B hBmeas
  have step5 := tv_eq_half_integral_abs μ ν f g hf_meas hg_meas hf_nonneg hg_nonneg
    hf_int hg_int hf_prob hg_prob hμpdf hνpdf
  calc
    |(∫ x in B, h x * f x) - ∫ x in B, h x * g x|
        = |∫ x in B, h x * (f x - g x)| := by rw [step1]
    _ ≤ ∫ x in B, |h x| * |f x - g x| := step2
    _ ≤ (⨆ x ∈ B, |h x|) * ∫ x in B, |f x - g x| := step3
    _ ≤ (⨆ x ∈ B, |h x|) * ∫ x, |f x - g x| := by
        apply mul_le_mul_of_nonneg_left step4
        apply Real.iSup_nonneg
        intro x
        apply Real.iSup_nonneg
        intro _
        exact abs_nonneg (h x)
    _ = 2 * totalVariationDistance μ ν * (⨆ x ∈ B, |h x|) := by
        rw [step5]
        ring



theorem prob_8_5_of_nonnegative
    (μ ν : MeasureTheory.Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f g : ℝ → ℝ)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x)
    (hf_int : Integrable f volume) (hg_int : Integrable g volume)
    (hf_prob : ∫ x, f x = 1) (hg_prob : ∫ x, g x = 1)
    (hμpdf : μ = densityMeasure f) (hνpdf : ν = densityMeasure g)
    (h : ℝ → ℝ) (hbounded : ∃ M : ℝ, ∀ x, |h x| ≤ M)
    (hmeas : Measurable h) (hh_nonneg : ∀ x, 0 ≤ h x)
    (B : Set ℝ) (hBmeas : MeasurableSet B) :
    |(∫ x in B, h x * f x ∂volume) - (∫ x in B, h x * g x ∂volume)| ≤
    2 * totalVariationDistance μ ν * (⨆ x ∈ B, h x) := by
  simpa only [abs_of_nonneg (hh_nonneg _)] using
    (prob_8_5 μ ν f g hf_meas hg_meas hf_nonneg hg_nonneg hf_int hg_int
      hf_prob hg_prob hμpdf hνpdf h hbounded hmeas B hBmeas)
