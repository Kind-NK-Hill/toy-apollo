/-
TASK ID: prob_8_5
TYPE: Problem
SOURCE PLAN: 35_chap8_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory MeasurableSpace Set ENNReal

noncomputable section

noncomputable def totalVariationDistance
    {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) : ℝ :=
  sSup {d : ℝ | ∃ A : Set Ω, MeasurableSet A ∧ d = |P.real A - Q.real A|}

namespace TVCore

noncomputable def densityMeasure (f : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (f x)

def densityDiff (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  f x - g x

def densityPos (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  max (densityDiff f g x) 0

def densityPositiveSet (f g : ℝ → ℝ) : Set ℝ :=
  {x | 0 < densityDiff f g x}

lemma densityMeasure_real_apply
    {f : ℝ → ℝ} (hf_int : Integrable f volume) (hf_nonneg : ∀ x, 0 ≤ f x)
    (s : Set ℝ) (hs : MeasurableSet s) :
    (densityMeasure f).real s = ∫ x in s, f x := by
  rw [densityMeasure, Measure.real_def, withDensity_apply _ hs]
  have h_int : Integrable f (volume.restrict s) := hf_int.restrict
  have h_nonneg : 0 ≤ᵐ[volume.restrict s] f := Filter.Eventually.of_forall hf_nonneg
  have hEq :
      ENNReal.ofReal (∫ x in s, f x) = ∫⁻ x in s, ENNReal.ofReal (f x) := by
    simpa using MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int h_nonneg
  have hint_nonneg : 0 ≤ ∫ x in s, f x := by
    exact MeasureTheory.integral_nonneg fun x => hf_nonneg x
  simpa [ENNReal.toReal_ofReal hint_nonneg] using (congrArg ENNReal.toReal hEq).symm

lemma densityMeasure_apply_univ
    {f : ℝ → ℝ} (hf_int : Integrable f volume) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_prob : ∫ x, f x = 1) :
    densityMeasure f Set.univ = 1 := by
  rw [densityMeasure, withDensity_apply' _ Set.univ, Measure.restrict_univ]
  have h_nonneg : 0 ≤ᵐ[volume] f := Filter.Eventually.of_forall hf_nonneg
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_int h_nonneg, hf_prob]
  norm_num

lemma densityMeasure_real_compl_eq_one_sub
    {f : ℝ → ℝ} (hf_int : Integrable f volume) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_prob : ∫ x, f x = 1) (s : Set ℝ) (hs : MeasurableSet s) :
    (densityMeasure f).real sᶜ = 1 - (densityMeasure f).real s := by
  have hsum : densityMeasure f s + densityMeasure f sᶜ = 1 := by
    calc
      densityMeasure f s + densityMeasure f sᶜ = densityMeasure f Set.univ := by
        simpa using (measure_add_measure_compl (μ := densityMeasure f) hs)
      _ = 1 := densityMeasure_apply_univ hf_int hf_nonneg hf_prob
  have hs_ne_top : densityMeasure f s ≠ ⊤ := by
    intro hs_top
    rw [hs_top, top_add] at hsum
    simp at hsum
  have hsc_ne_top : densityMeasure f sᶜ ≠ ⊤ := by
    intro hsc_top
    rw [hsc_top, add_top] at hsum
    simp at hsum
  have hreal :
      (densityMeasure f).real s + (densityMeasure f).real sᶜ = 1 := by
    simpa [Measure.real_def, ENNReal.toReal_add, hs_ne_top, hsc_ne_top] using
      congrArg ENNReal.toReal hsum
  linarith

lemma densityDiff_measurable {f g : ℝ → ℝ}
    (hf_meas : Measurable f) (hg_meas : Measurable g) :
    Measurable (densityDiff f g) := by
  simpa [densityDiff] using hf_meas.sub hg_meas

lemma densityPositiveSet_measurable {f g : ℝ → ℝ}
    (hf_meas : Measurable f) (hg_meas : Measurable g) :
    MeasurableSet (densityPositiveSet f g) := by
  have hdiff : Measurable (densityDiff f g) := densityDiff_measurable hf_meas hg_meas
  simpa [densityPositiveSet] using measurableSet_lt measurable_const hdiff

lemma densityPos_eq_half_abs_add {f g : ℝ → ℝ} (x : ℝ) :
    densityPos f g x = (|densityDiff f g x| + densityDiff f g x) / 2 := by
  by_cases hx : 0 ≤ densityDiff f g x
  · rw [densityPos, max_eq_left hx, abs_of_nonneg hx]
    ring
  · have hx' : densityDiff f g x < 0 := lt_of_not_ge hx
    rw [densityPos, max_eq_right (le_of_lt hx'), abs_of_neg hx']
    ring

lemma integrable_densityPos {f g : ℝ → ℝ}
    (hf_int : Integrable f volume) (hg_int : Integrable g volume) :
    Integrable (densityPos f g) volume := by
  have hdiff : Integrable (densityDiff f g) volume := by
    simpa [densityDiff] using hf_int.sub hg_int
  have habs : Integrable (fun x => |densityDiff f g x|) volume := hdiff.norm
  have hadd : Integrable (fun x => |densityDiff f g x| + densityDiff f g x) volume :=
    habs.add hdiff
  have hformula :
      densityPos f g = fun x => (|densityDiff f g x| + densityDiff f g x) / 2 := by
    funext x
    exact densityPos_eq_half_abs_add (f := f) (g := g) x
  rw [hformula]
  exact hadd.div_const 2

lemma densityPositiveSet_indicator_eq_pos {f g : ℝ → ℝ} :
    (densityPositiveSet f g).indicator (densityDiff f g) = densityPos f g := by
  funext x
  by_cases hx : 0 < densityDiff f g x
  · simp [densityPositiveSet, Set.indicator_of_mem, hx, densityPos, le_of_lt hx, max_eq_left]
  · have hx' : densityDiff f g x ≤ 0 := le_of_not_gt hx
    simp [densityPositiveSet, hx, densityPos, hx', max_eq_right]

lemma densityMeasure_real_diff_eq_integral_indicator
    {f g : ℝ → ℝ} (hf_int : Integrable f volume) (hg_int : Integrable g volume)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x)
    (s : Set ℝ) (hs : MeasurableSet s) :
    (densityMeasure f).real s - (densityMeasure g).real s
      = ∫ x, s.indicator (densityDiff f g) x := by
  calc
    (densityMeasure f).real s - (densityMeasure g).real s
        = (∫ x in s, f x) - ∫ x in s, g x := by
            rw [densityMeasure_real_apply hf_int hf_nonneg s hs,
              densityMeasure_real_apply hg_int hg_nonneg s hs]
    _ = (∫ x, s.indicator f x) - ∫ x, s.indicator g x := by
            rw [← integral_indicator hs, ← integral_indicator hs]
    _ = ∫ x, (s.indicator f x - s.indicator g x) := by
            symm
            exact MeasureTheory.integral_sub (hf_int.indicator hs) (hg_int.indicator hs)
    _ = ∫ x, s.indicator (densityDiff f g) x := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro x
            by_cases hx : x ∈ s <;> simp [Set.indicator_apply, hx, densityDiff]

lemma densityDiff_indicator_le_pos
    {f g : ℝ → ℝ} (s : Set ℝ) :
    ∀ x, s.indicator (densityDiff f g) x ≤ densityPos f g x := by
  intro x
  by_cases hx : x ∈ s
  · simpa [Set.indicator_apply, hx, densityPos] using
      (le_max_left (densityDiff f g x) 0)
  · simpa [Set.indicator_apply, hx, densityPos] using
      (le_max_right (densityDiff f g x) 0)

lemma densityDiff_le_integral_pos
    {f g : ℝ → ℝ} (hf_int : Integrable f volume) (hg_int : Integrable g volume)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x)
    (s : Set ℝ) (hs : MeasurableSet s) :
    (densityMeasure f).real s - (densityMeasure g).real s ≤ ∫ x, densityPos f g x := by
  rw [densityMeasure_real_diff_eq_integral_indicator hf_int hg_int hf_nonneg hg_nonneg s hs]
  exact MeasureTheory.integral_mono_ae
    ((hf_int.sub hg_int).indicator hs)
    (integrable_densityPos hf_int hg_int)
    (Filter.Eventually.of_forall (densityDiff_indicator_le_pos (f := f) (g := g) s))

lemma densityPos_integral_eq_half_abs
    {f g : ℝ → ℝ} (hf_int : Integrable f volume) (hg_int : Integrable g volume)
    (hf_prob : ∫ x, f x = 1) (hg_prob : ∫ x, g x = 1) :
    ∫ x, densityPos f g x = (1 / 2 : ℝ) * ∫ x, |densityDiff f g x| := by
  have hdiff : Integrable (densityDiff f g) volume := by
    simpa [densityDiff] using hf_int.sub hg_int
  have habs : Integrable (fun x => |densityDiff f g x|) volume := hdiff.norm
  calc
    ∫ x, densityPos f g x
        = ∫ x, (|densityDiff f g x| + densityDiff f g x) / 2 := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro x
            exact densityPos_eq_half_abs_add (f := f) (g := g) x
    _ = ((∫ x, |densityDiff f g x|) + ∫ x, densityDiff f g x) / 2 := by
            rw [MeasureTheory.integral_div 2, MeasureTheory.integral_add habs hdiff]
    _ = ((∫ x, |densityDiff f g x|) + ((∫ x, f x) - ∫ x, g x)) / 2 := by
            have hsub : ∫ x, densityDiff f g x = (∫ x, f x) - ∫ x, g x := by
              simpa [densityDiff] using (MeasureTheory.integral_sub hf_int hg_int)
            rw [hsub]
    _ = (1 / 2 : ℝ) * ∫ x, |densityDiff f g x| := by
            rw [hf_prob, hg_prob]
            ring

lemma densityPositiveSet_real_diff_eq_half_abs
    {f g : ℝ → ℝ} (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_int : Integrable f volume) (hg_int : Integrable g volume)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x)
    (hf_prob : ∫ x, f x = 1) (hg_prob : ∫ x, g x = 1) :
    (densityMeasure f).real (densityPositiveSet f g)
      - (densityMeasure g).real (densityPositiveSet f g)
      = (1 / 2 : ℝ) * ∫ x, |densityDiff f g x| := by
  rw [densityMeasure_real_diff_eq_integral_indicator hf_int hg_int hf_nonneg hg_nonneg
      (densityPositiveSet f g) (densityPositiveSet_measurable hf_meas hg_meas)]
  rw [densityPositiveSet_indicator_eq_pos]
  exact densityPos_integral_eq_half_abs hf_int hg_int hf_prob hg_prob

theorem continuous_totalVariationDistance_eq_half_integral_abs
    {f g : ℝ → ℝ} (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_int : Integrable f volume) (hg_int : Integrable g volume)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x)
    (hf_prob : ∫ x, f x = 1) (hg_prob : ∫ x, g x = 1) :
    totalVariationDistance (densityMeasure f) (densityMeasure g)
      = (1 / 2 : ℝ) * ∫ x, |densityDiff f g x| := by
  let S : Set ℝ :=
    {d : ℝ | ∃ A : Set ℝ, MeasurableSet A ∧
      d = |(densityMeasure f).real A - (densityMeasure g).real A|}
  have hnonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨∅, MeasurableSet.empty, ?_⟩
    simp
  have hupper :
      ∀ d ∈ S, d ≤ (1 / 2 : ℝ) * ∫ x, |densityDiff f g x| := by
    intro d hd
    rcases hd with ⟨A, hA, rfl⟩
    let δ := (densityMeasure f).real A - (densityMeasure g).real A
    by_cases hδ : 0 ≤ δ
    · rw [abs_of_nonneg hδ]
      exact (densityDiff_le_integral_pos hf_int hg_int hf_nonneg hg_nonneg A hA).trans_eq
        (densityPos_integral_eq_half_abs hf_int hg_int hf_prob hg_prob)
    · have hδ' : δ < 0 := lt_of_not_ge hδ
      have hcomp :
          |δ| = (densityMeasure f).real Aᶜ - (densityMeasure g).real Aᶜ := by
        rw [abs_of_neg hδ']
        rw [densityMeasure_real_compl_eq_one_sub hf_int hf_nonneg hf_prob A hA,
          densityMeasure_real_compl_eq_one_sub hg_int hg_nonneg hg_prob A hA]
        dsimp [δ]
        ring
      rw [hcomp]
      exact (densityDiff_le_integral_pos hf_int hg_int hf_nonneg hg_nonneg Aᶜ hA.compl).trans_eq
        (densityPos_integral_eq_half_abs hf_int hg_int hf_prob hg_prob)
  have hbounded : BddAbove S := ⟨(1 / 2 : ℝ) * ∫ x, |densityDiff f g x|, hupper⟩
  have hlower :
      (1 / 2 : ℝ) * ∫ x, |densityDiff f g x| ≤
        totalVariationDistance (densityMeasure f) (densityMeasure g) := by
    unfold totalVariationDistance
    have hnonnegA :
        0 ≤ (densityMeasure f).real (densityPositiveSet f g)
          - (densityMeasure g).real (densityPositiveSet f g) := by
      rw [densityPositiveSet_real_diff_eq_half_abs hf_meas hg_meas hf_int hg_int
        hf_nonneg hg_nonneg hf_prob hg_prob]
      positivity
    have hmem :
        (1 / 2 : ℝ) * ∫ x, |densityDiff f g x| ∈ S := by
      refine ⟨densityPositiveSet f g, densityPositiveSet_measurable hf_meas hg_meas, ?_⟩
      rw [← densityPositiveSet_real_diff_eq_half_abs hf_meas hg_meas hf_int hg_int
        hf_nonneg hg_nonneg hf_prob hg_prob]
      rw [abs_of_nonneg hnonnegA]
    exact le_csSup hbounded hmem
  unfold totalVariationDistance
  apply le_antisymm
  · exact csSup_le hnonempty hupper
  · exact hlower

end TVCore

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

private lemma abs_integral_le_integral_abs (f g h : ℝ → ℝ)
    (hf_int : Integrable f volume) (hg_int : Integrable g volume)
    (hbounded : ∃ M, ∀ x, |h x| ≤ M) (hmeas : Measurable h)
    (hh_nonneg : ∀ x, 0 ≤ h x)
    (B : Set ℝ) (hBmeas : MeasurableSet B) :
    |∫ x in B, h x * (f x - g x)| ≤ ∫ x in B, h x * |f x - g x| := by
      refine' le_trans (MeasureTheory.norm_integral_le_integral_norm (_ : ℝ → ℝ)) _
      norm_num [abs_mul, abs_of_nonneg (hh_nonneg _)]

private lemma integral_mul_le_sup_mul (f g h : ℝ → ℝ)
    (hf_int : Integrable f volume) (hg_int : Integrable g volume)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hbounded : ∃ M, ∀ x, |h x| ≤ M) (hmeas : Measurable h)
    (hh_nonneg : ∀ x, 0 ≤ h x)
    (B : Set ℝ) (hBmeas : MeasurableSet B) :
    ∫ x in B, h x * |f x - g x| ≤ (⨆ x ∈ B, h x) * ∫ x in B, |f x - g x| := by
      have h_le_sup : ∀ x ∈ B, h x ≤ ⨆ x ∈ B, h x := by
        intros x hx
        apply le_csSup
        · obtain ⟨M, hM⟩ := hbounded
          use M
          rintro _ ⟨y, rfl⟩
          by_cases hy : y ∈ B <;> simp +decide [*, abs_le.mp (hM _)]
          linarith [abs_le.mp (hM x), abs_le.mp (hM y), hh_nonneg x, hh_nonneg y]
        · exact ⟨x, by aesop⟩
      rw [← MeasureTheory.integral_const_mul]
      refine' MeasureTheory.integral_mono_of_nonneg _ _ _
      · exact Filter.Eventually.of_forall fun x => mul_nonneg (hh_nonneg x) (abs_nonneg _)
      · exact MeasureTheory.Integrable.const_mul
          (MeasureTheory.Integrable.abs
            (hf_int.sub hg_int |> MeasureTheory.Integrable.mono_measure <|
              MeasureTheory.Measure.restrict_le_self)) _
      · filter_upwards [MeasureTheory.ae_restrict_mem hBmeas] with x hx using
          mul_le_mul_of_nonneg_right (h_le_sup x hx) (abs_nonneg _)

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
      convert continuous_totalVariationDistance_eq_half_integral_abs
        hf_meas hg_meas hf_int hg_int hf_nonneg hg_nonneg hf_prob hg_prob using 1
      rw [hμ, hν]

theorem prob_8_5 (μ ν : MeasureTheory.Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f g : ℝ → ℝ)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x)
    (hf_int : Integrable f volume) (hg_int : Integrable g volume)
    (hf_prob : ∫ x, f x = 1) (hg_prob : ∫ x, g x = 1)
    (hμpdf : μ = densityMeasure f) (hνpdf : ν = densityMeasure g)
    (h : ℝ → NNReal) (hbounded : ∃ M : ℝ, ∀ x, (h x : ℝ) ≤ M)
    (hmeas : Measurable fun x => (h x : ℝ))
    (B : Set ℝ) (hBmeas : MeasurableSet B) :
    |(∫ x in B, (h x : ℝ) * f x ∂volume) - (∫ x in B, (h x : ℝ) * g x ∂volume)| ≤
    2 * totalVariationDistance μ ν * (⨆ x ∈ B, (h x : ℝ)) := by
  let hR : ℝ → ℝ := fun x => (h x : ℝ)
  have hh_nonneg : ∀ x, 0 ≤ hR x := by
    intro x
    exact NNReal.coe_nonneg (h x)
  have habs_bounded : ∃ M, ∀ x, |hR x| ≤ M := by
    rcases hbounded with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro x
    simpa [hR, abs_of_nonneg (hh_nonneg x)] using hM x
  have step1 := integral_diff_eq f g hR hf_int hg_int habs_bounded hmeas B hBmeas
  have step2 := abs_integral_le_integral_abs f g hR hf_int hg_int habs_bounded hmeas
    hh_nonneg B hBmeas
  have step3 := integral_mul_le_sup_mul f g hR hf_int hg_int hf_meas hg_meas habs_bounded
    hmeas hh_nonneg B hBmeas
  have step4 := integral_abs_restrict_le f g hf_int hg_int hf_nonneg hg_nonneg B hBmeas
  have step5 := tv_eq_half_integral_abs μ ν f g hf_meas hg_meas hf_nonneg hg_nonneg
    hf_int hg_int hf_prob hg_prob hμpdf hνpdf
  calc |(∫ x in B, hR x * f x) - ∫ x in B, hR x * g x|
      = |∫ x in B, hR x * (f x - g x)| := by rw [step1]
    _ ≤ ∫ x in B, hR x * |f x - g x| := step2
    _ ≤ (⨆ x ∈ B, hR x) * ∫ x in B, |f x - g x| := step3
    _ ≤ (⨆ x ∈ B, hR x) * ∫ x, |f x - g x| := by
        apply mul_le_mul_of_nonneg_left step4
        apply Real.iSup_nonneg
        intro x
        apply Real.iSup_nonneg
        intro _
        exact hh_nonneg x
    _ = 2 * totalVariationDistance μ ν * (⨆ x ∈ B, hR x) := by
        rw [step5]
        ring
