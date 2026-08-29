/-
TASK ID: prob_7_1
TYPE: Problem
SOURCE PLAN: 30_chap7_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set Filter Classical Measure

noncomputable section

noncomputable def ofCdf (F : StieltjesFunction ℝ)
    (hF0 : Tendsto F atBot (nhds 0))
    (hF1 : Tendsto F atTop (nhds 1)) : ProbabilityMeasure ℝ :=
  ⟨F.measure, by
    constructor
    rw [F.measure_univ hF0 hF1]
    norm_num⟩

noncomputable def mean (μ : ProbabilityMeasure ℝ)
    (_hμ : Integrable (fun x : ℝ => x) (μ : Measure ℝ)) : ℝ :=
  ∫ x, x ∂(μ : Measure ℝ)

noncomputable def variance (μ : ProbabilityMeasure ℝ)
    (_hμ1 : Integrable (fun x : ℝ => x) (μ : Measure ℝ))
    (_hμ2 : Integrable (fun x : ℝ => x ^ 2) (μ : Measure ℝ)) : ℝ :=
  ∫ x, x ^ 2 ∂(μ : Measure ℝ) -
    (∫ x, x ∂(μ : Measure ℝ)) ^ 2

def F_cdf : ℝ → ℝ := fun x =>
  if x < 0 then 0 else if x < 1 then x / 3 else if x < 2 then 2 / 3 else 1

theorem F_cdf_mono : Monotone F_cdf := by
  intro a b hab
  simp only [F_cdf]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 <;> linarith

def F_sf : StieltjesFunction ℝ := F_cdf_mono.stieltjesFunction
private def μ_F : Measure ℝ := F_sf.measure

private lemma F_cdf_rightContinuous (x : ℝ) :
    Tendsto F_cdf (nhdsWithin x (Ioi x)) (nhds (F_cdf x)) := by
  unfold F_cdf
  by_cases hx0 : x < 0 <;> by_cases hx1 : x < 1 <;> by_cases hx2 : x < 2 <;>
    norm_num [hx0, hx1, hx2]
  any_goals linarith
  · exact tendsto_const_nhds.congr'
      (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsGT_of_mem ⟨le_rfl, hx0⟩)
        fun y hy => by aesop)
  · refine' Filter.Tendsto.congr' _ _
    exacts [
      fun y => y / 3,
      Filter.eventuallyEq_of_mem (Ioo_mem_nhdsGT_of_mem ⟨le_rfl, hx1⟩)
        fun y hy => by split_ifs <;> linarith [hy.1, hy.2],
      Filter.Tendsto.div_const (Filter.tendsto_id.mono_left inf_le_left) _]
  · exact tendsto_const_nhds.congr'
      (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsGT_of_mem ⟨le_rfl, hx2⟩)
        fun y hy => by split_ifs <;> linarith [hy.1, hy.2])
  · exact tendsto_const_nhds.congr'
      (Filter.eventuallyEq_of_mem self_mem_nhdsWithin
        fun y hy => by split_ifs <;> linarith [hy.out])

theorem F_sf_eq_F_cdf : (F_sf : ℝ → ℝ) = F_cdf := by
  ext x
  simp only [F_sf, Monotone.stieltjesFunction_eq]
  exact tendsto_nhds_unique (F_cdf_mono.tendsto_rightLim x) (F_cdf_rightContinuous x)

theorem F_sf_tendsto_atBot :
    Tendsto F_sf atBot (nhds 0) := by
  rw [F_sf_eq_F_cdf]
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
  simp [F_cdf, hx]

theorem F_sf_tendsto_atTop :
    Tendsto F_sf atTop (nhds 1) := by
  rw [F_sf_eq_F_cdf]
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hx0 : ¬x < 0 := by linarith
  have hx1 : ¬x < 1 := by linarith
  have hx2 : ¬x < 2 := by linarith
  simp [F_cdf, hx0, hx1, hx2]

noncomputable def prob_7_1_law : ProbabilityMeasure ℝ :=
  ofCdf F_sf F_sf_tendsto_atBot F_sf_tendsto_atTop

private lemma prob_7_1_law_toMeasure :
    (prob_7_1_law : Measure ℝ) = μ_F := by
  rfl

private def μ_explicit : Measure ℝ :=
  (ENNReal.ofReal (1 / 3)) • volume.restrict (Ioo 0 1) +
    (ENNReal.ofReal (1 / 3)) • Measure.dirac 1 +
    (ENNReal.ofReal (1 / 3)) • Measure.dirac 2

private lemma F_cdf_diff_eq (a b : ℝ) (hab : a < b) :
    F_cdf b - F_cdf a =
      (min b 1 - max a 0) / 3 * (if max a 0 < min b 1 then 1 else 0) +
        (1 / 3) * (if a < 1 ∧ 1 ≤ b then 1 else 0) +
        (1 / 3) * (if a < 2 ∧ 2 ≤ b then 1 else 0) := by
  unfold F_cdf
  grind

private lemma μ_explicit_Ioc (a b : ℝ) (hab : a < b) :
    μ_explicit (Ioc a b) =
      ENNReal.ofReal ((min b 1 - max a 0) / 3 *
        (if max a 0 < min b 1 then 1 else 0)) +
      ENNReal.ofReal ((1 / 3) * (if a < 1 ∧ 1 ≤ b then 1 else 0)) +
      ENNReal.ofReal ((1 / 3) * (if a < 2 ∧ 2 ≤ b then 1 else 0)) := by
  unfold μ_explicit
  split_ifs <;> simp_all +decide [Set.indicator]
  any_goals linarith
  · rw [show Ioc a b ∩ Ioo 0 1 = Set.Ioc (Max.max a 0) 1 \ {1} from ?_,
      MeasureTheory.measure_diff_null] <;> norm_num
    · rw [ENNReal.ofReal_div_of_pos] <;> norm_num
      rw [ENNReal.div_eq_inv_mul]
    · grind
  · rw [show (Ioc a b ∩ Ioo 0 1 : Set ℝ) = Set.Ioc (Max.max a 0) 1 \ {1} from ?_,
      MeasureTheory.measure_diff_null] <;> norm_num
    · rw [if_neg (by intros h; linarith [‹a < 2 → b < 2› (by linarith)])]
      rw [ENNReal.ofReal_div_of_pos] <;> norm_num
      ring
      rw [ENNReal.div_eq_inv_mul]
    · grind
  · rw [show (Ioc a b ∩ Ioo 0 1 : Set ℝ) = Set.Ioc (Max.max a 0) (Min.min b 1) from ?_,
      Real.volume_Ioc]
    · rw [if_neg (by linarith), if_neg (by intros h; linarith)]
      rw [ENNReal.ofReal_div_of_pos] <;> norm_num
      ring
      rw [ENNReal.div_eq_inv_mul]
    · grind +extAll
  · rw [show Ioc a b ∩ Ioo 0 1 = ∅ by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨hx₁, hx₂⟩
      linarith [hx₁.1, hx₁.2, hx₂.1, hx₂.2, ‹0 < b → 1 ≤ a› (by linarith)]]
    norm_num
  · rw [show Ioc a b ∩ Ioo 0 1 = ∅ by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨hx₁, hx₂⟩
      linarith [hx₁.1, hx₁.2, hx₂.1, hx₂.2,
        ‹0 < b → 1 ≤ a› (by linarith [hx₁.1, hx₁.2, hx₂.1, hx₂.2])]]
    norm_num

private lemma μ_F_eq_μ_explicit : μ_F = μ_explicit := by
  apply MeasureTheory.Measure.ext_of_Ioc'
  · exact fun a b _hab => ne_of_lt (by
      simpa [μ_F, F_sf] using
        (measure_Ioc_lt_top
          (μ := F_cdf_mono.stieltjesFunction.measure) (a := a) (b := b)))
  · intro a b hab
    convert congr_arg ENNReal.ofReal (F_cdf_diff_eq a b hab) using 1
    · convert F_sf.measure_Ioc a b using 1
      · rfl
      · rw [F_sf_eq_F_cdf]
    · convert μ_explicit_Ioc a b hab using 1
      rw [← ENNReal.ofReal_add, ← ENNReal.ofReal_add] <;> split_ifs <;> norm_num
      · linarith
      · linarith
      · linarith

private lemma prob_7_1_law_toMeasure_eq_explicit :
    (prob_7_1_law : Measure ℝ) = μ_explicit := by
  exact prob_7_1_law_toMeasure.trans μ_F_eq_μ_explicit

theorem prob_7_1_integrable_id :
    Integrable (fun x : ℝ => x)
      (prob_7_1_law : Measure ℝ) := by
  rw [prob_7_1_law_toMeasure_eq_explicit, μ_explicit,
    integrable_add_measure, integrable_add_measure]
  constructor
  · constructor
    · rw [integrable_smul_measure] <;> norm_num
      exact
        continuous_id.integrableOn_Icc.mono_set
          Ioo_subset_Icc_self
    · rw [integrable_smul_measure] <;> norm_num
      exact integrable_dirac (by norm_num)
  · rw [integrable_smul_measure] <;> norm_num
    exact integrable_dirac (by norm_num)

theorem prob_7_1_integrable_sq :
    Integrable (fun x : ℝ => x ^ 2)
      (prob_7_1_law : Measure ℝ) := by
  rw [prob_7_1_law_toMeasure_eq_explicit, μ_explicit,
    integrable_add_measure, integrable_add_measure]
  constructor
  · constructor
    · rw [integrable_smul_measure] <;> norm_num
      exact
        (Continuous.integrableOn_Icc (by continuity)).mono_set
          Ioo_subset_Icc_self
    · rw [integrable_smul_measure] <;> norm_num
      exact integrable_dirac (by norm_num)
  · rw [integrable_smul_measure] <;> norm_num
    exact integrable_dirac (by norm_num)

private lemma mean_val :
    mean prob_7_1_law prob_7_1_integrable_id = (7 : ℝ) / 6 := by
  unfold mean
  rw [prob_7_1_law_toMeasure_eq_explicit, μ_explicit]
  rw [integral_add_measure, integral_add_measure] <;> norm_num
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le] <;> norm_num
  · rw [integrable_smul_measure] <;> norm_num
    exact (continuous_id.integrableOn_Icc.mono_set <| Ioo_subset_Icc_self)
  · norm_num [integrable_smul_measure]
    norm_num [integrable_dirac]
  · constructor <;> norm_num [integrable_smul_measure]
    · exact (continuous_id.integrableOn_Icc.mono_set <| Ioo_subset_Icc_self)
    · norm_num [integrable_dirac]
  · norm_num [integrable_smul_measure]
    norm_num [integrable_dirac]

private lemma moment2_val :
    ∫ x : ℝ, x ^ 2 ∂(prob_7_1_law : Measure ℝ) = (16 : ℝ) / 9 := by
  rw [prob_7_1_law_toMeasure_eq_explicit, μ_explicit]
  rw [integral_add_measure, integral_add_measure] <;> norm_num
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le] <;> norm_num
  · rw [integrable_smul_measure] <;> norm_num
    exact Continuous.integrableOn_Icc (by continuity) |>.mono_set <| Ioo_subset_Icc_self
  · rw [integrable_smul_measure] <;> norm_num
    norm_num [integrable_dirac]
  · constructor <;> norm_num [integrable_smul_measure]
    · exact Continuous.integrableOn_Icc (by continuity) |>.mono_set <| Ioo_subset_Icc_self
    · norm_num [integrable_dirac]
  · norm_num [integrable_smul_measure]
    norm_num [integrable_dirac]

private lemma variance_val :
    variance prob_7_1_law prob_7_1_integrable_id prob_7_1_integrable_sq =
      (5 : ℝ) / 12 := by
  unfold variance
  have hmean :
      (∫ x, x ∂(prob_7_1_law : Measure ℝ)) = (7 : ℝ) / 6 := by
    simpa [mean] using mean_val
  rw [hmean, moment2_val]
  norm_num

theorem prob_7_1 :
    mean prob_7_1_law prob_7_1_integrable_id = (7 / 6 : ℝ) ∧
    variance prob_7_1_law prob_7_1_integrable_id
      prob_7_1_integrable_sq = (5 / 12 : ℝ) := by
  exact ⟨mean_val, variance_val⟩
