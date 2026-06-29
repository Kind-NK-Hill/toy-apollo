import Mathlib

/-
TASK ID: prob_7_1
TYPE: Problem
SOURCE PLAN: 30_chap7_problems
TASK CONTENT:
\textbf{7.1.} Compute the mean and variance of the random variable specified by cdf
\[
F(x)=
\begin{cases}
0 & \text{if } x<0,\\
x/3 & \text{if } 0\le x<1,\\
2/3 & \text{if } 1\le x<2,\\
1 & \text{if } 2\le x.
\end{cases}
\]
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set Filter Classical Measure

noncomputable section

noncomputable def ofCdf (F : ℝ → ℝ) : Measure ℝ :=
  if h : Monotone F then h.stieltjesFunction.measure else 0

noncomputable def mean (μ : Measure ℝ) : ℝ := ∫ x, x ∂μ

noncomputable def variance (μ : Measure ℝ) : ℝ :=
  ∫ x, x ^ 2 ∂μ - (∫ x, x ∂μ) ^ 2

private def F_cdf : ℝ → ℝ := fun x =>
  if x < 0 then 0 else if x < 1 then x / 3 else if x < 2 then 2 / 3 else 1

private lemma F_cdf_mono : Monotone F_cdf := by
  intro a b hab
  simp only [F_cdf]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 <;> linarith

private def F_sf : StieltjesFunction ℝ := F_cdf_mono.stieltjesFunction
private def μ_F : Measure ℝ := F_sf.measure

private lemma ofCdf_eq_μ_F :
    ofCdf (fun x => if x < 0 then 0 else if x < 1 then x / 3 else
      if x < 2 then 2 / 3 else 1) = μ_F := by
  simp only [ofCdf, μ_F, F_sf]
  have : Monotone
      (fun x : ℝ => if x < 0 then (0 : ℝ) else if x < 1 then x / 3 else
        if x < 2 then 2 / 3 else 1) := F_cdf_mono
  rw [dif_pos this]
  have hmono : this = F_cdf_mono := by
    apply Subsingleton.elim
  cases hmono
  rfl

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

private lemma F_sf_eq_F_cdf : (F_sf : ℝ → ℝ) = F_cdf := by
  ext x
  simp only [F_sf, Monotone.stieltjesFunction_eq]
  exact tendsto_nhds_unique (F_cdf_mono.tendsto_rightLim x) (F_cdf_rightContinuous x)

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
      rw [F_sf_eq_F_cdf]
    · convert μ_explicit_Ioc a b hab using 1
      rw [← ENNReal.ofReal_add, ← ENNReal.ofReal_add] <;> split_ifs <;> norm_num
      · linarith
      · linarith
      · linarith

private lemma mean_val : mean μ_F = (7 : ℝ) / 6 := by
  unfold mean
  rw [μ_F_eq_μ_explicit, μ_explicit]
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

private lemma moment2_val : ∫ x : ℝ, x ^ 2 ∂μ_F = (16 : ℝ) / 9 := by
  rw [μ_F_eq_μ_explicit, μ_explicit]
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

private lemma variance_val : variance μ_F = (5 : ℝ) / 12 := by
  unfold variance
  rw [show ∫ x, x ∂μ_F = (7 : ℝ) / 6 from by rw [← mean]; exact mean_val]
  rw [moment2_val]
  norm_num

theorem prob_7_1 :
    mean (ofCdf (fun x => if x < 0 then 0 else if x < 1 then x / 3 else
      if x < 2 then 2 / 3 else 1)) = (7 / 6 : ℝ) ∧
    variance (ofCdf (fun x => if x < 0 then 0 else if x < 1 then x / 3 else
      if x < 2 then 2 / 3 else 1)) = (5 / 12 : ℝ) := by
  rw [ofCdf_eq_μ_F]
  exact ⟨mean_val, variance_val⟩
