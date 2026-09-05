/-
TASK ID: ex_7_2_1
TYPE: Example_Proof
SOURCE PLAN: 26_chap7_fatou_dct
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Filter Set
open scoped ENNReal



noncomputable def fatouIllustrationSeq (n : ℕ) (x : ℝ) : ℝ≥0∞ :=
  (Set.Icc (0 : ℝ) (1 / (n + 1 : ℝ))).indicator (fun _ => ((n + 1 : ℕ) : ℝ≥0∞)) x

 
noncomputable def fatouIllustrationLimit (x : ℝ) : ℝ≥0∞ :=
  ({(0 : ℝ)} : Set ℝ).indicator (fun _ => (∞ : ℝ≥0∞)) x

 
structure FatouLemmaIllustration where
  seq : ℕ → ℝ → ℝ≥0∞
  seq_def : seq = fatouIllustrationSeq
  integral_eq_one : ∀ n, ∫⁻ x, seq n x ∂volume = 1
  eventually_zero_off_zero : ∀ ⦃x : ℝ⦄, x ≠ 0 → ∀ᶠ n in atTop, seq n x = 0
  at_zero_eq : ∀ n, seq n 0 = ((n + 1 : ℕ) : ℝ≥0∞)
  limitProfile : ℝ → ℝ≥0∞
  limitProfile_def : limitProfile = fatouIllustrationLimit
  limitProfile_eq_if : ∀ x, limitProfile x = if x = 0 then (∞ : ℝ≥0∞) else 0
  limitProfile_integral_zero : ∫⁻ x, limitProfile x ∂volume = 0
  pointwise_tendsto : ∀ x, Tendsto (fun n => seq n x) atTop (nhds (limitProfile x))
  pointwise_liminf_eq : ∀ x, liminf (fun n => seq n x) atTop = limitProfile x
  pointwise_limsup_eq : ∀ x, limsup (fun n => seq n x) atTop = limitProfile x
  integral_liminf_eq_one : liminf (fun n => ∫⁻ x, seq n x ∂volume) atTop = 1
  strict_fatou_gap :
    (∫⁻ x, liminf (fun n => seq n x) atTop ∂volume) <
      liminf (fun n => ∫⁻ x, seq n x ∂volume) atTop

theorem fatouIllustrationSeq_integral_eq_one (n : ℕ) :
    ∫⁻ x, fatouIllustrationSeq n x ∂volume = 1 := by
  simp only [fatouIllustrationSeq, lintegral_indicator measurableSet_Icc]
  rw [MeasureTheory.setLIntegral_const]
  have hpos : (0 : ℝ) < n + 1 := by positivity
  have hsucc_ne : (((n + 1 : ℕ) : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have h_inv :
      ENNReal.ofReal (1 / (n + 1 : ℝ)) = (((n + 1 : ℕ) : ℝ≥0∞))⁻¹ := by
    have h_inv0 := ENNReal.ofReal_inv_of_pos hpos
    have h_nat : ENNReal.ofReal (n + 1 : ℝ) = (((n + 1 : ℕ) : ℝ≥0∞)) := by
      simpa using ENNReal.ofReal_natCast (n + 1)
    rw [h_nat] at h_inv0
    simpa [one_div] using h_inv0
  rw [Real.volume_Icc, sub_zero, h_inv]
  simpa using ENNReal.mul_inv_cancel hsucc_ne

theorem fatouIllustrationSeq_eventually_zero_off_zero {x : ℝ} (hx : x ≠ 0) :
    ∀ᶠ n in atTop, fatouIllustrationSeq n x = 0 := by
  by_cases hxneg : x < 0
  · filter_upwards [Filter.Eventually.of_forall fun n => True.intro] with n _
    have hxnot : x ∉ Set.Icc (0 : ℝ) (1 / (n + 1 : ℝ)) := by
      intro hmem
      exact not_lt_of_ge hmem.1 hxneg
    rw [fatouIllustrationSeq, Set.indicator_of_notMem hxnot]
  · have hxpos : 0 < x := lt_of_le_of_ne (le_of_not_gt hxneg) hx.symm
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hxpos
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hle : (1 / (n + 1 : ℝ)) ≤ 1 / (N + 1 : ℝ) := by
      have hsucc : (N + 1 : ℝ) ≤ (n + 1 : ℝ) := by
        exact_mod_cast Nat.succ_le_succ hn
      have hNpos : (0 : ℝ) < N + 1 := by positivity
      exact one_div_le_one_div_of_le hNpos hsucc
    have hxnot : x ∉ Set.Icc (0 : ℝ) (1 / (n + 1 : ℝ)) := by
      intro hmem
      exact not_lt_of_ge hmem.2 (lt_of_le_of_lt hle hN)
    rw [fatouIllustrationSeq, Set.indicator_of_notMem hxnot]

theorem fatouIllustrationSeq_at_zero (n : ℕ) :
    fatouIllustrationSeq n 0 = ((n + 1 : ℕ) : ℝ≥0∞) := by
  have hmem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / (n + 1 : ℝ)) := by
    constructor <;> positivity
  rw [fatouIllustrationSeq, Set.indicator_of_mem hmem]

theorem fatouIllustrationLimit_eq_if (x : ℝ) :
    fatouIllustrationLimit x = if x = 0 then (∞ : ℝ≥0∞) else 0 := by
  by_cases hx : x = 0 <;> simp [fatouIllustrationLimit, hx]

theorem fatouIllustrationLimit_integral_zero :
    ∫⁻ x, fatouIllustrationLimit x ∂volume = 0 := by
  change ∫⁻ x, ({(0 : ℝ)} : Set ℝ).indicator (fun _ => (∞ : ℝ≥0∞)) x ∂volume = 0
  rw [lintegral_indicator (measurableSet_singleton (0 : ℝ))]
  rw [MeasureTheory.setLIntegral_const]
  simp

 
theorem fatouIllustrationSeq_tendsto_limit (x : ℝ) :
    Tendsto (fun n => fatouIllustrationSeq n x) atTop
      (nhds (fatouIllustrationLimit x)) := by
  by_cases hx : x = 0
  · subst x
    have h : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ≥0∞))) atTop (nhds ∞) :=
      ENNReal.tendsto_nat_nhds_top.comp (Filter.tendsto_add_atTop_nat 1)
    simpa [fatouIllustrationSeq_at_zero, fatouIllustrationLimit_eq_if] using h
  · have hzero : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (nhds 0) :=
      tendsto_const_nhds
    have heq :
        (fun n => fatouIllustrationSeq n x) =ᶠ[atTop] (fun _ => (0 : ℝ≥0∞)) :=
      fatouIllustrationSeq_eventually_zero_off_zero hx
    have hseq : Tendsto (fun n => fatouIllustrationSeq n x) atTop (nhds 0) :=
      Filter.Tendsto.congr' heq.symm hzero
    simpa [fatouIllustrationLimit_eq_if, hx] using hseq

 
theorem fatouIllustrationSeq_liminf_eq (x : ℝ) :
    liminf (fun n => fatouIllustrationSeq n x) atTop = fatouIllustrationLimit x :=
  (fatouIllustrationSeq_tendsto_limit x).liminf_eq

 
theorem fatouIllustrationSeq_limsup_eq (x : ℝ) :
    limsup (fun n => fatouIllustrationSeq n x) atTop = fatouIllustrationLimit x :=
  (fatouIllustrationSeq_tendsto_limit x).limsup_eq

 
theorem fatouIllustrationSeq_integral_liminf_eq_one :
    liminf (fun n => ∫⁻ x, fatouIllustrationSeq n x ∂volume) atTop = 1 := by
  simp only [fatouIllustrationSeq_integral_eq_one, Filter.liminf_const]

 
theorem fatouIllustration_strict_fatou_gap :
    (∫⁻ x, liminf (fun n => fatouIllustrationSeq n x) atTop ∂volume) <
      liminf (fun n => ∫⁻ x, fatouIllustrationSeq n x ∂volume) atTop := by
  simp_rw [fatouIllustrationSeq_liminf_eq]
  rw [fatouIllustrationLimit_integral_zero, fatouIllustrationSeq_integral_liminf_eq_one]
  exact zero_lt_one

 
noncomputable def ex_7_2_1 : FatouLemmaIllustration where
  seq := fatouIllustrationSeq
  seq_def := rfl
  integral_eq_one := fatouIllustrationSeq_integral_eq_one
  eventually_zero_off_zero := fun {x} hx =>
    fatouIllustrationSeq_eventually_zero_off_zero (x := x) hx
  at_zero_eq := fatouIllustrationSeq_at_zero
  limitProfile := fatouIllustrationLimit
  limitProfile_def := rfl
  limitProfile_eq_if := fatouIllustrationLimit_eq_if
  limitProfile_integral_zero := fatouIllustrationLimit_integral_zero
  pointwise_tendsto := fatouIllustrationSeq_tendsto_limit
  pointwise_liminf_eq := fatouIllustrationSeq_liminf_eq
  pointwise_limsup_eq := fatouIllustrationSeq_limsup_eq
  integral_liminf_eq_one := fatouIllustrationSeq_integral_liminf_eq_one
  strict_fatou_gap := fatouIllustration_strict_fatou_gap
