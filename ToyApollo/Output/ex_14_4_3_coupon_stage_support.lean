/-
TASK ID: ex_14_4_3_coupon_stage_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.prob_6_3
import ToyApollo.Output.chapter14_coupon_geometric_support
import ToyApollo.Output.thm_14_7
import ToyApollo.Output.thm_14_8

open Filter MeasureTheory
open scoped Topology BigOperators

noncomputable section

def ex_14_4_3_couponTypes (n : ℕ) : ℕ :=
  n + 2

def ex_14_4_3_targetDistinct (n : ℕ) : ℕ :=
  (ex_14_4_3_couponTypes n + 1) / 2

def ex_14_4_3_successProbability
    (n : ℕ) (i : Fin (ex_14_4_3_targetDistinct n)) : ℝ :=
  Prob63Support.stageSuccessProb (ex_14_4_3_couponTypes n) i

lemma ex_14_4_3_targetDistinct_pos (n : ℕ) :
    1 ≤ ex_14_4_3_targetDistinct n := by
  unfold ex_14_4_3_targetDistinct ex_14_4_3_couponTypes
  omega

lemma ex_14_4_3_targetDistinct_le_couponTypes (n : ℕ) :
    ex_14_4_3_targetDistinct n ≤ ex_14_4_3_couponTypes n := by
  unfold ex_14_4_3_targetDistinct ex_14_4_3_couponTypes
  omega

theorem ex_14_4_3_half_coupon_success_probability_bounds
    (n : ℕ) (i : Fin (ex_14_4_3_targetDistinct n)) :
    (1 / 2 : ℝ) ≤ ex_14_4_3_successProbability n i ∧
      ex_14_4_3_successProbability n i ≤ 1 := by
  constructor
  · unfold ex_14_4_3_successProbability Prob63Support.stageSuccessProb
      ex_14_4_3_couponTypes
    have htwice : 2 * i.1 ≤ n + 2 := by
      have hi : i.1 < (n + 2 + 1) / 2 := by
        simpa [ex_14_4_3_targetDistinct, ex_14_4_3_couponTypes] using i.2
      omega
    have hsub : n + 2 ≤ 2 * (n + 2 - i.1) := by
      omega
    have hsub_real : ((n + 2 : ℕ) : ℝ) ≤ 2 * ((n + 2 - i.1 : ℕ) : ℝ) := by
      exact_mod_cast hsub
    have hden : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hden]
    linarith
  · unfold ex_14_4_3_successProbability Prob63Support.stageSuccessProb
      ex_14_4_3_couponTypes
    have hsub : ((n + 2 - i.1 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le (n + 2) i.1
    have hden : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hden]
    exact hsub

def ex_14_4_3_geometricMgf (p t : ℝ) : ℝ :=
  chapter14_geometricMgf p t

theorem ex_14_4_3_geometric_mgf_hasSum
    {p t : ℝ} (ht : ‖(1 - p) * Real.exp t‖ < 1) :
    HasSum
      (fun m : ℕ =>
        ProbabilityTheory.geometricPMFReal p m *
          Real.exp (t * Prob63Support.scalarStageWait m))
      (ex_14_4_3_geometricMgf p t) := by
  simpa [ex_14_4_3_geometricMgf] using
    chapter14_geometric_mgf_hasSum (p := p) (t := t) ht

def ex_14_4_3_geometricMean (p : ℝ) : ℝ :=
  chapter14_geometricMean p

def ex_14_4_3_geometricVariance (p : ℝ) : ℝ :=
  chapter14_geometricVariance p

def ex_14_4_3_stageProbabilityMeasure
    (n : ℕ) (i : Fin (ex_14_4_3_targetDistinct n)) : ProbabilityMeasure ℕ :=
  ⟨Prob63Support.stageMeasure (ex_14_4_3_couponTypes n)
      (ex_14_4_3_targetDistinct n)
      (ex_14_4_3_targetDistinct_pos n)
      (ex_14_4_3_targetDistinct_le_couponTypes n) i,
    by
      simpa [Prob63Support.stageMeasure, Prob63Support.stagePMF] using
        (ProbabilityTheory.isProbabilityMeasure_geometricMeasure
          (p := Prob63Support.stageSuccessProb
            (ex_14_4_3_couponTypes n) i)
          (Prob63Support.stageSuccessProb_pos
            (ex_14_4_3_targetDistinct_pos n)
            (ex_14_4_3_targetDistinct_le_couponTypes n) i)
          (Prob63Support.stageSuccessProb_le_one
            (ex_14_4_3_targetDistinct_pos n)
            (ex_14_4_3_targetDistinct_le_couponTypes n) i))⟩

def ex_14_4_3_centeredStageValue
    (n : ℕ) (i : Fin (ex_14_4_3_targetDistinct n)) (m : ℕ) : ℝ :=
  Prob63Support.scalarStageWait m -
    ex_14_4_3_geometricMean (ex_14_4_3_successProbability n i)

def ex_14_4_3_centeredCouponStageLaw
    (n : ℕ) (i : Fin (ex_14_4_3_targetDistinct n)) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map (ex_14_4_3_stageProbabilityMeasure n i)
    ((measurable_of_countable (ex_14_4_3_centeredStageValue n i)).aemeasurable)

theorem ex_14_4_3_geometricVariance_ge_index_ratio
    (n : ℕ) (i : Fin (ex_14_4_3_targetDistinct n)) :
    ((i.1 : ℝ) / (ex_14_4_3_couponTypes n : ℝ)) ≤
      ex_14_4_3_geometricVariance
        (ex_14_4_3_successProbability n i) := by
  have hp_pos : 0 < ex_14_4_3_successProbability n i := by
    unfold ex_14_4_3_successProbability
    apply Prob63Support.stageSuccessProb_pos
    · unfold ex_14_4_3_targetDistinct ex_14_4_3_couponTypes
      omega
    · unfold ex_14_4_3_targetDistinct ex_14_4_3_couponTypes
      omega
  have hp_le : ex_14_4_3_successProbability n i ≤ 1 := by
    unfold ex_14_4_3_successProbability
    apply Prob63Support.stageSuccessProb_le_one
    · unfold ex_14_4_3_targetDistinct ex_14_4_3_couponTypes
      omega
    · unfold ex_14_4_3_targetDistinct ex_14_4_3_couponTypes
      omega
  have htarget :
      ex_14_4_3_targetDistinct n ≤ ex_14_4_3_couponTypes n := by
    unfold ex_14_4_3_targetDistinct ex_14_4_3_couponTypes
    omega
  have hi_lt : i.1 < ex_14_4_3_couponTypes n := lt_of_lt_of_le i.2 htarget
  have hi_le_nat : i.1 ≤ ex_14_4_3_couponTypes n := Nat.le_of_lt hi_lt
  have hNpos : (0 : ℝ) < (ex_14_4_3_couponTypes n : ℕ) := by
    unfold ex_14_4_3_couponTypes
    positivity
  have hNne : ((ex_14_4_3_couponTypes n : ℕ) : ℝ) ≠ 0 := ne_of_gt hNpos
  have hsub_cast :
      (((ex_14_4_3_couponTypes n - i.1 : ℕ) : ℝ) =
        ((ex_14_4_3_couponTypes n : ℕ) : ℝ) - (i.1 : ℝ)) := by
    exact Nat.cast_sub hi_le_nat
  have hone_minus :
      1 - ex_14_4_3_successProbability n i =
        (i.1 : ℝ) / (ex_14_4_3_couponTypes n : ℝ) := by
    unfold ex_14_4_3_successProbability Prob63Support.stageSuccessProb
    rw [hsub_cast]
    field_simp [hNne]
    ring
  have hgap_nonneg : 0 ≤ 1 - ex_14_4_3_successProbability n i := by
    linarith
  have hp_sq_pos : 0 < ex_14_4_3_successProbability n i ^ 2 :=
    sq_pos_of_ne_zero hp_pos.ne'
  have hp_sq_le_one : ex_14_4_3_successProbability n i ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (ex_14_4_3_successProbability n i - 1), hp_pos, hp_le]
  have hinv_sq_ge_one : 1 ≤ 1 / ex_14_4_3_successProbability n i ^ 2 := by
    rw [le_div_iff₀ hp_sq_pos]
    nlinarith
  calc
    ((i.1 : ℝ) / (ex_14_4_3_couponTypes n : ℝ))
        = 1 - ex_14_4_3_successProbability n i := hone_minus.symm
    _ ≤ (1 - ex_14_4_3_successProbability n i) *
          (1 / ex_14_4_3_successProbability n i ^ 2) := by
        exact le_mul_of_one_le_right hgap_nonneg hinv_sq_ge_one
    _ = ex_14_4_3_geometricVariance
          (ex_14_4_3_successProbability n i) := by
        unfold ex_14_4_3_geometricVariance chapter14_geometricVariance
        ring_nf

theorem ex_14_4_3_geometricVariance_row_sum_ge_index_sum (n : ℕ) :
    (∑ i : Fin (ex_14_4_3_targetDistinct n),
      ((i.1 : ℝ) / (ex_14_4_3_couponTypes n : ℝ))) ≤
      ∑ i : Fin (ex_14_4_3_targetDistinct n),
        ex_14_4_3_geometricVariance
          (ex_14_4_3_successProbability n i) := by
  exact Finset.sum_le_sum
    (fun i _ => ex_14_4_3_geometricVariance_ge_index_ratio n i)

theorem ex_14_4_3_index_ratio_sum_linear_lower_bound :
    ∀ᶠ n : ℕ in atTop,
      (ex_14_4_3_couponTypes n : ℝ) / 64 ≤
        ∑ i : Fin (ex_14_4_3_targetDistinct n),
          ((i.1 : ℝ) / (ex_14_4_3_couponTypes n : ℝ)) := by
  filter_upwards [eventually_ge_atTop 6] with n hn
  let N : ℕ := ex_14_4_3_couponTypes n
  let m : ℕ := ex_14_4_3_targetDistinct n
  have hN_pos_nat : 0 < N := by
    simp [N, ex_14_4_3_couponTypes]
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos_nat
  have hN_ge_four : 4 ≤ N := by
    simp [N, ex_14_4_3_couponTypes]
    omega
  have hN_ge_eight : 8 ≤ N := by
    simp [N, ex_14_4_3_couponTypes]
    omega
  have hm_def : m = (N + 1) / 2 := by
    simp [m, N, ex_14_4_3_targetDistinct, ex_14_4_3_couponTypes]
  have hm_ge_half_nat : N ≤ 2 * m := by
    rw [hm_def]
    omega
  have hm_sub_ge_quarter_nat : N ≤ 4 * (m - 1) := by
    rw [hm_def]
    omega
  have hsum_fin :
      (∑ i : Fin m, (i.1 : ℝ)) =
        ((m * (m - 1) / 2 : ℕ) : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range]
    rw [← Nat.cast_sum]
    exact_mod_cast Finset.sum_range_id m
  have hsum_div :
      (∑ i : Fin m, ((i.1 : ℝ) / (N : ℝ))) =
        (∑ i : Fin m, (i.1 : ℝ)) / (N : ℝ) := by
    rw [Finset.sum_div]
  have hm_half_real : (N : ℝ) / 2 ≤ (m : ℝ) := by
    nlinarith [show (N : ℝ) ≤ 2 * (m : ℝ) by exact_mod_cast hm_ge_half_nat]
  have hm_sub_quarter_real : (N : ℝ) / 4 ≤ ((m - 1 : ℕ) : ℝ) := by
    nlinarith [show (N : ℝ) ≤ 4 * ((m - 1 : ℕ) : ℝ) by
      exact_mod_cast hm_sub_ge_quarter_nat]
  have hprod_lower :
      ((N : ℝ) * (N : ℝ)) / 16 ≤
        ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) / 2 := by
    have hmul := mul_le_mul hm_half_real hm_sub_quarter_real
      (by positivity : 0 ≤ (N : ℝ) / 4)
      (by positivity : 0 ≤ (m : ℝ))
    nlinarith
  have hfloor_lower :
      ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) / 2 - 1 ≤
        ((m * (m - 1) / 2 : ℕ) : ℝ) := by
    have hmod : m * (m - 1) < 2 * ((m * (m - 1)) / 2 + 1) := by
      omega
    have hcast :
        (m : ℝ) * ((m - 1 : ℕ) : ℝ) <
          2 * (((m * (m - 1) / 2 : ℕ) : ℝ) + 1) := by
      exact_mod_cast hmod
    nlinarith
  have hlarge :
      (1 : ℝ) ≤ ((N : ℝ) * (N : ℝ)) / 64 := by
    nlinarith [show (8 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN_ge_eight]
  have hnat_div_lower :
      ((N : ℝ) * (N : ℝ)) / 64 ≤
        ((m * (m - 1) / 2 : ℕ) : ℝ) := by
    nlinarith
  have hmain :
      (N : ℝ) / 64 ≤
        ((m * (m - 1) / 2 : ℕ) : ℝ) / (N : ℝ) := by
    have hdiv := div_le_div_of_nonneg_right hnat_div_lower (le_of_lt hN_pos)
    have hleft :
        (((N : ℝ) * (N : ℝ)) / 64) / (N : ℝ) = (N : ℝ) / 64 := by
      field_simp [ne_of_gt hN_pos]
    nlinarith
  simpa [N, m, hsum_div, hsum_fin] using hmain

def ex_14_4_3_geometricCenteredFourthMoment (p : ℝ) : ℝ :=
  chapter14_geometricCenteredFourthMoment p

lemma ex_14_4_3_choose_add_two_cast (m : ℕ) :
    (((m + 2).choose 2 : ℕ) : ℝ) =
      ((m : ℝ) + 1) * ((m : ℝ) + 2) / 2 :=
  chapter14_choose_add_two_cast m

lemma ex_14_4_3_centeredSecond_term_choose_expansion
    {p r : ℝ} (hp : p ≠ 0) (m : ℕ) :
    ((m : ℝ) + 1 - 1 / p) ^ 2 * p * r ^ m =
      (((2 * p) * (((m + 2).choose 2 : ℕ) : ℝ)
        + (-(p + 2)) * (((m + 1).choose 1 : ℕ) : ℝ)
        + (1 / p)) * r ^ m) :=
  chapter14_geometric_centeredSecond_term_choose_expansion hp m

theorem ex_14_4_3_geometric_centered_second_hasSum
    {p : ℝ} (hp_pos : 0 < p) (hp_le : p ≤ 1) :
    HasSum
      (fun m : ℕ =>
        (((m : ℝ) + 1 - 1 / p) ^ 2) *
          ProbabilityTheory.geometricPMFReal p m)
      (ex_14_4_3_geometricVariance p) := by
  simpa [ex_14_4_3_geometricVariance] using
    chapter14_geometric_centered_second_hasSum hp_pos hp_le

theorem ex_14_4_3_geometric_centered_second_tsum_eq
    {p : ℝ} (hp_pos : 0 < p) (hp_le : p ≤ 1) :
    (∑' m : ℕ,
      (Prob63Support.scalarStageWait m - 1 / p) ^ 2 *
        ProbabilityTheory.geometricPMFReal p m) =
      ex_14_4_3_geometricVariance p := by
  simpa [ex_14_4_3_geometricVariance] using
    chapter14_geometric_centered_second_tsum_eq hp_pos hp_le

lemma ex_14_4_3_choose_add_three_cast (m : ℕ) :
    (((m + 3).choose 3 : ℕ) : ℝ) =
      ((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) / 6 :=
  chapter14_choose_add_three_cast m

lemma ex_14_4_3_choose_add_four_cast (m : ℕ) :
    (((m + 4).choose 4 : ℕ) : ℝ) =
      ((m : ℝ) + 1) * ((m : ℝ) + 2) *
        ((m : ℝ) + 3) * ((m : ℝ) + 4) / 24 :=
  chapter14_choose_add_four_cast m

lemma ex_14_4_3_centeredFourth_term_choose_expansion
    {p r : ℝ} (hp : p ≠ 0) (m : ℕ) :
    ((m : ℝ) + 1 - 1 / p) ^ 4 * p * r ^ m =
      (((24 * p) * (((m + 4).choose 4 : ℕ) : ℝ)
        + (-(36 * p + 24)) * (((m + 3).choose 3 : ℕ) : ℝ)
        + (14 * p + 24 + 12 / p) * (((m + 2).choose 2 : ℕ) : ℝ)
        + (-(p + 4 + 6 / p + 4 / p ^ 2)) *
            (((m + 1).choose 1 : ℕ) : ℝ)
        + (1 / p ^ 3)) * r ^ m) :=
  chapter14_geometric_centeredFourth_term_choose_expansion hp m

theorem ex_14_4_3_geometric_centered_fourth_hasSum
    {p : ℝ} (hp_pos : 0 < p) (hp_le : p ≤ 1) :
    HasSum
      (fun m : ℕ =>
        (((m : ℝ) + 1 - 1 / p) ^ 4) *
          ProbabilityTheory.geometricPMFReal p m)
      (ex_14_4_3_geometricCenteredFourthMoment p) := by
  simpa [ex_14_4_3_geometricCenteredFourthMoment] using
    chapter14_geometric_centered_fourth_hasSum hp_pos hp_le

theorem ex_14_4_3_geometric_centered_fourth_tsum_eq
    {p : ℝ} (hp_pos : 0 < p) (hp_le : p ≤ 1) :
    (∑' m : ℕ,
      (Prob63Support.scalarStageWait m - 1 / p) ^ 4 *
        ProbabilityTheory.geometricPMFReal p m) =
      ex_14_4_3_geometricCenteredFourthMoment p := by
  simpa [ex_14_4_3_geometricCenteredFourthMoment] using
    chapter14_geometric_centered_fourth_tsum_eq hp_pos hp_le

lemma ex_14_4_3_stageMgfSummableNorm
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) {t : ℝ}
    (ht : ‖(1 - Prob63Support.stageSuccessProb n i) * Real.exp t‖ < 1) :
    Summable
      (fun m : ℕ =>
        (Prob63Support.stageMeasure n k hk hkn i {m}).toReal *
          ‖Real.exp (t * Prob63Support.scalarStageWait m)‖) :=
  chapter14_couponStageMgfSummableNorm hk hkn i ht

lemma ex_14_4_3_stageMgfIntegrable
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) {t : ℝ}
    (ht : ‖(1 - Prob63Support.stageSuccessProb n i) * Real.exp t‖ < 1) :
    Integrable
      (fun m : ℕ => Real.exp (t * Prob63Support.scalarStageWait m))
      (Prob63Support.stageMeasure n k hk hkn i) :=
  chapter14_couponStageMgfIntegrable hk hkn i ht

theorem ex_14_4_3_stageMeasure_mgf_eq
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) {t : ℝ}
    (ht : ‖(1 - Prob63Support.stageSuccessProb n i) * Real.exp t‖ < 1) :
    ProbabilityTheory.mgf Prob63Support.scalarStageWait
      (Prob63Support.stageMeasure n k hk hkn i) t =
      Prob63Support.stageSuccessProb n i * Real.exp t /
        (1 - (1 - Prob63Support.stageSuccessProb n i) * Real.exp t) :=
  chapter14_couponStageMeasure_mgf_eq hk hkn i ht

lemma ex_14_4_3_stageCenteredSecondSummableNorm
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    Summable
      (fun m : ℕ =>
        (Prob63Support.stageMeasure n k hk hkn i {m}).toReal *
          ‖(Prob63Support.scalarStageWait m -
              1 / Prob63Support.stageSuccessProb n i) ^ 2‖) :=
  chapter14_couponStageCenteredSecondSummableNorm hk hkn i

lemma ex_14_4_3_stageCenteredSecondIntegrable
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    Integrable
      (fun m : ℕ =>
        (Prob63Support.scalarStageWait m -
          1 / Prob63Support.stageSuccessProb n i) ^ 2)
      (Prob63Support.stageMeasure n k hk hkn i) :=
  chapter14_couponStageCenteredSecondIntegrable hk hkn i

theorem ex_14_4_3_stageMeasure_centered_second_moment_eq
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    ∫ m, (Prob63Support.scalarStageWait m -
        1 / Prob63Support.stageSuccessProb n i) ^ 2
      ∂(Prob63Support.stageMeasure n k hk hkn i) =
      ex_14_4_3_geometricVariance
        (Prob63Support.stageSuccessProb n i) := by
  simpa [ex_14_4_3_geometricVariance] using
    chapter14_couponStageMeasure_centered_second_moment_eq hk hkn i

lemma ex_14_4_3_stageCenteredFourthSummableNorm
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    Summable
      (fun m : ℕ =>
        (Prob63Support.stageMeasure n k hk hkn i {m}).toReal *
          ‖(Prob63Support.scalarStageWait m -
              1 / Prob63Support.stageSuccessProb n i) ^ 4‖) :=
  chapter14_couponStageCenteredFourthSummableNorm hk hkn i

lemma ex_14_4_3_stageCenteredFourthIntegrable
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    Integrable
      (fun m : ℕ =>
        (Prob63Support.scalarStageWait m -
          1 / Prob63Support.stageSuccessProb n i) ^ 4)
      (Prob63Support.stageMeasure n k hk hkn i) :=
  chapter14_couponStageCenteredFourthIntegrable hk hkn i

theorem ex_14_4_3_stageMeasure_centered_fourth_moment_eq
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    ∫ m, (Prob63Support.scalarStageWait m -
        1 / Prob63Support.stageSuccessProb n i) ^ 4
      ∂(Prob63Support.stageMeasure n k hk hkn i) =
      ex_14_4_3_geometricCenteredFourthMoment
        (Prob63Support.stageSuccessProb n i) := by
  simpa [ex_14_4_3_geometricCenteredFourthMoment] using
    chapter14_couponStageMeasure_centered_fourth_moment_eq hk hkn i

lemma ex_14_4_3_rpow_abs_four_eq_pow_four (x : ℝ) :
    Real.rpow |x| (2 + (2 : ℝ)) = x ^ 4 :=
  chapter14_rpow_abs_four_eq_pow_four x

theorem ex_14_4_3_centeredCouponStageLaw_second_moment_eq
    (n : ℕ) (i : Fin (ex_14_4_3_targetDistinct n)) :
    ∫ x, x ^ 2 ∂((ex_14_4_3_centeredCouponStageLaw n i :
        ProbabilityMeasure ℝ) : Measure ℝ) =
      ex_14_4_3_geometricVariance (ex_14_4_3_successProbability n i) := by
  unfold ex_14_4_3_centeredCouponStageLaw
  rw [ProbabilityMeasure.toMeasure_map]
  rw [integral_map
    ((measurable_of_countable (ex_14_4_3_centeredStageValue n i)).aemeasurable)
    (by fun_prop)]
  simpa [ex_14_4_3_stageProbabilityMeasure, ex_14_4_3_centeredStageValue,
    ex_14_4_3_geometricMean, chapter14_geometricMean,
    ex_14_4_3_successProbability] using
    (ex_14_4_3_stageMeasure_centered_second_moment_eq
      (ex_14_4_3_targetDistinct_pos n)
      (ex_14_4_3_targetDistinct_le_couponTypes n) i)

theorem ex_14_4_3_centeredCouponStageLaw_lyapunovMoment_eq
    (n : ℕ) (i : Fin (ex_14_4_3_targetDistinct n)) :
    thm_14_8_lyapunovMoment (ex_14_4_3_centeredCouponStageLaw n i) 2 =
      ex_14_4_3_geometricCenteredFourthMoment
        (ex_14_4_3_successProbability n i) := by
  unfold thm_14_8_lyapunovMoment ex_14_4_3_centeredCouponStageLaw
  rw [ProbabilityMeasure.toMeasure_map]
  simp_rw [ex_14_4_3_rpow_abs_four_eq_pow_four]
  rw [integral_map
    ((measurable_of_countable (ex_14_4_3_centeredStageValue n i)).aemeasurable)
    (by fun_prop)]
  simpa [ex_14_4_3_stageProbabilityMeasure, ex_14_4_3_centeredStageValue,
    ex_14_4_3_geometricMean, chapter14_geometricMean,
    ex_14_4_3_successProbability] using
    (ex_14_4_3_stageMeasure_centered_fourth_moment_eq
      (ex_14_4_3_targetDistinct_pos n)
      (ex_14_4_3_targetDistinct_le_couponTypes n) i)

theorem ex_14_4_3_centeredFourthMoment_bound_of_half
    {p : ℝ} (hp_lower : (1 / 2 : ℝ) ≤ p) (hp_upper : p ≤ 1) :
    ex_14_4_3_geometricCenteredFourthMoment p ≤ 160 := by
  have hp_pos : 0 < p := by linarith
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hp_sq_lower : (1 / 4 : ℝ) ≤ p ^ 2 := by
    nlinarith [hp_lower, hp_pos]
  have hp_four_lower : (1 / 16 : ℝ) ≤ p ^ 4 := by
    have hmul :
        (1 / 4 : ℝ) * (1 / 4 : ℝ) ≤ p ^ 2 * p ^ 2 :=
      mul_le_mul hp_sq_lower hp_sq_lower (by norm_num) (by nlinarith)
    nlinarith
  have hp_four_pos : 0 < p ^ 4 := pow_pos hp_pos 4
  have hinv_le : (1 / p ^ 4 : ℝ) ≤ 16 := by
    rw [div_le_iff₀ hp_four_pos]
    nlinarith [hp_four_lower]
  have hinv_nonneg : 0 ≤ (1 / p ^ 4 : ℝ) := by positivity
  have hgap_nonneg : 0 ≤ 1 - p := by linarith
  have hgap_le : 1 - p ≤ 1 := by linarith
  have hquad_nonneg : 0 ≤ p ^ 2 - 9 * p + 9 := by
    nlinarith [sq_nonneg p, hp_upper]
  have hquad_le : p ^ 2 - 9 * p + 9 ≤ 10 := by
    have hp_sq_le_one : p ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (p - 1), hp_nonneg, hp_upper]
    nlinarith [hp_sq_le_one, hp_nonneg]
  have hfirst :
      (1 / p ^ 4 : ℝ) * (1 - p) ≤ 16 * 1 :=
    mul_le_mul hinv_le hgap_le hgap_nonneg (by norm_num)
  have hfirst_nonneg : 0 ≤ (1 / p ^ 4 : ℝ) * (1 - p) :=
    mul_nonneg hinv_nonneg hgap_nonneg
  have hprod :
      ((1 / p ^ 4 : ℝ) * (1 - p)) * (p ^ 2 - 9 * p + 9) ≤
        (16 * 1 : ℝ) * 10 :=
    mul_le_mul hfirst hquad_le hquad_nonneg (by norm_num)
  unfold ex_14_4_3_geometricCenteredFourthMoment
    chapter14_geometricCenteredFourthMoment
  nlinarith

theorem ex_14_4_3_fourth_moment_row_sum_is_O_n (n : ℕ) :
    (∑ i : Fin (ex_14_4_3_targetDistinct n),
      ex_14_4_3_geometricCenteredFourthMoment
        (ex_14_4_3_successProbability n i)) ≤
      160 * (ex_14_4_3_couponTypes n : ℝ) := by
  calc
    (∑ i : Fin (ex_14_4_3_targetDistinct n),
      ex_14_4_3_geometricCenteredFourthMoment
        (ex_14_4_3_successProbability n i))
        ≤ ∑ _i : Fin (ex_14_4_3_targetDistinct n), (160 : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          exact ex_14_4_3_centeredFourthMoment_bound_of_half
            (ex_14_4_3_half_coupon_success_probability_bounds n i).1
            (ex_14_4_3_half_coupon_success_probability_bounds n i).2
    _ = (ex_14_4_3_targetDistinct n : ℝ) * 160 := by simp
    _ ≤ (ex_14_4_3_couponTypes n : ℝ) * 160 := by
      have htarget :
          ex_14_4_3_targetDistinct n ≤ ex_14_4_3_couponTypes n := by
        unfold ex_14_4_3_targetDistinct ex_14_4_3_couponTypes
        omega
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast htarget) (by norm_num)
    _ = 160 * (ex_14_4_3_couponTypes n : ℝ) := by ring
