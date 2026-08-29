/-
TASK ID: ex_14_4_3
TYPE: Example_Proof
SOURCE PLAN: chapter14-central-limit-theorems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.prob_6_3
import ToyApollo.Output.thm_14_7
import ToyApollo.Output.thm_14_8

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology BigOperators

noncomputable section

namespace Ex1443LocalGeometric

open ProbabilityTheory

def chapter14_geometricMgf (p t : ℝ) : ℝ :=
  p * Real.exp t / (1 - (1 - p) * Real.exp t)

theorem chapter14_geometric_mgf_hasSum
    {p t : ℝ} (ht : ‖(1 - p) * Real.exp t‖ < 1) :
    HasSum
      (fun m : ℕ =>
        ProbabilityTheory.geometricPMFReal p m *
          Real.exp (t * Prob63Support.scalarStageWait m))
      (chapter14_geometricMgf p t) := by
  let r : ℝ := (1 - p) * Real.exp t
  have hgeom := (hasSum_geometric_of_norm_lt_one (ξ := r) ht).mul_left
    (p * Real.exp t)
  have hterm :
      (fun m : ℕ =>
        ProbabilityTheory.geometricPMFReal p m *
          Real.exp (t * Prob63Support.scalarStageWait m)) =
        (fun m : ℕ => p * Real.exp t * r ^ m) := by
    funext m
    change ((1 - p) ^ m * p) *
        Real.exp (t * Prob63Support.scalarStageWait m) = _
    dsimp [r, Prob63Support.scalarStageWait]
    have hexp :
        Real.exp (t * ((m : ℝ) + 1)) =
          Real.exp t * (Real.exp t) ^ m := by
      rw [show t * ((m : ℝ) + 1) = t + (m : ℝ) * t by ring]
      rw [Real.exp_add]
      rw [show Real.exp ((m : ℝ) * t) = (Real.exp t) ^ m by
        simpa [mul_comm] using Real.exp_nat_mul t m]
    rw [hexp]
    have hpow :
        (Real.exp t) ^ m * (1 - p) ^ m =
          ((1 - p) * Real.exp t) ^ m := by
      rw [← mul_pow]
      ring
    calc
      (1 - p) ^ m * p * (Real.exp t * Real.exp t ^ m)
          = p * Real.exp t * ((Real.exp t) ^ m * (1 - p) ^ m) := by
            ring
      _ = p * Real.exp t * (((1 - p) * Real.exp t) ^ m) := by
            rw [hpow]
  have htarget :
      p * Real.exp t * (1 - r)⁻¹ = chapter14_geometricMgf p t := by
    simp [chapter14_geometricMgf, r, div_eq_mul_inv]
  rw [hterm, ← htarget]
  exact hgeom

def chapter14_geometricMean (p : ℝ) : ℝ :=
  1 / p

def chapter14_geometricVariance (p : ℝ) : ℝ :=
  (1 - p) / p ^ 2

def chapter14_geometricCenteredFourthMoment (p : ℝ) : ℝ :=
  (1 / p ^ 4) * (1 - p) * (p ^ 2 - 9 * p + 9)

lemma chapter14_choose_add_two_cast (m : ℕ) :
    (((m + 2).choose 2 : ℕ) : ℝ) =
      ((m : ℝ) + 1) * ((m : ℝ) + 2) / 2 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [show m.succ + 2 = (m + 2).succ by omega, Nat.choose_succ_succ]
      rw [Nat.choose_one_right]
      norm_num at ih ⊢
      nlinarith

lemma chapter14_geometric_centeredSecond_term_choose_expansion
    {p r : ℝ} (hp : p ≠ 0) (m : ℕ) :
    ((m : ℝ) + 1 - 1 / p) ^ 2 * p * r ^ m =
      (((2 * p) * (((m + 2).choose 2 : ℕ) : ℝ)
        + (-(p + 2)) * (((m + 1).choose 1 : ℕ) : ℝ)
        + (1 / p)) * r ^ m) := by
  rw [chapter14_choose_add_two_cast m, Nat.choose_one_right]
  push_cast
  field_simp [hp]
  ring_nf

theorem chapter14_geometric_centered_second_hasSum
    {p : ℝ} (hp_pos : 0 < p) (hp_le : p ≤ 1) :
    HasSum
      (fun m : ℕ =>
        (((m : ℝ) + 1 - 1 / p) ^ 2) *
          ProbabilityTheory.geometricPMFReal p m)
      (chapter14_geometricVariance p) := by
  let r : ℝ := 1 - p
  have hp_ne : p ≠ 0 := hp_pos.ne'
  have hr_nonneg : 0 ≤ r := by dsimp [r]; linarith
  have hr_lt : r < 1 := by dsimp [r]; linarith
  have hr_norm : ‖r‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hr_nonneg] using hr_lt
  have h2 :=
    (hasSum_choose_mul_geometric_of_norm_lt_one 2 (𝕜 := ℝ) hr_norm).mul_left
      (2 * p)
  have h1 :=
    (hasSum_choose_mul_geometric_of_norm_lt_one 1 (𝕜 := ℝ) hr_norm).mul_left
      (-(p + 2))
  have h0 :=
    (hasSum_choose_mul_geometric_of_norm_lt_one 0 (𝕜 := ℝ) hr_norm).mul_left
      (1 / p)
  have hsum := (h2.add h1).add h0
  have htarget :
      ((2 * p) * (1 / (1 - r) ^ (2 + 1)) +
          (-(p + 2)) * (1 / (1 - r) ^ (1 + 1))) +
          (1 / p) * (1 / (1 - r) ^ (0 + 1)) =
        chapter14_geometricVariance p := by
    dsimp [chapter14_geometricVariance, r]
    field_simp [hp_ne]
    ring
  have hterm :
      (fun m : ℕ =>
        (((m : ℝ) + 1 - 1 / p) ^ 2) *
          ProbabilityTheory.geometricPMFReal p m) =
        (fun m : ℕ =>
          2 * p * (↑((m + 2).choose 2) * r ^ m) +
            -(p + 2) * (↑((m + 1).choose 1) * r ^ m) +
              1 / p * (↑((m + 0).choose 0) * r ^ m)) := by
    funext m
    change (((m : ℝ) + 1 - 1 / p) ^ 2) * ((1 - p) ^ m * p) = _
    dsimp [r]
    calc
      ((m : ℝ) + 1 - 1 / p) ^ 2 * ((1 - p) ^ m * p)
          = ((m : ℝ) + 1 - 1 / p) ^ 2 * p * (1 - p) ^ m := by ring
      _ =
          (((2 * p) * (((m + 2).choose 2 : ℕ) : ℝ)
            + (-(p + 2)) * (((m + 1).choose 1 : ℕ) : ℝ)
            + (1 / p)) * (1 - p) ^ m) :=
          chapter14_geometric_centeredSecond_term_choose_expansion
            (p := p) (r := 1 - p) hp_ne m
      _ =
          2 * p * (↑((m + 2).choose 2) * (1 - p) ^ m) +
            -(p + 2) * (↑((m + 1).choose 1) * (1 - p) ^ m) +
              1 / p * (↑((m + 0).choose 0) * (1 - p) ^ m) := by
          simp
          ring
  rw [hterm, ← htarget]
  exact hsum

theorem chapter14_geometric_centered_second_tsum_eq
    {p : ℝ} (hp_pos : 0 < p) (hp_le : p ≤ 1) :
    (∑' m : ℕ,
      (Prob63Support.scalarStageWait m - 1 / p) ^ 2 *
        ProbabilityTheory.geometricPMFReal p m) =
      chapter14_geometricVariance p := by
  simpa [Prob63Support.scalarStageWait] using
    (chapter14_geometric_centered_second_hasSum hp_pos hp_le).tsum_eq

lemma chapter14_choose_add_three_cast (m : ℕ) :
    (((m + 3).choose 3 : ℕ) : ℝ) =
      ((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) / 6 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [show m.succ + 3 = (m + 3).succ by omega, Nat.choose_succ_succ]
      have h2 := chapter14_choose_add_two_cast (m + 1)
      norm_num at h2 ih ⊢
      nlinarith

lemma chapter14_choose_add_four_cast (m : ℕ) :
    (((m + 4).choose 4 : ℕ) : ℝ) =
      ((m : ℝ) + 1) * ((m : ℝ) + 2) *
        ((m : ℝ) + 3) * ((m : ℝ) + 4) / 24 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [show m.succ + 4 = (m + 4).succ by omega, Nat.choose_succ_succ]
      have h3 := chapter14_choose_add_three_cast (m + 1)
      norm_num at h3 ih ⊢
      nlinarith

lemma chapter14_geometric_centeredFourth_term_choose_expansion
    {p r : ℝ} (hp : p ≠ 0) (m : ℕ) :
    ((m : ℝ) + 1 - 1 / p) ^ 4 * p * r ^ m =
      (((24 * p) * (((m + 4).choose 4 : ℕ) : ℝ)
        + (-(36 * p + 24)) * (((m + 3).choose 3 : ℕ) : ℝ)
        + (14 * p + 24 + 12 / p) * (((m + 2).choose 2 : ℕ) : ℝ)
        + (-(p + 4 + 6 / p + 4 / p ^ 2)) *
            (((m + 1).choose 1 : ℕ) : ℝ)
        + (1 / p ^ 3)) * r ^ m) := by
  rw [chapter14_choose_add_two_cast m,
    chapter14_choose_add_three_cast m,
    chapter14_choose_add_four_cast m,
    Nat.choose_one_right]
  push_cast
  field_simp [hp]
  ring_nf

theorem chapter14_geometric_centered_fourth_hasSum
    {p : ℝ} (hp_pos : 0 < p) (hp_le : p ≤ 1) :
    HasSum
      (fun m : ℕ =>
        (((m : ℝ) + 1 - 1 / p) ^ 4) *
          ProbabilityTheory.geometricPMFReal p m)
      (chapter14_geometricCenteredFourthMoment p) := by
  let r : ℝ := 1 - p
  have hp_ne : p ≠ 0 := hp_pos.ne'
  have hr_nonneg : 0 ≤ r := by dsimp [r]; linarith
  have hr_lt : r < 1 := by dsimp [r]; linarith
  have hr_norm : ‖r‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hr_nonneg] using hr_lt
  have h4 :=
    (hasSum_choose_mul_geometric_of_norm_lt_one 4 (𝕜 := ℝ) hr_norm).mul_left
      (24 * p)
  have h3 :=
    (hasSum_choose_mul_geometric_of_norm_lt_one 3 (𝕜 := ℝ) hr_norm).mul_left
      (-(36 * p + 24))
  have h2 :=
    (hasSum_choose_mul_geometric_of_norm_lt_one 2 (𝕜 := ℝ) hr_norm).mul_left
      (14 * p + 24 + 12 / p)
  have h1 :=
    (hasSum_choose_mul_geometric_of_norm_lt_one 1 (𝕜 := ℝ) hr_norm).mul_left
      (-(p + 4 + 6 / p + 4 / p ^ 2))
  have h0 :=
    (hasSum_choose_mul_geometric_of_norm_lt_one 0 (𝕜 := ℝ) hr_norm).mul_left
      (1 / p ^ 3)
  have hsum := (((h4.add h3).add h2).add h1).add h0
  have htarget :
      ((((24 * p) * (1 / (1 - r) ^ (4 + 1)) +
          (-(36 * p + 24)) * (1 / (1 - r) ^ (3 + 1))) +
          (14 * p + 24 + 12 / p) * (1 / (1 - r) ^ (2 + 1))) +
          (-(p + 4 + 6 / p + 4 / p ^ 2)) *
            (1 / (1 - r) ^ (1 + 1))) +
          (1 / p ^ 3) * (1 / (1 - r) ^ (0 + 1)) =
        chapter14_geometricCenteredFourthMoment p := by
    dsimp [chapter14_geometricCenteredFourthMoment, r]
    field_simp [hp_ne]
    ring
  have hterm :
      (fun m : ℕ =>
        (((m : ℝ) + 1 - 1 / p) ^ 4) *
          ProbabilityTheory.geometricPMFReal p m) =
        (fun m : ℕ =>
          24 * p * (↑((m + 4).choose 4) * r ^ m) +
              -(36 * p + 24) * (↑((m + 3).choose 3) * r ^ m) +
            (14 * p + 24 + 12 / p) *
                (↑((m + 2).choose 2) * r ^ m) +
          -(p + 4 + 6 / p + 4 / p ^ 2) *
              (↑((m + 1).choose 1) * r ^ m) +
        1 / p ^ 3 * (↑((m + 0).choose 0) * r ^ m)) := by
    funext m
    change (((m : ℝ) + 1 - 1 / p) ^ 4) * ((1 - p) ^ m * p) = _
    dsimp [r]
    calc
      ((m : ℝ) + 1 - 1 / p) ^ 4 * ((1 - p) ^ m * p)
          = ((m : ℝ) + 1 - 1 / p) ^ 4 * p * (1 - p) ^ m := by ring
      _ =
          (((24 * p) * (((m + 4).choose 4 : ℕ) : ℝ)
            + (-(36 * p + 24)) * (((m + 3).choose 3 : ℕ) : ℝ)
            + (14 * p + 24 + 12 / p) * (((m + 2).choose 2 : ℕ) : ℝ)
            + (-(p + 4 + 6 / p + 4 / p ^ 2)) *
                (((m + 1).choose 1 : ℕ) : ℝ)
            + (1 / p ^ 3)) * (1 - p) ^ m) :=
          chapter14_geometric_centeredFourth_term_choose_expansion
            (p := p) (r := 1 - p) hp_ne m
      _ =
          24 * p * (↑((m + 4).choose 4) * (1 - p) ^ m) +
              -(36 * p + 24) * (↑((m + 3).choose 3) * (1 - p) ^ m) +
            (14 * p + 24 + 12 / p) *
                (↑((m + 2).choose 2) * (1 - p) ^ m) +
          -(p + 4 + 6 / p + 4 / p ^ 2) *
              (↑((m + 1).choose 1) * (1 - p) ^ m) +
        1 / p ^ 3 * (↑((m + 0).choose 0) * (1 - p) ^ m) := by
          simp
          ring
  rw [hterm, ← htarget]
  exact hsum

theorem chapter14_geometric_centered_fourth_tsum_eq
    {p : ℝ} (hp_pos : 0 < p) (hp_le : p ≤ 1) :
    (∑' m : ℕ,
      (Prob63Support.scalarStageWait m - 1 / p) ^ 4 *
        ProbabilityTheory.geometricPMFReal p m) =
      chapter14_geometricCenteredFourthMoment p := by
  simpa [Prob63Support.scalarStageWait] using
    (chapter14_geometric_centered_fourth_hasSum hp_pos hp_le).tsum_eq

lemma chapter14_couponStageMgfSummableNorm
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) {t : ℝ}
    (ht : ‖(1 - Prob63Support.stageSuccessProb n i) * Real.exp t‖ < 1) :
    Summable
      (fun m : ℕ =>
        (Prob63Support.stageMeasure n k hk hkn i {m}).toReal *
          ‖Real.exp (t * Prob63Support.scalarStageWait m)‖) := by
  have hsum :=
    (chapter14_geometric_mgf_hasSum
      (p := Prob63Support.stageSuccessProb n i) (t := t) ht).summable
  refine hsum.congr ?_
  intro m
  rw [Prob63Support.stageMeasure_apply_singleton_toReal hk hkn i m]
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]

lemma chapter14_couponStageMgfIntegrable
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) {t : ℝ}
    (ht : ‖(1 - Prob63Support.stageSuccessProb n i) * Real.exp t‖ < 1) :
    Integrable
      (fun m : ℕ => Real.exp (t * Prob63Support.scalarStageWait m))
      (Prob63Support.stageMeasure n k hk hkn i) := by
  rw [← Measure.sum_smul_dirac (Prob63Support.stageMeasure n k hk hkn i)]
  apply MeasureTheory.integrable_sum_dirac
  · intro m
    haveI : IsProbabilityMeasure (Prob63Support.stageMeasure n k hk hkn i) := by
      unfold Prob63Support.stageMeasure
      infer_instance
    have hle :
        Prob63Support.stageMeasure n k hk hkn i {m} ≤
          Prob63Support.stageMeasure n k hk hkn i Set.univ := by
      exact measure_mono (by intro x hx; trivial)
    exact ne_of_lt (lt_of_le_of_lt (by simpa using hle) (by simp))
  · exact chapter14_couponStageMgfSummableNorm hk hkn i ht

theorem chapter14_couponStageMeasure_mgf_eq
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) {t : ℝ}
    (ht : ‖(1 - Prob63Support.stageSuccessProb n i) * Real.exp t‖ < 1) :
    ProbabilityTheory.mgf Prob63Support.scalarStageWait
      (Prob63Support.stageMeasure n k hk hkn i) t =
      Prob63Support.stageSuccessProb n i * Real.exp t /
        (1 - (1 - Prob63Support.stageSuccessProb n i) * Real.exp t) := by
  unfold ProbabilityTheory.mgf Prob63Support.stageMeasure
  rw [PMF.integral_eq_tsum]
  · change
      (∑' a : ℕ,
        ((Prob63Support.stagePMF n k hk hkn i a).toReal) *
          Real.exp (t * Prob63Support.scalarStageWait a)) =
        Prob63Support.stageSuccessProb n i * Real.exp t /
          (1 - (1 - Prob63Support.stageSuccessProb n i) * Real.exp t)
    have hmass :
        ∀ a : ℕ,
          ((Prob63Support.stagePMF n k hk hkn i a).toReal) =
            ProbabilityTheory.geometricPMFReal
              (Prob63Support.stageSuccessProb n i) a := by
      intro a
      unfold Prob63Support.stagePMF ProbabilityTheory.geometricPMF
      change (ENNReal.ofReal
          (ProbabilityTheory.geometricPMFReal
            (Prob63Support.stageSuccessProb n i) a)).toReal =
        ProbabilityTheory.geometricPMFReal
          (Prob63Support.stageSuccessProb n i) a
      rw [ENNReal.toReal_ofReal]
      exact ProbabilityTheory.geometricPMFReal_nonneg
        (Prob63Support.stageSuccessProb_pos hk hkn i)
        (Prob63Support.stageSuccessProb_le_one hk hkn i)
    calc
      (∑' a : ℕ,
        ((Prob63Support.stagePMF n k hk hkn i a).toReal) *
          Real.exp (t * Prob63Support.scalarStageWait a))
          =
        ∑' a : ℕ,
          ProbabilityTheory.geometricPMFReal
            (Prob63Support.stageSuccessProb n i) a *
              Real.exp (t * Prob63Support.scalarStageWait a) := by
            apply tsum_congr
            intro a
            rw [hmass a]
      _ =
        Prob63Support.stageSuccessProb n i * Real.exp t /
          (1 - (1 - Prob63Support.stageSuccessProb n i) * Real.exp t) :=
          (chapter14_geometric_mgf_hasSum
            (p := Prob63Support.stageSuccessProb n i) (t := t) ht).tsum_eq
  · exact chapter14_couponStageMgfIntegrable hk hkn i ht

lemma chapter14_couponStageCenteredSecondSummableNorm
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    Summable
      (fun m : ℕ =>
        (Prob63Support.stageMeasure n k hk hkn i {m}).toReal *
          ‖(Prob63Support.scalarStageWait m -
              1 / Prob63Support.stageSuccessProb n i) ^ 2‖) := by
  have hsum :=
    (chapter14_geometric_centered_second_hasSum
      (Prob63Support.stageSuccessProb_pos hk hkn i)
      (Prob63Support.stageSuccessProb_le_one hk hkn i)).summable
  refine hsum.congr ?_
  intro m
  rw [Prob63Support.stageMeasure_apply_singleton_toReal hk hkn i m]
  rw [Real.norm_of_nonneg (by positivity :
    0 ≤ (Prob63Support.scalarStageWait m -
      1 / Prob63Support.stageSuccessProb n i) ^ 2)]
  simp [Prob63Support.scalarStageWait]
  ring_nf

lemma chapter14_couponStageCenteredSecondIntegrable
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    Integrable
      (fun m : ℕ =>
        (Prob63Support.scalarStageWait m -
          1 / Prob63Support.stageSuccessProb n i) ^ 2)
      (Prob63Support.stageMeasure n k hk hkn i) := by
  rw [← Measure.sum_smul_dirac (Prob63Support.stageMeasure n k hk hkn i)]
  apply MeasureTheory.integrable_sum_dirac
  · intro m
    haveI : IsProbabilityMeasure (Prob63Support.stageMeasure n k hk hkn i) := by
      unfold Prob63Support.stageMeasure
      infer_instance
    have hle :
        Prob63Support.stageMeasure n k hk hkn i {m} ≤
          Prob63Support.stageMeasure n k hk hkn i Set.univ := by
      exact measure_mono (by intro x hx; trivial)
    exact ne_of_lt (lt_of_le_of_lt (by simpa using hle) (by simp))
  · exact chapter14_couponStageCenteredSecondSummableNorm hk hkn i

theorem chapter14_couponStageMeasure_centered_second_moment_eq
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    ∫ m, (Prob63Support.scalarStageWait m -
        1 / Prob63Support.stageSuccessProb n i) ^ 2
      ∂(Prob63Support.stageMeasure n k hk hkn i) =
      chapter14_geometricVariance
        (Prob63Support.stageSuccessProb n i) := by
  unfold Prob63Support.stageMeasure
  rw [PMF.integral_eq_tsum]
  · change
      (∑' a : ℕ,
        ((Prob63Support.stagePMF n k hk hkn i a).toReal) *
          (Prob63Support.scalarStageWait a -
            1 / Prob63Support.stageSuccessProb n i) ^ 2) =
        chapter14_geometricVariance
          (Prob63Support.stageSuccessProb n i)
    have hmass :
        ∀ a : ℕ,
          ((Prob63Support.stagePMF n k hk hkn i a).toReal) =
            ProbabilityTheory.geometricPMFReal
              (Prob63Support.stageSuccessProb n i) a := by
      intro a
      unfold Prob63Support.stagePMF ProbabilityTheory.geometricPMF
      change (ENNReal.ofReal
          (ProbabilityTheory.geometricPMFReal
            (Prob63Support.stageSuccessProb n i) a)).toReal =
        ProbabilityTheory.geometricPMFReal
          (Prob63Support.stageSuccessProb n i) a
      rw [ENNReal.toReal_ofReal]
      exact ProbabilityTheory.geometricPMFReal_nonneg
        (Prob63Support.stageSuccessProb_pos hk hkn i)
        (Prob63Support.stageSuccessProb_le_one hk hkn i)
    calc
      (∑' a : ℕ,
        ((Prob63Support.stagePMF n k hk hkn i a).toReal) *
          (Prob63Support.scalarStageWait a -
            1 / Prob63Support.stageSuccessProb n i) ^ 2)
          =
        ∑' a : ℕ,
          (Prob63Support.scalarStageWait a -
            1 / Prob63Support.stageSuccessProb n i) ^ 2 *
              ProbabilityTheory.geometricPMFReal
                (Prob63Support.stageSuccessProb n i) a := by
            apply tsum_congr
            intro a
            rw [hmass a]
            ring
      _ =
        chapter14_geometricVariance
          (Prob63Support.stageSuccessProb n i) :=
          chapter14_geometric_centered_second_tsum_eq
            (Prob63Support.stageSuccessProb_pos hk hkn i)
            (Prob63Support.stageSuccessProb_le_one hk hkn i)
  · exact chapter14_couponStageCenteredSecondIntegrable hk hkn i

lemma chapter14_couponStageCenteredFourthSummableNorm
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    Summable
      (fun m : ℕ =>
        (Prob63Support.stageMeasure n k hk hkn i {m}).toReal *
          ‖(Prob63Support.scalarStageWait m -
              1 / Prob63Support.stageSuccessProb n i) ^ 4‖) := by
  have hsum :=
    (chapter14_geometric_centered_fourth_hasSum
      (Prob63Support.stageSuccessProb_pos hk hkn i)
      (Prob63Support.stageSuccessProb_le_one hk hkn i)).summable
  refine hsum.congr ?_
  intro m
  rw [Prob63Support.stageMeasure_apply_singleton_toReal hk hkn i m]
  rw [Real.norm_of_nonneg (by positivity :
    0 ≤ (Prob63Support.scalarStageWait m -
      1 / Prob63Support.stageSuccessProb n i) ^ 4)]
  simp [Prob63Support.scalarStageWait]
  ring_nf

lemma chapter14_couponStageCenteredFourthIntegrable
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    Integrable
      (fun m : ℕ =>
        (Prob63Support.scalarStageWait m -
          1 / Prob63Support.stageSuccessProb n i) ^ 4)
      (Prob63Support.stageMeasure n k hk hkn i) := by
  rw [← Measure.sum_smul_dirac (Prob63Support.stageMeasure n k hk hkn i)]
  apply MeasureTheory.integrable_sum_dirac
  · intro m
    haveI : IsProbabilityMeasure (Prob63Support.stageMeasure n k hk hkn i) := by
      unfold Prob63Support.stageMeasure
      infer_instance
    have hle :
        Prob63Support.stageMeasure n k hk hkn i {m} ≤
          Prob63Support.stageMeasure n k hk hkn i Set.univ := by
      exact measure_mono (by intro x hx; trivial)
    exact ne_of_lt (lt_of_le_of_lt (by simpa using hle) (by simp))
  · exact chapter14_couponStageCenteredFourthSummableNorm hk hkn i

theorem chapter14_couponStageMeasure_centered_fourth_moment_eq
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    ∫ m, (Prob63Support.scalarStageWait m -
        1 / Prob63Support.stageSuccessProb n i) ^ 4
      ∂(Prob63Support.stageMeasure n k hk hkn i) =
      chapter14_geometricCenteredFourthMoment
        (Prob63Support.stageSuccessProb n i) := by
  unfold Prob63Support.stageMeasure
  rw [PMF.integral_eq_tsum]
  · change
      (∑' a : ℕ,
        ((Prob63Support.stagePMF n k hk hkn i a).toReal) *
          (Prob63Support.scalarStageWait a -
            1 / Prob63Support.stageSuccessProb n i) ^ 4) =
        chapter14_geometricCenteredFourthMoment
          (Prob63Support.stageSuccessProb n i)
    have hmass :
        ∀ a : ℕ,
          ((Prob63Support.stagePMF n k hk hkn i a).toReal) =
            ProbabilityTheory.geometricPMFReal
              (Prob63Support.stageSuccessProb n i) a := by
      intro a
      unfold Prob63Support.stagePMF ProbabilityTheory.geometricPMF
      change (ENNReal.ofReal
          (ProbabilityTheory.geometricPMFReal
            (Prob63Support.stageSuccessProb n i) a)).toReal =
        ProbabilityTheory.geometricPMFReal
          (Prob63Support.stageSuccessProb n i) a
      rw [ENNReal.toReal_ofReal]
      exact ProbabilityTheory.geometricPMFReal_nonneg
        (Prob63Support.stageSuccessProb_pos hk hkn i)
        (Prob63Support.stageSuccessProb_le_one hk hkn i)
    calc
      (∑' a : ℕ,
        ((Prob63Support.stagePMF n k hk hkn i a).toReal) *
          (Prob63Support.scalarStageWait a -
            1 / Prob63Support.stageSuccessProb n i) ^ 4)
          =
        ∑' a : ℕ,
          (Prob63Support.scalarStageWait a -
            1 / Prob63Support.stageSuccessProb n i) ^ 4 *
              ProbabilityTheory.geometricPMFReal
                (Prob63Support.stageSuccessProb n i) a := by
            apply tsum_congr
            intro a
            rw [hmass a]
            ring
      _ =
        chapter14_geometricCenteredFourthMoment
          (Prob63Support.stageSuccessProb n i) :=
          chapter14_geometric_centered_fourth_tsum_eq
            (Prob63Support.stageSuccessProb_pos hk hkn i)
            (Prob63Support.stageSuccessProb_le_one hk hkn i)
  · exact chapter14_couponStageCenteredFourthIntegrable hk hkn i

lemma chapter14_rpow_abs_four_eq_pow_four (x : ℝ) :
    Real.rpow |x| (2 + (2 : ℝ)) = x ^ 4 := by
  have hpow : |x| ^ 4 = x ^ 4 := by
    nlinarith [sq_abs x]
  norm_num
  simp [hpow]

end Ex1443LocalGeometric

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
  Ex1443LocalGeometric.chapter14_geometricMgf p t

theorem ex_14_4_3_geometric_mgf_hasSum
    {p t : ℝ} (ht : ‖(1 - p) * Real.exp t‖ < 1) :
    HasSum
      (fun m : ℕ =>
        ProbabilityTheory.geometricPMFReal p m *
          Real.exp (t * Prob63Support.scalarStageWait m))
      (ex_14_4_3_geometricMgf p t) := by
  simpa [ex_14_4_3_geometricMgf] using
    Ex1443LocalGeometric.chapter14_geometric_mgf_hasSum (p := p) (t := t) ht

def ex_14_4_3_geometricMean (p : ℝ) : ℝ :=
  Ex1443LocalGeometric.chapter14_geometricMean p

def ex_14_4_3_geometricVariance (p : ℝ) : ℝ :=
  Ex1443LocalGeometric.chapter14_geometricVariance p

def ex_14_4_3_stageProbabilityMeasure
    (n : ℕ) (i : Fin (ex_14_4_3_targetDistinct n)) : ProbabilityMeasure ℕ :=
  ⟨Prob63Support.stageMeasure (ex_14_4_3_couponTypes n)
      (ex_14_4_3_targetDistinct n)
      (ex_14_4_3_targetDistinct_pos n)
      (ex_14_4_3_targetDistinct_le_couponTypes n) i,
    by
      unfold Prob63Support.stageMeasure
      infer_instance⟩

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
        unfold ex_14_4_3_geometricVariance Ex1443LocalGeometric.chapter14_geometricVariance
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
  Ex1443LocalGeometric.chapter14_geometricCenteredFourthMoment p

lemma ex_14_4_3_choose_add_two_cast (m : ℕ) :
    (((m + 2).choose 2 : ℕ) : ℝ) =
      ((m : ℝ) + 1) * ((m : ℝ) + 2) / 2 :=
  Ex1443LocalGeometric.chapter14_choose_add_two_cast m

lemma ex_14_4_3_centeredSecond_term_choose_expansion
    {p r : ℝ} (hp : p ≠ 0) (m : ℕ) :
    ((m : ℝ) + 1 - 1 / p) ^ 2 * p * r ^ m =
      (((2 * p) * (((m + 2).choose 2 : ℕ) : ℝ)
        + (-(p + 2)) * (((m + 1).choose 1 : ℕ) : ℝ)
        + (1 / p)) * r ^ m) :=
  Ex1443LocalGeometric.chapter14_geometric_centeredSecond_term_choose_expansion hp m

theorem ex_14_4_3_geometric_centered_second_hasSum
    {p : ℝ} (hp_pos : 0 < p) (hp_le : p ≤ 1) :
    HasSum
      (fun m : ℕ =>
        (((m : ℝ) + 1 - 1 / p) ^ 2) *
          ProbabilityTheory.geometricPMFReal p m)
      (ex_14_4_3_geometricVariance p) := by
  simpa [ex_14_4_3_geometricVariance] using
    Ex1443LocalGeometric.chapter14_geometric_centered_second_hasSum hp_pos hp_le

theorem ex_14_4_3_geometric_centered_second_tsum_eq
    {p : ℝ} (hp_pos : 0 < p) (hp_le : p ≤ 1) :
    (∑' m : ℕ,
      (Prob63Support.scalarStageWait m - 1 / p) ^ 2 *
        ProbabilityTheory.geometricPMFReal p m) =
      ex_14_4_3_geometricVariance p := by
  simpa [ex_14_4_3_geometricVariance] using
    Ex1443LocalGeometric.chapter14_geometric_centered_second_tsum_eq hp_pos hp_le

lemma ex_14_4_3_choose_add_three_cast (m : ℕ) :
    (((m + 3).choose 3 : ℕ) : ℝ) =
      ((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3) / 6 :=
  Ex1443LocalGeometric.chapter14_choose_add_three_cast m

lemma ex_14_4_3_choose_add_four_cast (m : ℕ) :
    (((m + 4).choose 4 : ℕ) : ℝ) =
      ((m : ℝ) + 1) * ((m : ℝ) + 2) *
        ((m : ℝ) + 3) * ((m : ℝ) + 4) / 24 :=
  Ex1443LocalGeometric.chapter14_choose_add_four_cast m

lemma ex_14_4_3_centeredFourth_term_choose_expansion
    {p r : ℝ} (hp : p ≠ 0) (m : ℕ) :
    ((m : ℝ) + 1 - 1 / p) ^ 4 * p * r ^ m =
      (((24 * p) * (((m + 4).choose 4 : ℕ) : ℝ)
        + (-(36 * p + 24)) * (((m + 3).choose 3 : ℕ) : ℝ)
        + (14 * p + 24 + 12 / p) * (((m + 2).choose 2 : ℕ) : ℝ)
        + (-(p + 4 + 6 / p + 4 / p ^ 2)) *
            (((m + 1).choose 1 : ℕ) : ℝ)
        + (1 / p ^ 3)) * r ^ m) :=
  Ex1443LocalGeometric.chapter14_geometric_centeredFourth_term_choose_expansion hp m

theorem ex_14_4_3_geometric_centered_fourth_hasSum
    {p : ℝ} (hp_pos : 0 < p) (hp_le : p ≤ 1) :
    HasSum
      (fun m : ℕ =>
        (((m : ℝ) + 1 - 1 / p) ^ 4) *
          ProbabilityTheory.geometricPMFReal p m)
      (ex_14_4_3_geometricCenteredFourthMoment p) := by
  simpa [ex_14_4_3_geometricCenteredFourthMoment] using
    Ex1443LocalGeometric.chapter14_geometric_centered_fourth_hasSum hp_pos hp_le

theorem ex_14_4_3_geometric_centered_fourth_tsum_eq
    {p : ℝ} (hp_pos : 0 < p) (hp_le : p ≤ 1) :
    (∑' m : ℕ,
      (Prob63Support.scalarStageWait m - 1 / p) ^ 4 *
        ProbabilityTheory.geometricPMFReal p m) =
      ex_14_4_3_geometricCenteredFourthMoment p := by
  simpa [ex_14_4_3_geometricCenteredFourthMoment] using
    Ex1443LocalGeometric.chapter14_geometric_centered_fourth_tsum_eq hp_pos hp_le

lemma ex_14_4_3_stageMgfSummableNorm
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) {t : ℝ}
    (ht : ‖(1 - Prob63Support.stageSuccessProb n i) * Real.exp t‖ < 1) :
    Summable
      (fun m : ℕ =>
        (Prob63Support.stageMeasure n k hk hkn i {m}).toReal *
          ‖Real.exp (t * Prob63Support.scalarStageWait m)‖) :=
  Ex1443LocalGeometric.chapter14_couponStageMgfSummableNorm hk hkn i ht

lemma ex_14_4_3_stageMgfIntegrable
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) {t : ℝ}
    (ht : ‖(1 - Prob63Support.stageSuccessProb n i) * Real.exp t‖ < 1) :
    Integrable
      (fun m : ℕ => Real.exp (t * Prob63Support.scalarStageWait m))
      (Prob63Support.stageMeasure n k hk hkn i) :=
  Ex1443LocalGeometric.chapter14_couponStageMgfIntegrable hk hkn i ht

theorem ex_14_4_3_stageMeasure_mgf_eq
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) {t : ℝ}
    (ht : ‖(1 - Prob63Support.stageSuccessProb n i) * Real.exp t‖ < 1) :
    ProbabilityTheory.mgf Prob63Support.scalarStageWait
      (Prob63Support.stageMeasure n k hk hkn i) t =
      Prob63Support.stageSuccessProb n i * Real.exp t /
        (1 - (1 - Prob63Support.stageSuccessProb n i) * Real.exp t) :=
  Ex1443LocalGeometric.chapter14_couponStageMeasure_mgf_eq hk hkn i ht

lemma ex_14_4_3_stageCenteredSecondSummableNorm
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    Summable
      (fun m : ℕ =>
        (Prob63Support.stageMeasure n k hk hkn i {m}).toReal *
          ‖(Prob63Support.scalarStageWait m -
              1 / Prob63Support.stageSuccessProb n i) ^ 2‖) :=
  Ex1443LocalGeometric.chapter14_couponStageCenteredSecondSummableNorm hk hkn i

lemma ex_14_4_3_stageCenteredSecondIntegrable
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    Integrable
      (fun m : ℕ =>
        (Prob63Support.scalarStageWait m -
          1 / Prob63Support.stageSuccessProb n i) ^ 2)
      (Prob63Support.stageMeasure n k hk hkn i) :=
  Ex1443LocalGeometric.chapter14_couponStageCenteredSecondIntegrable hk hkn i

theorem ex_14_4_3_stageMeasure_centered_second_moment_eq
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    ∫ m, (Prob63Support.scalarStageWait m -
        1 / Prob63Support.stageSuccessProb n i) ^ 2
      ∂(Prob63Support.stageMeasure n k hk hkn i) =
      ex_14_4_3_geometricVariance
        (Prob63Support.stageSuccessProb n i) := by
  simpa [ex_14_4_3_geometricVariance] using
    Ex1443LocalGeometric.chapter14_couponStageMeasure_centered_second_moment_eq hk hkn i

lemma ex_14_4_3_stageCenteredFourthSummableNorm
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    Summable
      (fun m : ℕ =>
        (Prob63Support.stageMeasure n k hk hkn i {m}).toReal *
          ‖(Prob63Support.scalarStageWait m -
              1 / Prob63Support.stageSuccessProb n i) ^ 4‖) :=
  Ex1443LocalGeometric.chapter14_couponStageCenteredFourthSummableNorm hk hkn i

lemma ex_14_4_3_stageCenteredFourthIntegrable
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    Integrable
      (fun m : ℕ =>
        (Prob63Support.scalarStageWait m -
          1 / Prob63Support.stageSuccessProb n i) ^ 4)
      (Prob63Support.stageMeasure n k hk hkn i) :=
  Ex1443LocalGeometric.chapter14_couponStageCenteredFourthIntegrable hk hkn i

theorem ex_14_4_3_stageMeasure_centered_fourth_moment_eq
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    ∫ m, (Prob63Support.scalarStageWait m -
        1 / Prob63Support.stageSuccessProb n i) ^ 4
      ∂(Prob63Support.stageMeasure n k hk hkn i) =
      ex_14_4_3_geometricCenteredFourthMoment
        (Prob63Support.stageSuccessProb n i) := by
  simpa [ex_14_4_3_geometricCenteredFourthMoment] using
    Ex1443LocalGeometric.chapter14_couponStageMeasure_centered_fourth_moment_eq hk hkn i

lemma ex_14_4_3_rpow_abs_four_eq_pow_four (x : ℝ) :
    Real.rpow |x| (2 + (2 : ℝ)) = x ^ 4 :=
  Ex1443LocalGeometric.chapter14_rpow_abs_four_eq_pow_four x

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
    ex_14_4_3_geometricMean, Ex1443LocalGeometric.chapter14_geometricMean,
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
    ex_14_4_3_geometricMean, Ex1443LocalGeometric.chapter14_geometricMean,
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
    Ex1443LocalGeometric.chapter14_geometricCenteredFourthMoment
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

def ex_14_4_3_couponMean (n : ℕ) : ℝ :=
  Prob63Support.couponCollectorValueReal
    (ex_14_4_3_couponTypes n) (ex_14_4_3_targetDistinct n)

def ex_14_4_3_asymptoticMeanScale (n : ℕ) : ℝ :=
  (ex_14_4_3_couponTypes n : ℝ) * Real.log 2

def ex_14_4_3_asymptoticVarianceScale (n : ℕ) : ℝ :=
  (ex_14_4_3_couponTypes n : ℝ) * (1 - Real.log 2)

def ex_14_4_3_normalizedCouponValue (n : ℕ) (x : ℝ) : ℝ :=
  (x - ex_14_4_3_asymptoticMeanScale n) /
    Real.sqrt (ex_14_4_3_asymptoticVarianceScale n)

def ex_14_4_3_TextbookNormalization
    (couponCollectionLaws normalizedCouponLaws : ℕ → ProbabilityMeasure ℝ) :
    Prop :=
  ∀ n : ℕ,
    normalizedCouponLaws n =
      ProbabilityMeasure.map (couponCollectionLaws n)
        ((by
          have hmeas : Measurable (ex_14_4_3_normalizedCouponValue n) := by
            unfold ex_14_4_3_normalizedCouponValue
            fun_prop
          exact hmeas.aemeasurable) :
          AEMeasurable (ex_14_4_3_normalizedCouponValue n)
            ((couponCollectionLaws n : ProbabilityMeasure ℝ) : Measure ℝ))

namespace Ex1443

theorem centeredCouponStageLaw_sq_integrable
    (n : ℕ) (i : Fin (ex_14_4_3_targetDistinct n)) :
    Integrable (fun x : ℝ ↦ x ^ 2)
      (ex_14_4_3_centeredCouponStageLaw n i : Measure ℝ) := by
  unfold ex_14_4_3_centeredCouponStageLaw
  rw [ProbabilityMeasure.toMeasure_map]
  refine (integrable_map_measure (g := fun x : ℝ ↦ x ^ 2)
    (by fun_prop)
    ((measurable_of_countable
      (ex_14_4_3_centeredStageValue n i)).aemeasurable)).2 ?_
  simpa [Function.comp_def, ex_14_4_3_stageProbabilityMeasure,
    ex_14_4_3_centeredStageValue, ex_14_4_3_geometricMean,
    Ex1443LocalGeometric.chapter14_geometricMean, ex_14_4_3_successProbability] using
    (ex_14_4_3_stageCenteredSecondIntegrable
      (ex_14_4_3_targetDistinct_pos n)
      (ex_14_4_3_targetDistinct_le_couponTypes n) i)

theorem centeredCouponStageLaw_fourth_integrable
    (n : ℕ) (i : Fin (ex_14_4_3_targetDistinct n)) :
    Integrable (fun x : ℝ ↦ Real.rpow |x| (2 + (2 : ℝ)))
      (ex_14_4_3_centeredCouponStageLaw n i : Measure ℝ) := by
  simp_rw [ex_14_4_3_rpow_abs_four_eq_pow_four]
  unfold ex_14_4_3_centeredCouponStageLaw
  rw [ProbabilityMeasure.toMeasure_map]
  refine (integrable_map_measure (g := fun x : ℝ ↦ x ^ 4)
    (by fun_prop)
    ((measurable_of_countable
      (ex_14_4_3_centeredStageValue n i)).aemeasurable)).2 ?_
  simpa [Function.comp_def, ex_14_4_3_stageProbabilityMeasure,
    ex_14_4_3_centeredStageValue, ex_14_4_3_geometricMean,
    Ex1443LocalGeometric.chapter14_geometricMean, ex_14_4_3_successProbability] using
    (ex_14_4_3_stageCenteredFourthIntegrable
      (ex_14_4_3_targetDistinct_pos n)
      (ex_14_4_3_targetDistinct_le_couponTypes n) i)

theorem centeredCouponStageLaw_mean_eq_zero
    (n : ℕ) (i : Fin (ex_14_4_3_targetDistinct n)) :
    ∫ x, x ∂((ex_14_4_3_centeredCouponStageLaw n i :
      ProbabilityMeasure ℝ) : Measure ℝ) = 0 := by
  unfold ex_14_4_3_centeredCouponStageLaw
  rw [ProbabilityMeasure.toMeasure_map]
  rw [integral_map
    ((measurable_of_countable
      (ex_14_4_3_centeredStageValue n i)).aemeasurable)
    (by fun_prop)]
  have hmean :=
    Prob63Support.stageWaitIntegral_eq
      (n := ex_14_4_3_couponTypes n)
      (k := ex_14_4_3_targetDistinct n)
      (ex_14_4_3_targetDistinct_pos n)
      (ex_14_4_3_targetDistinct_le_couponTypes n) i
  unfold ex_14_4_3_centeredStageValue
  rw [integral_sub]
  change
    (∫ a : ℕ, Prob63Support.scalarStageWait a
        ∂Prob63Support.stageMeasure (ex_14_4_3_couponTypes n)
          (ex_14_4_3_targetDistinct n)
          (ex_14_4_3_targetDistinct_pos n)
          (ex_14_4_3_targetDistinct_le_couponTypes n) i) -
      ∫ _a : ℕ,
        ex_14_4_3_geometricMean (ex_14_4_3_successProbability n i)
        ∂Prob63Support.stageMeasure (ex_14_4_3_couponTypes n)
          (ex_14_4_3_targetDistinct n)
          (ex_14_4_3_targetDistinct_pos n)
          (ex_14_4_3_targetDistinct_le_couponTypes n) i = 0
  rw [hmean]
  · unfold ex_14_4_3_successProbability ex_14_4_3_geometricMean
      Ex1443LocalGeometric.chapter14_geometricMean Prob63Support.stageSuccessProb
    haveI : IsProbabilityMeasure
        (Prob63Support.stageMeasure (ex_14_4_3_couponTypes n)
          (ex_14_4_3_targetDistinct n)
          (ex_14_4_3_targetDistinct_pos n)
          (ex_14_4_3_targetDistinct_le_couponTypes n) i) := by
      unfold Prob63Support.stageMeasure
      infer_instance
    rw [integral_const]
    simp
  · exact Prob63Support.stageWaitIntegrable
      (ex_14_4_3_targetDistinct_pos n)
      (ex_14_4_3_targetDistinct_le_couponTypes n) i
  · exact integrable_const _

def shiftedSourceIndex (n : ℕ) : ℕ := n + 1

def totalVariance (n : ℕ) : ℝ :=
  ∑ i : Fin (ex_14_4_3_targetDistinct n),
    ex_14_4_3_geometricVariance (ex_14_4_3_successProbability n i)

def shiftedTotalVariance (n : ℕ) : ℝ :=
  totalVariance (shiftedSourceIndex n)

theorem shiftedTargetDistinct_ge_two (n : ℕ) :
    2 ≤ ex_14_4_3_targetDistinct (shiftedSourceIndex n) := by
  unfold shiftedSourceIndex ex_14_4_3_targetDistinct ex_14_4_3_couponTypes
  omega

theorem shiftedTotalVariance_pos (n : ℕ) :
    0 < shiftedTotalVariance n := by
  let i : Fin (ex_14_4_3_targetDistinct (shiftedSourceIndex n)) :=
    ⟨1, Nat.lt_of_succ_le (shiftedTargetDistinct_ge_two n)⟩
  have hN :
      0 < (ex_14_4_3_couponTypes (shiftedSourceIndex n) : ℝ) := by
    unfold shiftedSourceIndex ex_14_4_3_couponTypes
    positivity
  have hi_pos :
      0 < ((i.1 : ℝ) /
        (ex_14_4_3_couponTypes (shiftedSourceIndex n) : ℝ)) := by
    dsimp [i]
    exact div_pos (by norm_num) hN
  have hterm_pos :
      0 < ex_14_4_3_geometricVariance
        (ex_14_4_3_successProbability (shiftedSourceIndex n) i) :=
    lt_of_lt_of_le hi_pos
      (ex_14_4_3_geometricVariance_ge_index_ratio
        (shiftedSourceIndex n) i)
  have hnonneg :
      ∀ j : Fin (ex_14_4_3_targetDistinct (shiftedSourceIndex n)),
        0 ≤ ex_14_4_3_geometricVariance
          (ex_14_4_3_successProbability (shiftedSourceIndex n) j) := by
    intro j
    exact le_trans (div_nonneg (by positivity) (le_of_lt hN))
      (ex_14_4_3_geometricVariance_ge_index_ratio
        (shiftedSourceIndex n) j)
  exact lt_of_lt_of_le hterm_pos
    (Finset.single_le_sum (fun j _hj ↦ hnonneg j) (Finset.mem_univ i))

theorem shiftedTotalVariance_tendsto_atTop :
    Tendsto shiftedTotalVariance atTop atTop := by
  have hsource := ex_14_4_3_index_ratio_sum_linear_lower_bound
  have hshiftedSource :
      ∀ᶠ n : ℕ in atTop,
        (ex_14_4_3_couponTypes (shiftedSourceIndex n) : ℝ) / 64 ≤
          ∑ i : Fin (ex_14_4_3_targetDistinct (shiftedSourceIndex n)),
            ((i.1 : ℝ) /
              (ex_14_4_3_couponTypes (shiftedSourceIndex n) : ℝ)) := by
    exact (tendsto_add_atTop_nat 1).eventually hsource
  have hbound :
      ∀ᶠ n : ℕ in atTop,
        (ex_14_4_3_couponTypes (shiftedSourceIndex n) : ℝ) / 64 ≤
          shiftedTotalVariance n := by
    filter_upwards [hshiftedSource] with n hn
    exact le_trans hn
      (ex_14_4_3_geometricVariance_row_sum_ge_index_sum
        (shiftedSourceIndex n))
  have hN :
      Tendsto
        (fun n : ℕ ↦
          (ex_14_4_3_couponTypes (shiftedSourceIndex n) : ℝ))
        atTop atTop := by
    convert
      (tendsto_atTop_add_const_right atTop (3 : ℝ)
        (tendsto_natCast_atTop_atTop (R := ℝ))) using 1
    ext n
    simp only [shiftedSourceIndex, ex_14_4_3_couponTypes, Nat.cast_add,
      Nat.cast_one, Nat.cast_ofNat]
    ring
  have hleft :
      Tendsto
        (fun n : ℕ ↦
          (ex_14_4_3_couponTypes (shiftedSourceIndex n) : ℝ) / 64)
        atTop atTop := by
    simpa [div_eq_mul_inv, mul_comm] using
      hN.const_mul_atTop (by norm_num : (0 : ℝ) < (64 : ℝ)⁻¹)
  exact tendsto_atTop_mono' _ hbound hleft

def shiftedArrayNotation : chapter14_TriangularArrayNotation where
  rowLength := fun n ↦ ex_14_4_3_targetDistinct (shiftedSourceIndex n)
  rowLength_pos := fun n ↦
    lt_of_lt_of_le (by norm_num) (shiftedTargetDistinct_ge_two n)
  variance := fun n i ↦
    ex_14_4_3_geometricVariance
      (ex_14_4_3_successProbability (shiftedSourceIndex n) i)
  totalVariance := shiftedTotalVariance
  totalVariance_eq := fun _ ↦ rfl
  totalVariance_tendsto_atTop := shiftedTotalVariance_tendsto_atTop

def theoremSetup : thm_14_8_TriangularArraySetup where
  arrayNotation := shiftedArrayNotation
  rowLaws := fun n i ↦
    ex_14_4_3_centeredCouponStageLaw (shiftedSourceIndex n) i
  row_sq_integrable := fun n i ↦
    centeredCouponStageLaw_sq_integrable (shiftedSourceIndex n) i
  row_mean_zero := fun n i ↦
    centeredCouponStageLaw_mean_eq_zero (shiftedSourceIndex n) i
  row_variance := by
    intro n i
    exact (ex_14_4_3_centeredCouponStageLaw_second_moment_eq
      (shiftedSourceIndex n) i).symm
  totalVariance_pos := shiftedTotalVariance_pos

theorem row_lyapunov_sum_eq_coupon_fourth_sum (n : ℕ) :
    (∑ i : Fin (theoremSetup.arrayNotation.rowLength n),
      thm_14_8_lyapunovMoment (theoremSetup.rowLaws n i) 2) =
      ∑ i : Fin (ex_14_4_3_targetDistinct (shiftedSourceIndex n)),
        ex_14_4_3_geometricCenteredFourthMoment
          (ex_14_4_3_successProbability (shiftedSourceIndex n) i) := by
  simp only [theoremSetup, shiftedArrayNotation]
  exact Finset.sum_congr rfl fun i _hi ↦
    ex_14_4_3_centeredCouponStageLaw_lyapunovMoment_eq
      (shiftedSourceIndex n) i

theorem variance_scale_lower_bound :
    ∀ᶠ n : ℕ in atTop,
      (ex_14_4_3_couponTypes (shiftedSourceIndex n) : ℝ) / 64 ≤
        theoremSetup.arrayNotation.totalVariance n := by
  have hsource :=
    (tendsto_add_atTop_nat 1).eventually
      ex_14_4_3_index_ratio_sum_linear_lower_bound
  filter_upwards [hsource] with n hindex
  exact le_trans hindex
    (ex_14_4_3_geometricVariance_row_sum_ge_index_sum
      (shiftedSourceIndex n))

theorem lyapunov_condition :
    thm_14_8_LyapunovCondition theoremSetup := by
  refine ⟨2, by norm_num, ?_, ?_⟩
  · intro n i
    change Integrable (fun x : ℝ ↦ Real.rpow |x| (2 + (2 : ℝ)))
      (ex_14_4_3_centeredCouponStageLaw (shiftedSourceIndex n) i : Measure ℝ)
    exact centeredCouponStageLaw_fourth_integrable (shiftedSourceIndex n) i
  · let q : ℕ → ℝ := fun n ↦
      (∑ i : Fin (theoremSetup.arrayNotation.rowLength n),
        thm_14_8_lyapunovMoment (theoremSetup.rowLaws n i) 2) /
          Real.rpow (theoremSetup.sn n) (2 + (2 : ℝ))
    let b : ℕ → ℝ := fun n ↦
      (160 * 4096 : ℝ) /
        (ex_14_4_3_couponTypes (shiftedSourceIndex n) : ℝ)
    change Tendsto q atTop (𝓝 (0 : ℝ))
    refine squeeze_zero' (f := q) (g := b) ?_ ?_ ?_
    · filter_upwards with n
      have hnum_nonneg :
          0 ≤
            ∑ i : Fin (theoremSetup.arrayNotation.rowLength n),
              thm_14_8_lyapunovMoment (theoremSetup.rowLaws n i) 2 := by
        refine Finset.sum_nonneg ?_
        intro i _hi
        unfold thm_14_8_lyapunovMoment
        exact integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg x) _
      have hden_nonneg :
          0 ≤ Real.rpow (theoremSetup.sn n) (2 + (2 : ℝ)) :=
        Real.rpow_nonneg (le_of_lt (theoremSetup.sn_pos n)) _
      exact div_nonneg hnum_nonneg hden_nonneg
    · filter_upwards [variance_scale_lower_bound] with n hvar
      have hnum_bound :
          (∑ i : Fin (theoremSetup.arrayNotation.rowLength n),
            thm_14_8_lyapunovMoment (theoremSetup.rowLaws n i) 2) ≤
            160 *
              (ex_14_4_3_couponTypes (shiftedSourceIndex n) : ℝ) := by
        rw [row_lyapunov_sum_eq_coupon_fourth_sum n]
        exact ex_14_4_3_fourth_moment_row_sum_is_O_n
          (shiftedSourceIndex n)
      have hsn_sq_lower :
          (ex_14_4_3_couponTypes (shiftedSourceIndex n) : ℝ) / 64 ≤
            theoremSetup.sn n ^ 2 := by
        simpa [theoremSetup.sn_sq_eq_totalVariance n] using hvar
      have hsn_pos : 0 < theoremSetup.sn n := theoremSetup.sn_pos n
      have hden_eq :
          Real.rpow (theoremSetup.sn n) (2 + (2 : ℝ)) =
            theoremSetup.sn n ^ 4 := by
        norm_num
      have hden_lower :
          ((ex_14_4_3_couponTypes (shiftedSourceIndex n) : ℝ) / 64) ^ 2 ≤
            Real.rpow (theoremSetup.sn n) (2 + (2 : ℝ)) := by
        rw [hden_eq]
        have hsquare :
            ((ex_14_4_3_couponTypes (shiftedSourceIndex n) : ℝ) / 64) ^ 2 ≤
              (theoremSetup.sn n ^ 2) ^ 2 := by
          nlinarith [sq_nonneg
            (theoremSetup.sn n ^ 2 -
              (ex_14_4_3_couponTypes (shiftedSourceIndex n) : ℝ) / 64)]
        nlinarith
      have hden_pos :
          0 < Real.rpow (theoremSetup.sn n) (2 + (2 : ℝ)) :=
        Real.rpow_pos_of_pos hsn_pos _
      have hN_pos :
          0 < (ex_14_4_3_couponTypes (shiftedSourceIndex n) : ℝ) := by
        unfold shiftedSourceIndex ex_14_4_3_couponTypes
        positivity
      have hsmall_den_pos :
          0 <
            ((ex_14_4_3_couponTypes (shiftedSourceIndex n) : ℝ) / 64) ^ 2 :=
        sq_pos_of_pos (div_pos hN_pos (by norm_num))
      have hquot_bound :
          (∑ i : Fin (theoremSetup.arrayNotation.rowLength n),
            thm_14_8_lyapunovMoment (theoremSetup.rowLaws n i) 2) /
              Real.rpow (theoremSetup.sn n) (2 + (2 : ℝ)) ≤
            (160 *
              (ex_14_4_3_couponTypes (shiftedSourceIndex n) : ℝ)) /
              (((ex_14_4_3_couponTypes (shiftedSourceIndex n) : ℝ) / 64) ^ 2) := by
        gcongr
      have hsimplify :
          (160 * (ex_14_4_3_couponTypes (shiftedSourceIndex n) : ℝ)) /
              (((ex_14_4_3_couponTypes (shiftedSourceIndex n) : ℝ) / 64) ^ 2) =
            (160 * 4096 : ℝ) /
              (ex_14_4_3_couponTypes (shiftedSourceIndex n) : ℝ) := by
        field_simp [ne_of_gt hN_pos]
        ring
      simpa [q, b, hsimplify] using hquot_bound
    · have hb :
          Tendsto
            (fun n : ℕ ↦
              (160 * 4096 : ℝ) /
                (ex_14_4_3_couponTypes (shiftedSourceIndex n) : ℝ))
            atTop (𝓝 (0 : ℝ)) := by
        have h :=
          (tendsto_const_div_atTop_nhds_zero_nat (160 * 4096 : ℝ)).comp
            (tendsto_add_atTop_nat 3)
        convert h using 1
        ext n
        simp only [Function.comp_apply, shiftedSourceIndex,
          ex_14_4_3_couponTypes, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
        congr 1
        ring
      simpa [b] using hb

def couponStageProductLaw (n : ℕ) :
    ProbabilityMeasure (Prob63Support.CouponStageΩ (ex_14_4_3_targetDistinct n)) :=
  ProbabilityMeasure.pi (fun i ↦ ex_14_4_3_stageProbabilityMeasure n i)

def centeredStageVector (n : ℕ) :
    Prob63Support.CouponStageΩ (ex_14_4_3_targetDistinct n) →
      (Fin (ex_14_4_3_targetDistinct n) → ℝ) :=
  fun ω i ↦ ex_14_4_3_centeredStageValue n i (ω i)

theorem centeredStageVector_measurable (n : ℕ) :
    Measurable (centeredStageVector n) := by
  unfold centeredStageVector
  exact measurable_pi_lambda _ fun i ↦
    (measurable_of_countable
      (ex_14_4_3_centeredStageValue n i)).comp (measurable_pi_apply i)

theorem centeredStageProductLaw_eq_map (n : ℕ) :
    ProbabilityMeasure.pi
        (fun i : Fin (ex_14_4_3_targetDistinct n) ↦
          ex_14_4_3_centeredCouponStageLaw n i) =
      ProbabilityMeasure.map (couponStageProductLaw n)
        ((centeredStageVector_measurable n).aemeasurable :
          AEMeasurable (centeredStageVector n)
            ((couponStageProductLaw n : ProbabilityMeasure _) : Measure _)) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_pi,
    ProbabilityMeasure.toMeasure_map, couponStageProductLaw,
    ex_14_4_3_centeredCouponStageLaw]
  change
    Measure.pi (fun i ↦ Measure.map (ex_14_4_3_centeredStageValue n i)
        (ex_14_4_3_stageProbabilityMeasure n i : Measure ℕ)) =
      Measure.map
        (fun x i ↦ ex_14_4_3_centeredStageValue n i (x i))
        (Measure.pi fun i ↦
          (ex_14_4_3_stageProbabilityMeasure n i : Measure ℕ))
  exact (Measure.pi_map_pi
    (fun i : Fin (ex_14_4_3_targetDistinct n) ↦
      (measurable_of_countable
        (ex_14_4_3_centeredStageValue n i)).aemeasurable)).symm

theorem geometricMean_eq_couponCollectorTerm
    (n : ℕ) (i : Fin (ex_14_4_3_targetDistinct n)) :
    ex_14_4_3_geometricMean (ex_14_4_3_successProbability n i) =
      (ex_14_4_3_couponTypes n : ℝ) /
        (ex_14_4_3_couponTypes n - i.1 : ℕ) := by
  unfold ex_14_4_3_geometricMean Ex1443LocalGeometric.chapter14_geometricMean
    ex_14_4_3_successProbability Prob63Support.stageSuccessProb
  have hN : ((ex_14_4_3_couponTypes n : ℕ) : ℝ) ≠ 0 := by
    unfold ex_14_4_3_couponTypes
    positivity
  have hi_lt : i.1 < ex_14_4_3_couponTypes n :=
    lt_of_lt_of_le i.2 (ex_14_4_3_targetDistinct_le_couponTypes n)
  have hsub :
      (((ex_14_4_3_couponTypes n - i.1 : ℕ) : ℝ) =
        ((ex_14_4_3_couponTypes n : ℕ) : ℝ) - (i.1 : ℝ)) :=
    Nat.cast_sub (Nat.le_of_lt hi_lt)
  have hsub_ne : ((ex_14_4_3_couponTypes n - i.1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt hi_lt).ne'
  rw [hsub]
  field_simp [hN, hsub_ne]

theorem sum_centeredStageVector_eq_couponTime_sub_mean
    (n : ℕ) (ω : Prob63Support.CouponStageΩ (ex_14_4_3_targetDistinct n)) :
    (∑ i, centeredStageVector n ω i) =
      Prob63Support.couponCollectionTimeReal
        (ex_14_4_3_couponTypes n) (ex_14_4_3_targetDistinct n) ω -
        ex_14_4_3_couponMean n := by
  have hmeans :
      (∑ i : Fin (ex_14_4_3_targetDistinct n),
        ex_14_4_3_geometricMean (ex_14_4_3_successProbability n i)) =
        ex_14_4_3_couponMean n := by
    unfold ex_14_4_3_couponMean Prob63Support.couponCollectorValueReal
    exact Finset.sum_congr rfl fun i _hi ↦
      geometricMean_eq_couponCollectorTerm n i
  unfold centeredStageVector ex_14_4_3_centeredStageValue
    Prob63Support.couponCollectionTimeReal Prob63Support.stageWaitReal
  rw [Finset.sum_sub_distrib, hmeans]

def unshiftedExactStandardizedRowSumLaw (n : ℕ) : ProbabilityMeasure ℝ :=
  let rowLaws : Fin (ex_14_4_3_targetDistinct n) → ProbabilityMeasure ℝ :=
    fun i ↦ ex_14_4_3_centeredCouponStageLaw n i
  let rowProductLaw :
      ProbabilityMeasure (Fin (ex_14_4_3_targetDistinct n) → ℝ) :=
    ProbabilityMeasure.pi rowLaws
  let standardizedSum :
      (Fin (ex_14_4_3_targetDistinct n) → ℝ) → ℝ :=
    fun x ↦ (∑ i, x i) / Real.sqrt (totalVariance n)
  thm_14_7_law (rowProductLaw : Measure _)
    standardizedSum (by
      dsimp only [standardizedSum]
      fun_prop)

theorem shiftedCanonicalLaw_eq_unshifted_tail (n : ℕ) :
    theoremSetup.standardizedSumLaw n =
      unshiftedExactStandardizedRowSumLaw (shiftedSourceIndex n) := by
  rfl

def exactCouponStageStandardizedValue (n : ℕ) :
    Prob63Support.CouponStageΩ (ex_14_4_3_targetDistinct n) → ℝ :=
  fun ω ↦
    (Prob63Support.couponCollectionTimeReal
        (ex_14_4_3_couponTypes n) (ex_14_4_3_targetDistinct n) ω -
      ex_14_4_3_couponMean n) /
        Real.sqrt (totalVariance n)

def exactCouponStageStandardizedLaw (n : ℕ) : ProbabilityMeasure ℝ :=
  thm_14_7_law (couponStageProductLaw n : Measure _)
    (exactCouponStageStandardizedValue n)
    (measurable_of_countable
      (exactCouponStageStandardizedValue n)).aemeasurable

theorem unshiftedExactRowSumLaw_eq_couponStageLaw (n : ℕ) :
    unshiftedExactStandardizedRowSumLaw n =
      exactCouponStageStandardizedLaw n := by
  apply ProbabilityMeasure.toMeasure_injective
  change
    Measure.map
        (fun x : Fin (ex_14_4_3_targetDistinct n) → ℝ ↦
          (∑ i, x i) / Real.sqrt (totalVariance n))
        (Measure.pi fun i : Fin (ex_14_4_3_targetDistinct n) ↦
          (ex_14_4_3_centeredCouponStageLaw n i : Measure ℝ)) =
      Measure.map (exactCouponStageStandardizedValue n)
        (couponStageProductLaw n : Measure _)
  have hproduct :
      (Measure.pi fun i : Fin (ex_14_4_3_targetDistinct n) ↦
          (ex_14_4_3_centeredCouponStageLaw n i : Measure ℝ)) =
        Measure.map (centeredStageVector n)
          (couponStageProductLaw n : Measure _) := by
    exact congrArg ProbabilityMeasure.toMeasure
      (centeredStageProductLaw_eq_map n)
  rw [hproduct]
  rw [Measure.map_map]
  · exact Measure.map_congr (Filter.Eventually.of_forall fun ω ↦ by
      change
        (∑ i, centeredStageVector n ω i) / Real.sqrt (totalVariance n) =
          (Prob63Support.couponCollectionTimeReal
              (ex_14_4_3_couponTypes n) (ex_14_4_3_targetDistinct n) ω -
            ex_14_4_3_couponMean n) / Real.sqrt (totalVariance n)
      rw [sum_centeredStageVector_eq_couponTime_sub_mean])
  · fun_prop
  · exact centeredStageVector_measurable n

theorem exactCouponStageStandardizedLaw_converges :
    Tendsto exactCouponStageStandardizedLaw atTop
      (𝓝 Thm148Core.Setup.standardNormalLaw) := by
  have hcanonical : thm_14_8_conclusion theoremSetup :=
    thm_14_8_of_lyapunov theoremSetup lyapunov_condition
  have htail :
      Tendsto
        (fun n ↦ exactCouponStageStandardizedLaw (shiftedSourceIndex n))
        atTop (𝓝 Thm148Core.Setup.standardNormalLaw) := by
    apply hcanonical.congr'
    filter_upwards with n
    exact (shiftedCanonicalLaw_eq_unshifted_tail n).trans
      (unshiftedExactRowSumLaw_eq_couponStageLaw (shiftedSourceIndex n))
  simpa [shiftedSourceIndex] using
    (tendsto_add_atTop_iff_nat
      (f := exactCouponStageStandardizedLaw) 1).1 htail

def couponCollectionLaw (n : ℕ) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map (couponStageProductLaw n)
    ((measurable_of_countable
      (Prob63Support.couponCollectionTimeReal
        (ex_14_4_3_couponTypes n)
        (ex_14_4_3_targetDistinct n))).aemeasurable)

def textbookNormalizedCouponLaw (n : ℕ) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map (couponCollectionLaw n)
    ((by
      have hmeas : Measurable (ex_14_4_3_normalizedCouponValue n) := by
        unfold ex_14_4_3_normalizedCouponValue
        fun_prop
      exact hmeas.aemeasurable) :
      AEMeasurable (ex_14_4_3_normalizedCouponValue n)
        ((couponCollectionLaw n : ProbabilityMeasure ℝ) : Measure ℝ))

theorem textbook_normalization :
    ex_14_4_3_TextbookNormalization
      couponCollectionLaw textbookNormalizedCouponLaw := by
  intro n
  rfl

theorem asymptoticVarianceScale_pos (n : ℕ) :
    0 < ex_14_4_3_asymptoticVarianceScale n := by
  unfold ex_14_4_3_asymptoticVarianceScale ex_14_4_3_couponTypes
  have hcoef : 0 < 1 - Real.log 2 := by
    linarith [Real.log_two_lt_d9]
  exact mul_pos (by positivity) hcoef

def exactToTextbookScale (n : ℕ) : ℝ :=
  Real.sqrt (totalVariance n) /
    Real.sqrt (ex_14_4_3_asymptoticVarianceScale n)

def exactToTextbookShift (n : ℕ) : ℝ :=
  (ex_14_4_3_couponMean n - ex_14_4_3_asymptoticMeanScale n) /
    Real.sqrt (ex_14_4_3_asymptoticVarianceScale n)

def N (n : ℕ) : ℕ := ex_14_4_3_couponTypes n

def m (n : ℕ) : ℕ := ex_14_4_3_targetDistinct n

def L (n : ℕ) : ℕ := N n - m n

def reciprocalTail (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m n),
    1 / ((L n + j + 1 : ℕ) : ℝ)

def squareReciprocalTail (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m n),
    1 / (((L n + j + 1 : ℕ) : ℝ) ^ 2)

lemma N_eq (n : ℕ) : N n = n + 2 := rfl

lemma m_eq (n : ℕ) : m n = (N n + 1) / 2 := rfl

lemma m_le_N (n : ℕ) : m n ≤ N n := by
  simp [m, N, ex_14_4_3_targetDistinct, ex_14_4_3_couponTypes]
  omega

lemma L_add_m (n : ℕ) : L n + m n = N n := by
  exact Nat.sub_add_cancel (m_le_N n)

lemma L_eq_div_two (n : ℕ) : L n = N n / 2 := by
  unfold L m N ex_14_4_3_targetDistinct ex_14_4_3_couponTypes
  omega

lemma L_pos (n : ℕ) : 0 < L n := by
  rw [L_eq_div_two]
  unfold N ex_14_4_3_couponTypes
  omega

lemma N_pos (n : ℕ) : 0 < N n := by
  unfold N ex_14_4_3_couponTypes
  omega

lemma two_mul_L_le_N (n : ℕ) : 2 * L n ≤ N n := by
  rw [L_eq_div_two]
  omega

lemma N_le_two_mul_L_add_one (n : ℕ) : N n ≤ 2 * L n + 1 := by
  rw [L_eq_div_two]
  omega

lemma L_le_N (n : ℕ) : L n ≤ N n := by
  unfold L
  exact Nat.sub_le _ _

lemma N_sub_L_eq_m (n : ℕ) : N n - L n = m n := by
  have hLm := L_add_m n
  omega

lemma N_add_one_sub_L_add_one (n : ℕ) :
    (N n + 1) - (L n + 1) = m n := by
  have hLm := L_add_m n
  omega

lemma reflected_denominator (n : ℕ) {i : ℕ} (hi : i < m n) :
    N n - i = L n + (m n - 1 - i) + 1 := by
  have hLm := L_add_m n
  omega

theorem couponMean_eq_N_mul_reciprocalTail (n : ℕ) :
    ex_14_4_3_couponMean n = (N n : ℝ) * reciprocalTail n := by
  unfold ex_14_4_3_couponMean Prob63Support.couponCollectorValueReal
  change
    (∑ i : Fin (m n), (N n : ℝ) / ((N n - i.1 : ℕ) : ℝ)) =
      (N n : ℝ) * reciprocalTail n
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ ↦ (N n : ℝ) / ((N n - i : ℕ) : ℝ)) (m n)]
  unfold reciprocalTail
  rw [Finset.mul_sum]
  rw [← Finset.sum_range_reflect
    (fun j : ℕ ↦ (N n : ℝ) * (1 / ((L n + j + 1 : ℕ) : ℝ))) (m n)]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hden := reflected_denominator n (Finset.mem_range.1 hi)
  rw [hden]
  ring

lemma geometricVariance_div_N_eq
    (n : ℕ) {i : ℕ} (hi : i < m n) :
    ex_14_4_3_geometricVariance
        (Prob63Support.stageSuccessProb (N n) ⟨i, hi⟩) / (N n : ℝ) =
      (i : ℝ) / (((N n - i : ℕ) : ℝ) ^ 2) := by
  have hiN : i ≤ N n := le_trans (Nat.le_of_lt hi) (m_le_N n)
  have hNne : (N n : ℝ) ≠ 0 := by exact_mod_cast (N_pos n).ne'
  have hsubne : (((N n - i : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.sub_ne_zero_iff_lt).2
      (lt_of_lt_of_le hi (m_le_N n))
  unfold ex_14_4_3_geometricVariance
    Ex1443LocalGeometric.chapter14_geometricVariance
    Prob63Support.stageSuccessProb
  rw [Nat.cast_sub hiN]
  field_simp [hNne, hsubne]
  ring

theorem totalVariance_div_N_eq_tails (n : ℕ) :
    Ex1443.totalVariance n / (N n : ℝ) =
      (N n : ℝ) * squareReciprocalTail n - reciprocalTail n := by
  unfold Ex1443.totalVariance
  rw [Finset.sum_fin_eq_sum_range, Finset.sum_div]
  calc
    (∑ i ∈ Finset.range (ex_14_4_3_targetDistinct n),
        (if h : i < ex_14_4_3_targetDistinct n then
          ex_14_4_3_geometricVariance
            (ex_14_4_3_successProbability n ⟨i, h⟩)
        else 0) / (N n : ℝ)) =
        ∑ i ∈ Finset.range (m n),
          (i : ℝ) / (((N n - i : ℕ) : ℝ) ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have him : i < m n := Finset.mem_range.1 (by simpa [m] using hi)
      have hit : i < ex_14_4_3_targetDistinct n := by simpa [m] using him
      rw [dif_pos hit]
      simpa [N, m, ex_14_4_3_successProbability] using
        geometricVariance_div_N_eq n him
    _ = ∑ j ∈ Finset.range (m n),
          ((N n : ℝ) / (((L n + j + 1 : ℕ) : ℝ) ^ 2) -
            1 / ((L n + j + 1 : ℕ) : ℝ)) := by
      rw [← Finset.sum_range_reflect
        (fun j : ℕ ↦
          (N n : ℝ) / (((L n + j + 1 : ℕ) : ℝ) ^ 2) -
            1 / ((L n + j + 1 : ℕ) : ℝ)) (m n)]
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hden := reflected_denominator n (Finset.mem_range.1 hi)
      have hiN : i ≤ N n := le_trans
        (Nat.le_of_lt (Finset.mem_range.1 hi)) (m_le_N n)
      have hcast : ((N n - i : ℕ) : ℝ) = (N n : ℝ) - (i : ℝ) :=
        Nat.cast_sub hiN
      rw [← hden, hcast]
      have hne : (N n : ℝ) - (i : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.sub_ne_zero_iff_lt).2
          (lt_of_lt_of_le (Finset.mem_range.1 hi) (m_le_N n))
      field_simp [hne]
      ring
    _ = (N n : ℝ) * squareReciprocalTail n - reciprocalTail n := by
      simp only [squareReciprocalTail, reciprocalTail,
        Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl ?_
      intro j _hj
      ring

lemma reciprocalTail_eq_sum_Ico (n : ℕ) :
    reciprocalTail n =
      ∑ k ∈ Finset.Ico (L n + 1) (N n + 1), 1 / (k : ℝ) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [N_add_one_sub_L_add_one]
  unfold reciprocalTail
  refine Finset.sum_congr rfl ?_
  intro j _hj
  congr 2
  omega

lemma squareReciprocalTail_eq_sum_Ico (n : ℕ) :
    squareReciprocalTail n =
      ∑ k ∈ Finset.Ico (L n + 1) (N n + 1), 1 / ((k : ℝ) ^ 2) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [N_add_one_sub_L_add_one]
  unfold squareReciprocalTail
  refine Finset.sum_congr rfl ?_
  intro j _hj
  congr 3
  omega

lemma reciprocalTail_eq_shifted_sum_Ico (n : ℕ) :
    reciprocalTail n =
      ∑ k ∈ Finset.Ico (L n) (N n), 1 / (((k + 1 : ℕ) : ℝ)) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [N_sub_L_eq_m]
  unfold reciprocalTail
  refine Finset.sum_congr rfl ?_
  intro j _hj
  congr 2

lemma squareReciprocalTail_eq_shifted_sum_Ico (n : ℕ) :
    squareReciprocalTail n =
      ∑ k ∈ Finset.Ico (L n) (N n),
        1 / ((((k + 1 : ℕ) : ℝ)) ^ 2) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [N_sub_L_eq_m]
  unfold squareReciprocalTail
  refine Finset.sum_congr rfl ?_
  intro j _hj
  congr 3

lemma integral_one_div_sq {a b : ℝ} (h : 0 ∉ Set.uIcc a b) :
    (∫ x in a..b, 1 / x ^ 2) = 1 / a - 1 / b := by
  have hz := integral_zpow (a := a) (b := b) (n := (-2 : ℤ))
    (Or.inr ⟨by norm_num, h⟩)
  norm_num [zpow_neg] at hz ⊢
  calc
    (∫ x in a..b, (x ^ 2)⁻¹) =
        (b⁻¹ - a⁻¹) / (-1 : ℝ) := hz
    _ = a⁻¹ - b⁻¹ := by ring

lemma one_div_sq_antitoneOn {a b : ℝ} (ha : 0 < a) :
    AntitoneOn (fun x : ℝ ↦ 1 / x ^ 2) (Set.Icc a b) := by
  intro x hx y hy hxy
  have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
  have hypos : 0 < y := lt_of_lt_of_le hxpos hxy
  apply one_div_le_one_div_of_le (sq_pos_of_pos hxpos)
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy)
    (add_nonneg hxpos.le hypos.le)]

theorem reciprocalTail_lower (n : ℕ) :
    Real.log (((N n + 1 : ℕ) : ℝ) / ((L n + 1 : ℕ) : ℝ)) ≤
      reciprocalTail n := by
  rw [reciprocalTail_eq_sum_Ico]
  calc
    Real.log (((N n + 1 : ℕ) : ℝ) / ((L n + 1 : ℕ) : ℝ)) =
        ∫ x : ℝ in ((L n + 1 : ℕ) : ℝ)..((N n + 1 : ℕ) : ℝ), 1 / x := by
      rw [integral_one_div_of_pos]
      · exact_mod_cast (Nat.zero_lt_succ (L n))
      · exact_mod_cast (Nat.zero_lt_succ (N n))
    _ ≤ ∑ k ∈ Finset.Ico (L n + 1) (N n + 1), 1 / (k : ℝ) := by
      simpa [one_div] using
        (inv_antitoneOn_Icc_right
          (show (0 : ℝ) < ((L n + 1 : ℕ) : ℝ) by positivity)).integral_le_sum_Ico
            (Nat.add_le_add_right (L_le_N n) 1)

theorem reciprocalTail_upper (n : ℕ) :
    reciprocalTail n ≤ Real.log ((N n : ℝ) / (L n : ℝ)) := by
  rw [reciprocalTail_eq_shifted_sum_Ico]
  calc
    (∑ k ∈ Finset.Ico (L n) (N n), 1 / (((k + 1 : ℕ) : ℝ))) ≤
        ∫ x : ℝ in (L n : ℝ)..(N n : ℝ), 1 / x := by
      simpa [one_div] using
        (inv_antitoneOn_Icc_right
          (show (0 : ℝ) < (L n : ℝ) by exact_mod_cast L_pos n)).sum_le_integral_Ico
            (L_le_N n)
    _ = Real.log ((N n : ℝ) / (L n : ℝ)) := by
      rw [integral_one_div_of_pos]
      · exact_mod_cast L_pos n
      · exact_mod_cast N_pos n

theorem squareReciprocalTail_lower (n : ℕ) :
    1 / ((L n + 1 : ℕ) : ℝ) - 1 / ((N n + 1 : ℕ) : ℝ) ≤
      squareReciprocalTail n := by
  rw [squareReciprocalTail_eq_sum_Ico]
  calc
    1 / ((L n + 1 : ℕ) : ℝ) - 1 / ((N n + 1 : ℕ) : ℝ) =
        ∫ x : ℝ in ((L n + 1 : ℕ) : ℝ)..((N n + 1 : ℕ) : ℝ),
          1 / x ^ 2 := by
      symm
      apply integral_one_div_sq
      exact Set.notMem_uIcc_of_lt (by positivity) (by positivity)
    _ ≤ ∑ k ∈ Finset.Ico (L n + 1) (N n + 1), 1 / ((k : ℝ) ^ 2) := by
      exact (one_div_sq_antitoneOn
        (show (0 : ℝ) < ((L n + 1 : ℕ) : ℝ) by positivity)).integral_le_sum_Ico
          (Nat.add_le_add_right (L_le_N n) 1)

theorem squareReciprocalTail_upper (n : ℕ) :
    squareReciprocalTail n ≤ 1 / (L n : ℝ) - 1 / (N n : ℝ) := by
  rw [squareReciprocalTail_eq_shifted_sum_Ico]
  calc
    (∑ k ∈ Finset.Ico (L n) (N n),
        1 / ((((k + 1 : ℕ) : ℝ)) ^ 2)) ≤
        ∫ x : ℝ in (L n : ℝ)..(N n : ℝ), 1 / x ^ 2 := by
      exact (one_div_sq_antitoneOn
        (show (0 : ℝ) < (L n : ℝ) by exact_mod_cast L_pos n)).sum_le_integral_Ico
          (L_le_N n)
    _ = 1 / (L n : ℝ) - 1 / (N n : ℝ) := by
      apply integral_one_div_sq
      exact Set.notMem_uIcc_of_lt
        (by exact_mod_cast L_pos n) (by exact_mod_cast N_pos n)

theorem N_real_tendsto_atTop :
    Tendsto (fun n ↦ (N n : ℝ)) atTop atTop := by
  change Tendsto (fun n ↦ ((n + 2 : ℕ) : ℝ)) atTop atTop
  exact (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 2)

theorem L_div_N_tendsto_half :
    Tendsto (fun n ↦ (L n : ℝ) / (N n : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) := by
  have h :=
    (tendsto_nat_floor_mul_div_atTop (R := ℝ)
      (a := (1 / 2 : ℝ)) (by norm_num)).comp N_real_tendsto_atTop
  apply h.congr'
  filter_upwards with n
  have hfloor :
      ⌊(1 / 2 : ℝ) * (N n : ℝ)⌋₊ = L n := by
    calc
      ⌊(1 / 2 : ℝ) * (N n : ℝ)⌋₊ =
          ⌊(N n : ℝ) / (2 : ℕ)⌋₊ := by congr 1 <;> ring
      _ = N n / 2 := Nat.floor_div_eq_div (K := ℝ) (N n) 2
      _ = L n := (L_eq_div_two n).symm
  change
    ((⌊(1 / 2 : ℝ) * (N n : ℝ)⌋₊ : ℕ) : ℝ) / (N n : ℝ) =
      (L n : ℝ) / (N n : ℝ)
  rw [hfloor]

theorem N_div_L_tendsto_two :
    Tendsto (fun n ↦ (N n : ℝ) / (L n : ℝ)) atTop (𝓝 (2 : ℝ)) := by
  have h := L_div_N_tendsto_half.inv₀ (by norm_num : (1 / 2 : ℝ) ≠ 0)
  convert h using 1
  · ext n
    have hL : (L n : ℝ) ≠ 0 := by exact_mod_cast (L_pos n).ne'
    have hN : (N n : ℝ) ≠ 0 := by exact_mod_cast (N_pos n).ne'
    field_simp [hL, hN]
  · norm_num

theorem N_add_one_div_L_add_one_tendsto_two :
    Tendsto
      (fun n ↦ ((N n + 1 : ℕ) : ℝ) / ((L n + 1 : ℕ) : ℝ))
      atTop (𝓝 (2 : ℝ)) := by
  have hinvN : Tendsto (fun n ↦ (N n : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp N_real_tendsto_atTop
  have hnum : Tendsto (fun n ↦ ((N n + 1 : ℕ) : ℝ) / (N n : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
    have h : Tendsto (fun n ↦ (1 : ℝ) + (N n : ℝ)⁻¹) atTop
        (𝓝 ((1 : ℝ) + 0)) := tendsto_const_nhds.add hinvN
    have h' : Tendsto (fun n ↦ (1 : ℝ) + (N n : ℝ)⁻¹) atTop
        (𝓝 (1 : ℝ)) := by simpa using h
    apply h'.congr'
    filter_upwards with n
    have hN : (N n : ℝ) ≠ 0 := by exact_mod_cast (N_pos n).ne'
    push_cast
    field_simp [hN]
  have hden : Tendsto (fun n ↦ ((L n + 1 : ℕ) : ℝ) / (N n : ℝ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    have h := L_div_N_tendsto_half.add hinvN
    have h' : Tendsto
        (fun n ↦ (L n : ℝ) / (N n : ℝ) + (N n : ℝ)⁻¹)
        atTop (𝓝 (1 / 2 : ℝ)) := by simpa using h
    apply h'.congr'
    filter_upwards with n
    have hN : (N n : ℝ) ≠ 0 := by exact_mod_cast (N_pos n).ne'
    push_cast
    field_simp [hN]
  have hquot := hnum.div hden (by norm_num : (1 / 2 : ℝ) ≠ 0)
  convert hquot using 1
  · ext n
    have hN : (N n : ℝ) ≠ 0 := by exact_mod_cast (N_pos n).ne'
    have hL1 : ((L n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast
    change
      ((N n : ℝ) + 1) / ((L n : ℝ) + 1) =
        (((N n : ℝ) + 1) / (N n : ℝ)) /
          (((L n : ℝ) + 1) / (N n : ℝ))
    field_simp [hN, hL1]
  · norm_num

theorem reciprocalTail_tendsto_log_two :
    Tendsto reciprocalTail atTop (𝓝 (Real.log 2)) := by
  have hlo := N_add_one_div_L_add_one_tendsto_two.log (by norm_num : (2 : ℝ) ≠ 0)
  have hhi := N_div_L_tendsto_two.log (by norm_num : (2 : ℝ) ≠ 0)
  exact hlo.squeeze hhi reciprocalTail_lower reciprocalTail_upper

theorem L_tendsto_atTop : Tendsto L atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨2 * b, ?_⟩
  intro n hn
  rw [L_eq_div_two, N_eq]
  omega

theorem L_real_tendsto_atTop :
    Tendsto (fun n ↦ (L n : ℝ)) atTop atTop :=
  (tendsto_natCast_atTop_atTop (R := ℝ)).comp L_tendsto_atTop

theorem scaledSquareReciprocalTail_tendsto_one :
    Tendsto (fun n ↦ (N n : ℝ) * squareReciprocalTail n)
      atTop (𝓝 (1 : ℝ)) := by
  have hL1Top : Tendsto (fun n ↦ (L n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 L_real_tendsto_atTop
  have hN1Top : Tendsto (fun n ↦ (N n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 N_real_tendsto_atTop
  have hinvL1 : Tendsto (fun n ↦ ((L n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hL1Top
  have hinvN1 : Tendsto (fun n ↦ ((N n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hN1Top
  have hNL1 : Tendsto (fun n ↦ (N n : ℝ) / ((L n : ℝ) + 1))
      atTop (𝓝 (2 : ℝ)) := by
    have h := N_add_one_div_L_add_one_tendsto_two.sub hinvL1
    have h' : Tendsto
        (fun n ↦ ((N n + 1 : ℕ) : ℝ) / ((L n + 1 : ℕ) : ℝ) -
          ((L n : ℝ) + 1)⁻¹) atTop (𝓝 (2 : ℝ)) := by simpa using h
    apply h'.congr'
    filter_upwards with n
    have hL1 : (L n : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp [hL1]
    ring
  have hNN1 : Tendsto (fun n ↦ (N n : ℝ) / ((N n : ℝ) + 1))
      atTop (𝓝 (1 : ℝ)) := by
    have h : Tendsto (fun n ↦ (1 : ℝ) - ((N n : ℝ) + 1)⁻¹)
        atTop (𝓝 ((1 : ℝ) - 0)) := tendsto_const_nhds.sub hinvN1
    have h' : Tendsto (fun n ↦ (1 : ℝ) - ((N n : ℝ) + 1)⁻¹)
        atTop (𝓝 (1 : ℝ)) := by simpa using h
    apply h'.congr'
    filter_upwards with n
    have hN1 : (N n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hN1]
    ring
  have hlower : Tendsto
      (fun n ↦ (N n : ℝ) *
        (1 / ((L n + 1 : ℕ) : ℝ) - 1 / ((N n + 1 : ℕ) : ℝ)))
      atTop (𝓝 (1 : ℝ)) := by
    have h := hNL1.sub hNN1
    have h' : Tendsto
        (fun n ↦ (N n : ℝ) / ((L n : ℝ) + 1) -
          (N n : ℝ) / ((N n : ℝ) + 1)) atTop (𝓝 (1 : ℝ)) := by
      convert h using 1 <;> norm_num
    apply h'.congr'
    filter_upwards with n
    have hL1 : (L n : ℝ) + 1 ≠ 0 := by positivity
    have hN1 : (N n : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp [hL1, hN1]
  have hupper : Tendsto
      (fun n ↦ (N n : ℝ) *
        (1 / (L n : ℝ) - 1 / (N n : ℝ)))
      atTop (𝓝 (1 : ℝ)) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
      tendsto_const_nhds
    have h := N_div_L_tendsto_two.sub hone
    have h' : Tendsto (fun n ↦ (N n : ℝ) / (L n : ℝ) - 1)
        atTop (𝓝 (1 : ℝ)) := by convert h using 1 <;> norm_num
    apply h'.congr'
    filter_upwards with n
    have hL : (L n : ℝ) ≠ 0 := by exact_mod_cast (L_pos n).ne'
    have hN : (N n : ℝ) ≠ 0 := by exact_mod_cast (N_pos n).ne'
    field_simp [hL, hN]
  exact hlower.squeeze hupper
    (fun n ↦ mul_le_mul_of_nonneg_left (squareReciprocalTail_lower n)
      (Nat.cast_nonneg (N n)))
    (fun n ↦ mul_le_mul_of_nonneg_left (squareReciprocalTail_upper n)
      (Nat.cast_nonneg (N n)))

theorem totalVariance_div_N_tendsto_one_sub_log_two :
    Tendsto (fun n ↦ Ex1443.totalVariance n / (N n : ℝ))
      atTop (𝓝 (1 - Real.log 2)) := by
  have h := scaledSquareReciprocalTail_tendsto_one.sub
    reciprocalTail_tendsto_log_two
  apply h.congr'
  filter_upwards with n
  exact (totalVariance_div_N_eq_tails n).symm

theorem totalVariance_div_asymptoticVarianceScale_tendsto_one :
    Tendsto
      (fun n ↦ Ex1443.totalVariance n /
        ex_14_4_3_asymptoticVarianceScale n)
      atTop (𝓝 (1 : ℝ)) := by
  let c : ℝ := 1 - Real.log 2
  have hcpos : 0 < c := by
    dsimp [c]
    linarith [Real.log_two_lt_d9]
  have h := totalVariance_div_N_tendsto_one_sub_log_two.div_const c
  have h' : Tendsto
      (fun n ↦ (Ex1443.totalVariance n / (N n : ℝ)) / c)
      atTop (𝓝 (1 : ℝ)) := by
    have hlim : (1 - Real.log 2) / c = (1 : ℝ) := by
      dsimp [c]
      exact div_self hcpos.ne'
    rw [hlim] at h
    exact h
  apply h'.congr'
  filter_upwards with n
  have hN : (N n : ℝ) ≠ 0 := by exact_mod_cast (N_pos n).ne'
  unfold ex_14_4_3_asymptoticVarianceScale
  change
    (Ex1443.totalVariance n / (N n : ℝ)) / c =
      Ex1443.totalVariance n / ((N n : ℝ) * (1 - Real.log 2))
  dsimp [c]
  field_simp [hN, hcpos.ne']

theorem exactToTextbookScale_tendsto_one :
    Tendsto Ex1443.exactToTextbookScale atTop (𝓝 (1 : ℝ)) := by
  have hsqrt := (Real.continuous_sqrt.tendsto (1 : ℝ)).comp
    totalVariance_div_asymptoticVarianceScale_tendsto_one
  have hsqrt' : Tendsto
      (fun n ↦ Real.sqrt
        (Ex1443.totalVariance n / ex_14_4_3_asymptoticVarianceScale n))
      atTop (𝓝 (1 : ℝ)) := by
    change Tendsto
      (fun n ↦ Real.sqrt
        (Ex1443.totalVariance n / ex_14_4_3_asymptoticVarianceScale n))
      atTop (𝓝 (Real.sqrt (1 : ℝ))) at hsqrt
    simpa using hsqrt
  apply hsqrt'.congr'
  filter_upwards with n
  unfold Ex1443.exactToTextbookScale
  rw [Real.sqrt_div' _ (Ex1443.asymptoticVarianceScale_pos n).le]

lemma upper_log_error_bound {ell NN : ℝ}
    (hell : 1 ≤ ell) (hlo : 2 * ell ≤ NN) (hhi : NN ≤ 2 * ell + 1) :
    NN * (Real.log (NN / ell) - Real.log 2) ≤ 2 := by
  have hell0 : 0 < ell := zero_lt_one.trans_le hell
  have hNN0 : 0 < NN := lt_of_lt_of_le (mul_pos (by norm_num) hell0) hlo
  have hr0 : 0 < NN / (2 * ell) :=
    div_pos hNN0 (mul_pos (by norm_num) hell0)
  have heq : Real.log (NN / ell) - Real.log 2 =
      Real.log (NN / (2 * ell)) := by
    rw [Real.log_div hNN0.ne' hell0.ne', Real.log_div hNN0.ne'
      (mul_ne_zero (by norm_num) hell0.ne'),
      Real.log_mul (by norm_num) hell0.ne']
    ring
  rw [heq]
  calc
    NN * Real.log (NN / (2 * ell)) ≤ NN * (NN / (2 * ell) - 1) :=
      mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hr0) hNN0.le
    _ = NN * (NN - 2 * ell) / (2 * ell) := by field_simp
    _ ≤ 2 := by
      rw [div_le_iff₀ (mul_pos (by norm_num) hell0)]
      have hd0 : 0 ≤ NN - 2 * ell := sub_nonneg.mpr hlo
      have hd1 : NN - 2 * ell ≤ 1 := by linarith
      have hNN3 : NN ≤ 3 * ell := by linarith
      have hp : NN * (NN - 2 * ell) ≤ (3 * ell) * 1 :=
        mul_le_mul hNN3 hd1 hd0 (by linarith)
      nlinarith

lemma lower_log_error_bound {ell NN : ℝ}
    (hell : 1 ≤ ell) (hlo : 2 * ell ≤ NN) (hhi : NN ≤ 2 * ell + 1) :
    NN * (Real.log 2 - Real.log ((NN + 1) / (ell + 1))) ≤ 1 := by
  have hell0 : 0 < ell := zero_lt_one.trans_le hell
  have hNN0 : 0 < NN := lt_of_lt_of_le (mul_pos (by norm_num) hell0) hlo
  have hell10 : 0 < ell + 1 := by linarith
  have hNN10 : 0 < NN + 1 := by linarith
  have hr0 : 0 < 2 * (ell + 1) / (NN + 1) :=
    div_pos (mul_pos (by norm_num) hell10) hNN10
  have heq : Real.log 2 - Real.log ((NN + 1) / (ell + 1)) =
      Real.log (2 * (ell + 1) / (NN + 1)) := by
    rw [Real.log_div hNN10.ne' hell10.ne', Real.log_div
      (mul_ne_zero (by norm_num) hell10.ne') hNN10.ne',
      Real.log_mul (by norm_num) hell10.ne']
    ring
  rw [heq]
  calc
    NN * Real.log (2 * (ell + 1) / (NN + 1)) ≤
        NN * (2 * (ell + 1) / (NN + 1) - 1) :=
      mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hr0) hNN0.le
    _ = NN * (2 * ell + 1 - NN) / (NN + 1) := by field_simp <;> ring
    _ ≤ 1 := by
      rw [div_le_iff₀ hNN10]
      have hd1 : 2 * ell + 1 - NN ≤ 1 := by linarith
      have hp : NN * (2 * ell + 1 - NN) ≤ NN * 1 :=
        mul_le_mul_of_nonneg_left hd1 hNN0.le
      nlinarith

theorem scaled_reciprocalTail_error_bounded (n : ℕ) :
    -1 ≤ (N n : ℝ) * (reciprocalTail n - Real.log 2) ∧
      (N n : ℝ) * (reciprocalTail n - Real.log 2) ≤ 2 := by
  have hell : (1 : ℝ) ≤ (L n : ℝ) := by exact_mod_cast L_pos n
  have hlo : 2 * (L n : ℝ) ≤ (N n : ℝ) := by
    exact_mod_cast two_mul_L_le_N n
  have hhi : (N n : ℝ) ≤ 2 * (L n : ℝ) + 1 := by
    exact_mod_cast N_le_two_mul_L_add_one n
  have hN0 : (0 : ℝ) ≤ (N n : ℝ) := by positivity
  have hlow := lower_log_error_bound hell hlo hhi
  have hupp := upper_log_error_bound hell hlo hhi
  have htlo : Real.log (((N n : ℝ) + 1) / ((L n : ℝ) + 1)) ≤
      reciprocalTail n := by
    simpa only [Nat.cast_add, Nat.cast_one] using reciprocalTail_lower n
  constructor
  · have hgap : (N n : ℝ) * (Real.log 2 - reciprocalTail n) ≤
        (N n : ℝ) * (Real.log 2 -
          Real.log (((N n : ℝ) + 1) / ((L n : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left htlo _) hN0
    nlinarith
  · exact (mul_le_mul_of_nonneg_left
      (sub_le_sub_right (reciprocalTail_upper n) _) hN0).trans hupp

theorem couponMean_sub_asymptoticMeanScale_eq_scaled_tail (n : ℕ) :
    ex_14_4_3_couponMean n - ex_14_4_3_asymptoticMeanScale n =
      (N n : ℝ) * (reciprocalTail n - Real.log 2) := by
  rw [couponMean_eq_N_mul_reciprocalTail]
  unfold ex_14_4_3_asymptoticMeanScale
  change
    (N n : ℝ) * reciprocalTail n - (N n : ℝ) * Real.log 2 =
      (N n : ℝ) * (reciprocalTail n - Real.log 2)
  ring

theorem asymptoticVarianceSqrt_tendsto_atTop :
    Tendsto
      (fun n ↦ Real.sqrt (ex_14_4_3_asymptoticVarianceScale n))
      atTop atTop := by
  have hc : 0 < (1 - Real.log 2) := by
    linarith [Real.log_two_lt_d9]
  have hscale : Tendsto (fun n ↦ (N n : ℝ) * (1 - Real.log 2))
      atTop atTop := N_real_tendsto_atTop.atTop_mul_const hc
  have hsqrt := Real.tendsto_sqrt_atTop.comp hscale
  change Tendsto
    (fun n ↦ Real.sqrt ((N n : ℝ) * (1 - Real.log 2))) atTop atTop at hsqrt
  change Tendsto
    (fun n ↦ Real.sqrt ((N n : ℝ) * (1 - Real.log 2))) atTop atTop
  exact hsqrt

theorem exactToTextbookShift_tendsto_zero :
    Tendsto Ex1443.exactToTextbookShift atTop (𝓝 (0 : ℝ)) := by
  have hzero := tendsto_bdd_div_atTop_nhds_zero
    (Eventually.of_forall fun n ↦ (scaled_reciprocalTail_error_bounded n).1)
    (Eventually.of_forall fun n ↦ (scaled_reciprocalTail_error_bounded n).2)
    asymptoticVarianceSqrt_tendsto_atTop
  apply hzero.congr'
  filter_upwards with n
  unfold Ex1443.exactToTextbookShift
  rw [couponMean_sub_asymptoticMeanScale_eq_scaled_tail]

theorem textbookNormalizedValue_eq_affine_exact_tail
    (n : ℕ)
    (ω : Prob63Support.CouponStageΩ
      (ex_14_4_3_targetDistinct (shiftedSourceIndex n))) :
    ex_14_4_3_normalizedCouponValue (shiftedSourceIndex n)
        (Prob63Support.couponCollectionTimeReal
          (ex_14_4_3_couponTypes (shiftedSourceIndex n))
          (ex_14_4_3_targetDistinct (shiftedSourceIndex n)) ω) =
      exactToTextbookScale (shiftedSourceIndex n) *
          exactCouponStageStandardizedValue (shiftedSourceIndex n) ω +
        exactToTextbookShift (shiftedSourceIndex n) := by
  have hvar : 0 < totalVariance (shiftedSourceIndex n) := by
    exact shiftedTotalVariance_pos n
  have hexact : Real.sqrt (totalVariance (shiftedSourceIndex n)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hvar)
  have hasym :
      Real.sqrt
          (ex_14_4_3_asymptoticVarianceScale (shiftedSourceIndex n)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2
      (asymptoticVarianceScale_pos (shiftedSourceIndex n)))
  unfold ex_14_4_3_normalizedCouponValue exactToTextbookScale
    exactCouponStageStandardizedValue exactToTextbookShift
  field_simp [hexact, hasym]
  ring

theorem map_prod_diracProba_affine
    (ν : ProbabilityMeasure ℝ) (a b : ℝ) :
    ProbabilityMeasure.map (ν.prod (diracProba (a, b)))
        ((by fun_prop) : AEMeasurable
          (fun z : ℝ × (ℝ × ℝ) => z.2.1 * z.1 + z.2.2)
          ((ν.prod (diracProba (a, b)) : ProbabilityMeasure _) : Measure _)) =
      ProbabilityMeasure.map ν
        ((by fun_prop) : AEMeasurable (fun x : ℝ => a * x + b) (ν : Measure ℝ)) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map
      (fun z : ℝ × (ℝ × ℝ) => z.2.1 * z.1 + z.2.2)
      ((ν : Measure ℝ).prod (Measure.dirac (a, b))) =
    Measure.map (fun x : ℝ => a * x + b) (ν : Measure ℝ)
  rw [Measure.prod_dirac, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem map_affine_one_zero (ν : ProbabilityMeasure ℝ) :
    ProbabilityMeasure.map ν
        ((by fun_prop) : AEMeasurable (fun x : ℝ => 1 * x + 0) (ν : Measure ℝ)) = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun x : ℝ => 1 * x + 0) (ν : Measure ℝ) = (ν : Measure ℝ)
  simpa only [one_mul, add_zero] using (Measure.map_id' (μ := (ν : Measure ℝ)))

theorem tendsto_map_affine
    {ι : Type*} {l : Filter ι}
    (νs : ι → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (a b : ι → ℝ)
    (hν : Tendsto νs l (𝓝 ν))
    (ha : Tendsto a l (𝓝 1))
    (hb : Tendsto b l (𝓝 0)) :
    Tendsto
      (fun n => ProbabilityMeasure.map (νs n)
        ((by fun_prop) : AEMeasurable (fun x : ℝ => a n * x + b n)
          (νs n : Measure ℝ)))
      l (𝓝 ν) := by
  have hp : Tendsto (fun n => (a n, b n)) l (𝓝 ((1 : ℝ), (0 : ℝ))) :=
    ha.prodMk_nhds hb
  have hd : Tendsto (fun n => diracProba (a n, b n)) l
      (𝓝 (diracProba ((1 : ℝ), (0 : ℝ)))) :=
    Filter.Tendsto.comp continuous_diracProba.continuousAt hp
  have hprod : Tendsto
      (fun n => (νs n).prod (diracProba (a n, b n))) l
      (𝓝 (ν.prod (diracProba ((1 : ℝ), (0 : ℝ))))) :=
    Filter.Tendsto.comp ProbabilityMeasure.continuous_prod.continuousAt
      (hν.prodMk_nhds hd)
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => (νs n).prod (diracProba (a n, b n)))
    (ν.prod (diracProba ((1 : ℝ), (0 : ℝ)))) hprod
    (by fun_prop : Continuous
      (fun z : ℝ × (ℝ × ℝ) => z.2.1 * z.1 + z.2.2))
  rw [show (fun n => ProbabilityMeasure.map ((νs n).prod (diracProba (a n, b n)))
      ((by fun_prop) : AEMeasurable
        (fun z : ℝ × (ℝ × ℝ) => z.2.1 * z.1 + z.2.2)
        (((νs n).prod (diracProba (a n, b n)) : ProbabilityMeasure _) : Measure _))) =
      (fun n => ProbabilityMeasure.map (νs n)
        ((by fun_prop) : AEMeasurable (fun x : ℝ => a n * x + b n)
          (νs n : Measure ℝ))) by
        funext n
        exact map_prod_diracProba_affine (νs n) (a n) (b n)] at hmap
  rw [map_prod_diracProba_affine, map_affine_one_zero] at hmap
  exact hmap

theorem textbookNormalizedCouponLaw_eq_affine_exact_tail (n : ℕ) :
    textbookNormalizedCouponLaw (shiftedSourceIndex n) =
      ProbabilityMeasure.map
        (exactCouponStageStandardizedLaw (shiftedSourceIndex n))
        ((by fun_prop) :
          AEMeasurable
            (fun x : ℝ =>
              exactToTextbookScale (shiftedSourceIndex n) * x +
                exactToTextbookShift (shiftedSourceIndex n))
            ((exactCouponStageStandardizedLaw (shiftedSourceIndex n) :
              ProbabilityMeasure ℝ) : Measure ℝ)) := by
  let k := shiftedSourceIndex n
  let μ : Measure (Prob63Support.CouponStageΩ (ex_14_4_3_targetDistinct k)) :=
    (couponStageProductLaw k : Measure _)
  let T : Prob63Support.CouponStageΩ (ex_14_4_3_targetDistinct k) → ℝ :=
    Prob63Support.couponCollectionTimeReal
      (ex_14_4_3_couponTypes k) (ex_14_4_3_targetDistinct k)
  let Z : Prob63Support.CouponStageΩ (ex_14_4_3_targetDistinct k) → ℝ :=
    exactCouponStageStandardizedValue k
  let f : ℝ → ℝ := ex_14_4_3_normalizedCouponValue k
  let g : ℝ → ℝ := fun x : ℝ =>
    exactToTextbookScale k * x + exactToTextbookShift k
  have hT : Measurable T := by
    unfold T
    exact measurable_of_countable _
  have hZ : Measurable Z := by
    unfold Z
    exact measurable_of_countable _
  have hf : Measurable f := by
    unfold f ex_14_4_3_normalizedCouponValue
    fun_prop
  have hg : Measurable g := by
    unfold g
    fun_prop
  have hpoint : f ∘ T =ᵐ[μ] g ∘ Z := by
    filter_upwards with ω
    exact textbookNormalizedValue_eq_affine_exact_tail n ω
  unfold textbookNormalizedCouponLaw couponCollectionLaw
    exactCouponStageStandardizedLaw
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map f (Measure.map T μ) = Measure.map g (Measure.map Z μ)
  rw [Measure.map_map hf hT, Measure.map_map hg hZ]
  exact Measure.map_congr hpoint

theorem textbookNormalizedCouponLaw_converges :
    Tendsto textbookNormalizedCouponLaw atTop
      (𝓝 Thm148Core.Setup.standardNormalLaw) := by
  have hν : Tendsto
      (fun n ↦ exactCouponStageStandardizedLaw (shiftedSourceIndex n))
      atTop (𝓝 Thm148Core.Setup.standardNormalLaw) :=
    exactCouponStageStandardizedLaw_converges.comp
      (tendsto_add_atTop_nat 1)
  have ha : Tendsto
      (fun n ↦ exactToTextbookScale (shiftedSourceIndex n))
      atTop (𝓝 (1 : ℝ)) :=
    exactToTextbookScale_tendsto_one.comp (tendsto_add_atTop_nat 1)
  have hb : Tendsto
      (fun n ↦ exactToTextbookShift (shiftedSourceIndex n))
      atTop (𝓝 (0 : ℝ)) :=
    exactToTextbookShift_tendsto_zero.comp (tendsto_add_atTop_nat 1)
  have haffine := tendsto_map_affine
    (fun n ↦ exactCouponStageStandardizedLaw (shiftedSourceIndex n))
    Thm148Core.Setup.standardNormalLaw
    (fun n ↦ exactToTextbookScale (shiftedSourceIndex n))
    (fun n ↦ exactToTextbookShift (shiftedSourceIndex n))
    hν ha hb
  have htail : Tendsto
      (fun n ↦ textbookNormalizedCouponLaw (shiftedSourceIndex n))
      atTop (𝓝 Thm148Core.Setup.standardNormalLaw) := by
    apply haffine.congr'
    filter_upwards with n
    exact (textbookNormalizedCouponLaw_eq_affine_exact_tail n).symm
  simpa [shiftedSourceIndex] using
    (tendsto_add_atTop_iff_nat
      (f := textbookNormalizedCouponLaw) 1).1 htail

end Ex1443

abbrev ex_14_4_3_couponCollectionLaws : ℕ → ProbabilityMeasure ℝ :=
  Ex1443.couponCollectionLaw

abbrev ex_14_4_3_normalizedCouponLaws : ℕ → ProbabilityMeasure ℝ :=
  Ex1443.textbookNormalizedCouponLaw

theorem ex_14_4_3_textbook_normalization :
    ex_14_4_3_TextbookNormalization
      ex_14_4_3_couponCollectionLaws ex_14_4_3_normalizedCouponLaws :=
  Ex1443.textbook_normalization

def ex_14_4_3_ExactNormalizedConvergence : Prop :=
  Tendsto Ex1443.exactCouponStageStandardizedLaw atTop
    (𝓝 Thm148Core.Setup.standardNormalLaw)

theorem ex_14_4_3_exact_normalized_clt :
    ex_14_4_3_ExactNormalizedConvergence :=
  Ex1443.exactCouponStageStandardizedLaw_converges

def ex_14_4_3_TextbookNormalizedConvergence : Prop :=
  ex_14_4_3_TextbookNormalization
      ex_14_4_3_couponCollectionLaws ex_14_4_3_normalizedCouponLaws ∧
    Tendsto ex_14_4_3_normalizedCouponLaws atTop
      (𝓝 Thm148Core.Setup.standardNormalLaw)

theorem ex_14_4_3_textbook_normalized_clt :
    ex_14_4_3_TextbookNormalizedConvergence := by
  exact ⟨ex_14_4_3_textbook_normalization,
    Ex1443.textbookNormalizedCouponLaw_converges⟩

theorem ex_14_4_3 :
    ex_14_4_3_TextbookNormalizedConvergence :=
  ex_14_4_3_textbook_normalized_clt
