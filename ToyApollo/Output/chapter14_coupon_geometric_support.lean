import Mathlib
import ToyApollo.Output.prob_6_3

/-!
Foundational geometric coupon-stage support for Chapter 14.

This file owns the task-neutral geometric waiting-time formulas shared by
Example 14.4.3 and Problem 14.11. It deliberately does not import Theorem 14.8.
-/

open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

noncomputable section

/-- The geometric moment-generating function displayed in the source text. -/
def chapter14_geometricMgf (p t : ℝ) : ℝ :=
  p * Real.exp t / (1 - (1 - p) * Real.exp t)

/-- The geometric MGF series sums to the displayed closed form on its natural
domain of convergence. -/
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
  convert hgeom using 1
  · ext m
    rw [ProbabilityTheory.geometricPMFReal]
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

/-- The mean of a geometric waiting time with success probability `p`. -/
def chapter14_geometricMean (p : ℝ) : ℝ :=
  1 / p

/-- The variance `(1-p)/p^2` of a geometric waiting time. -/
def chapter14_geometricVariance (p : ℝ) : ℝ :=
  (1 - p) / p ^ 2


/-- The centered fourth moment formula used for Lyapunov's condition. -/
def chapter14_geometricCenteredFourthMoment (p : ℝ) : ℝ :=
  (1 / p ^ 4) * (1 - p) * (p ^ 2 - 9 * p + 9)

/-- Closed form for `choose (m+2) 2`, cast to real numbers. -/
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

/-- Polynomial expansion of the centered second power into the binomial
series basis used by `hasSum_choose_mul_geometric_of_norm_lt_one`. -/
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

/-- The centered second moment of a zero-based geometric waiting time. -/
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
  convert hsum using 1
  · ext m
    rw [ProbabilityTheory.geometricPMFReal]
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
  · exact htarget.symm

theorem chapter14_geometric_centered_second_tsum_eq
    {p : ℝ} (hp_pos : 0 < p) (hp_le : p ≤ 1) :
    (∑' m : ℕ,
      (Prob63Support.scalarStageWait m - 1 / p) ^ 2 *
        ProbabilityTheory.geometricPMFReal p m) =
      chapter14_geometricVariance p := by
  simpa [Prob63Support.scalarStageWait] using
    (chapter14_geometric_centered_second_hasSum hp_pos hp_le).tsum_eq

/-- Closed form for `choose (m+3) 3`, cast to real numbers. -/
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

/-- Closed form for `choose (m+4) 4`, cast to real numbers. -/
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

/-- Polynomial expansion of the centered fourth power into the binomial
series basis used by `hasSum_choose_mul_geometric_of_norm_lt_one`. -/
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

/-- The geometric centered fourth moment is the `tsum` of the centered
fourth power against the zero-based geometric PMF. -/
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
  convert hsum using 1
  · ext m
    rw [ProbabilityTheory.geometricPMFReal]
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
  · exact htarget.symm

theorem chapter14_geometric_centered_fourth_tsum_eq
    {p : ℝ} (hp_pos : 0 < p) (hp_le : p ≤ 1) :
    (∑' m : ℕ,
      (Prob63Support.scalarStageWait m - 1 / p) ^ 4 *
        ProbabilityTheory.geometricPMFReal p m) =
      chapter14_geometricCenteredFourthMoment p := by
  simpa [Prob63Support.scalarStageWait] using
    (chapter14_geometric_centered_fourth_hasSum hp_pos hp_le).tsum_eq

/-- Summability needed to integrate the exponential in the MGF of one
concrete geometric coupon stage. -/
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
      simpa [Prob63Support.stageMeasure, Prob63Support.stagePMF] using
        (ProbabilityTheory.isProbabilityMeasure_geometricMeasure
          (p := Prob63Support.stageSuccessProb n i)
          (Prob63Support.stageSuccessProb_pos hk hkn i)
          (Prob63Support.stageSuccessProb_le_one hk hkn i))
    have hle :
        Prob63Support.stageMeasure n k hk hkn i {m} ≤
          Prob63Support.stageMeasure n k hk hkn i Set.univ := by
      exact measure_mono (by intro x hx; trivial)
    exact ne_of_lt (lt_of_le_of_lt (by simpa using hle) (by simp))
  · exact chapter14_couponStageMgfSummableNorm hk hkn i ht

/-- The concrete geometric coupon stage has the displayed MGF on its natural
domain of convergence. -/
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

/-- Summability needed to integrate the centered second stage wait over the
zero-based geometric stage measure from `prob_6_3`. -/
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
      simpa [Prob63Support.stageMeasure, Prob63Support.stagePMF] using
        (ProbabilityTheory.isProbabilityMeasure_geometricMeasure
          (p := Prob63Support.stageSuccessProb n i)
          (Prob63Support.stageSuccessProb_pos hk hkn i)
          (Prob63Support.stageSuccessProb_le_one hk hkn i))
    have hle :
        Prob63Support.stageMeasure n k hk hkn i {m} ≤
          Prob63Support.stageMeasure n k hk hkn i Set.univ := by
      exact measure_mono (by intro x hx; trivial)
    exact ne_of_lt (lt_of_le_of_lt (by simpa using hle) (by simp))
  · exact chapter14_couponStageCenteredSecondSummableNorm hk hkn i

/-- The centered second moment formula for the concrete geometric waiting
time stage measure inherited from `prob_6_3`. -/
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

/-- Summability needed to integrate the fourth centered stage wait over the
zero-based geometric stage measure from `prob_6_3`. -/
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
      simpa [Prob63Support.stageMeasure, Prob63Support.stagePMF] using
        (ProbabilityTheory.isProbabilityMeasure_geometricMeasure
          (p := Prob63Support.stageSuccessProb n i)
          (Prob63Support.stageSuccessProb_pos hk hkn i)
          (Prob63Support.stageSuccessProb_le_one hk hkn i))
    have hle :
        Prob63Support.stageMeasure n k hk hkn i {m} ≤
          Prob63Support.stageMeasure n k hk hkn i Set.univ := by
      exact measure_mono (by intro x hx; trivial)
    exact ne_of_lt (lt_of_le_of_lt (by simpa using hle) (by simp))
  · exact chapter14_couponStageCenteredFourthSummableNorm hk hkn i

/-- The centered fourth moment formula for the concrete geometric waiting
time stage measure inherited from `prob_6_3`. -/
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
