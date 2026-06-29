import Mathlib
import ToyApollo.Output.def_5_10
import ToyApollo.Output.thm_5_8
import ToyApollo.Output.thm_10_1
import ToyApollo.Output.thm_11_2

/-
TASK ID: prob_11_5
TYPE: Problem
SOURCE PLAN: chapter11-problems
TASK CONTENT:
\textbf{11.5.} Suppose that Xk ,f o r k = 1, 2, 3,... , are independent random variables with

zero mean and variance V ar (Xk) \leq c

\sqrt

k for some positive constant c. Prove that

Xn/n converges almost surely to zero as n \to\infty .
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option maxHeartbeats 800000

/-- The scaled sequence from Problem 11.5, written with `n + 1` in the denominator
so the natural-number indexing has no zero denominator. -/
noncomputable def prob_11_5_scaledSeq {Ω : Type*} (X : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ :=
  fun n ω => X n ω / ((n : ℝ) + 1)

/-- The tail-summability support needed after applying Chebyshev's inequality.

In the textbook this follows from `Var(X_n) <= c sqrt n`, because the resulting
bound is a constant multiple of `n^(-3/2)`.  The local formalization keeps that
p-series comparison as explicit support instead of rebuilding a general
real/ENNReal p-series library inside this problem. -/
def prob_11_5_tailSummabilitySupport {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (∑' n : ℕ,
      P (almostSureDeviationEvent (prob_11_5_scaledSeq X) (fun _ : Ω => 0) n ε)) ≠ ∞

/-- One Chebyshev step in Problem 11.5: the scaled tail event is controlled by
the variance of `X_n` divided by the square of the scaling denominator. -/
theorem prob_11_5_scaled_tail_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (n : ℕ) (hX : MemLp (X n) 2 P) (hMean : P[X n] = 0)
    {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ |prob_11_5_scaledSeq X n ω - 0|} ≤
      _root_.variance P (X n) / (((n : ℝ) + 1) ^ 2 * ε ^ 2) := by
  have hNpos : 0 < (n : ℝ) + 1 := by positivity
  have hThreshold : 0 < ((n : ℝ) + 1) * ε := mul_pos hNpos hε
  have hCheb :
      P.real {ω | ((n : ℝ) + 1) * ε ≤ |X n ω - P[X n]|} ≤
        _root_.variance P (X n) / (((n : ℝ) + 1) * ε) ^ 2 := by
    exact thm_11_2 P (X n) hX hThreshold
  have hsubset :
      {ω | ε ≤ |prob_11_5_scaledSeq X n ω - 0|} ⊆
        {ω | ((n : ℝ) + 1) * ε ≤ |X n ω - P[X n]|} := by
    intro ω hω
    have hω' : ε ≤ |X n ω| / ((n : ℝ) + 1) := by
      simpa [prob_11_5_scaledSeq, sub_zero, abs_div, abs_of_pos hNpos] using hω
    have hmul := mul_le_mul_of_nonneg_right hω' hNpos.le
    have hcancel : |X n ω| / ((n : ℝ) + 1) * ((n : ℝ) + 1) = |X n ω| := by
      exact div_mul_cancel₀ _ hNpos.ne'
    have hscaled : ((n : ℝ) + 1) * ε ≤ |X n ω| := by
      nlinarith [hmul, hcancel]
    simpa [hMean, sub_zero] using hscaled
  have hmeasure :
      P.real {ω | ε ≤ |prob_11_5_scaledSeq X n ω - 0|} ≤
        P.real {ω | ((n : ℝ) + 1) * ε ≤ |X n ω - P[X n]|} :=
    measureReal_mono (μ := P) hsubset
  calc
    P.real {ω | ε ≤ |prob_11_5_scaledSeq X n ω - 0|}
        ≤ P.real {ω | ((n : ℝ) + 1) * ε ≤ |X n ω - P[X n]|} := hmeasure
    _ ≤ _root_.variance P (X n) / (((n : ℝ) + 1) * ε) ^ 2 := hCheb
    _ = _root_.variance P (X n) / (((n : ℝ) + 1) ^ 2 * ε ^ 2) := by
      ring_nf

/-- The elementary p-series estimate used in Problem 11.5.  This is the
Mathlib-facing form of Tao's comparison with `n^(-3/2)`. -/
theorem prob_11_5_pseries_bound_ne_top (C : ℝ) (hC : 0 ≤ C) :
    (∑' n : ℕ, ENNReal.ofReal (C * (1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ)))) ≠ ∞ := by
  have hs0 : Summable fun n : ℕ => 1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ) := by
    exact (Real.summable_one_div_nat_add_rpow 1 (3 / 2 : ℝ)).2 (by norm_num)
  have hs : Summable fun n : ℕ => C * (1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ)) := by
    exact hs0.mul_left C
  have hnonneg : ∀ n : ℕ, 0 ≤ C * (1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ)) := by
    intro n
    exact mul_nonneg hC (by positivity)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hs]
  exact ENNReal.ofReal_ne_top

/-- Chebyshev's inequality, rewritten for the strict deviation event used by
Theorem 10.1. -/
theorem prob_11_5_deviation_event_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (n : ℕ) (hX : MemLp (X n) 2 P) (hMean : P[X n] = 0)
    {ε : ℝ} (hε : 0 < ε) :
    P (almostSureDeviationEvent (prob_11_5_scaledSeq X) (fun _ : Ω => 0) n ε) ≤
      ENNReal.ofReal
        (_root_.variance P (X n) / (((n : ℝ) + 1) ^ 2 * ε ^ 2)) := by
  have hreal := prob_11_5_scaled_tail_bound P X n hX hMean hε
  have hfinite :
      P (almostSureDeviationEvent (prob_11_5_scaledSeq X) (fun _ : Ω => 0) n ε) ≠ ∞ := by
    exact measure_ne_top P _
  rw [← MeasureTheory.ofReal_measureReal hfinite]
  have hsubset :
      almostSureDeviationEvent (prob_11_5_scaledSeq X) (fun _ : Ω => 0) n ε ⊆
        {ω | ε ≤ |prob_11_5_scaledSeq X n ω - 0|} := by
    intro ω hω
    simpa [sub_zero] using le_of_lt (by simpa [almostSureDeviationEvent] using hω)
  have hmono :
      P.real (almostSureDeviationEvent (prob_11_5_scaledSeq X) (fun _ : Ω => 0) n ε) ≤
        P.real {ω | ε ≤ |prob_11_5_scaledSeq X n ω - 0|} := by
    exact measureReal_mono (μ := P) hsubset
  exact ENNReal.ofReal_le_ofReal (le_trans hmono hreal)

/-- The variance-growth hypothesis from the problem implies the summability of
the Chebyshev tail probabilities. -/
theorem prob_11_5_tailSummability_of_variance_growth {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hMemLp : ∀ n : ℕ, MemLp (X n) 2 P)
    (hMean : ∀ n : ℕ, P[X n] = 0)
    (hVarGrowth : ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, _root_.variance P (X n) ≤ c * Real.sqrt ((n : ℝ) + 1)) :
    prob_11_5_tailSummabilitySupport P X := by
  rcases hVarGrowth with ⟨c, hc, hVar⟩
  intro ε hε
  let C : ℝ := c / ε ^ 2
  have hC : 0 ≤ C := div_nonneg hc.le (sq_nonneg ε)
  have hseries :
      (∑' n : ℕ, ENNReal.ofReal (C * (1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ)))) ≠ ∞ :=
    prob_11_5_pseries_bound_ne_top C hC
  refine ne_top_of_le_ne_top hseries ?_
  refine ENNReal.tsum_le_tsum fun n => ?_
  have htail :
      P (almostSureDeviationEvent (prob_11_5_scaledSeq X) (fun _ : Ω => 0) n ε) ≤
        ENNReal.ofReal
          (_root_.variance P (X n) / (((n : ℝ) + 1) ^ 2 * ε ^ 2)) := by
    exact prob_11_5_deviation_event_bound P X n (hMemLp n) (hMean n) hε
  refine le_trans htail ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hden_nonneg : 0 ≤ ((n : ℝ) + 1) ^ 2 * ε ^ 2 := by positivity
  have hdiv :
      _root_.variance P (X n) / (((n : ℝ) + 1) ^ 2 * ε ^ 2) ≤
        (c * Real.sqrt ((n : ℝ) + 1)) / (((n : ℝ) + 1) ^ 2 * ε ^ 2) := by
    exact div_le_div_of_nonneg_right (hVar n) hden_nonneg
  have halg :
      (c * Real.sqrt ((n : ℝ) + 1)) / (((n : ℝ) + 1) ^ 2 * ε ^ 2) =
        C * (1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ)) := by
    have hx : 0 < (n : ℝ) + 1 := by positivity
    rw [Real.sqrt_eq_rpow]
    rw [abs_of_pos hx]
    field_simp [C, hx.ne', hε.ne']
    dsimp [C]
    rw [mul_assoc, ← Real.rpow_add hx]
    rw [← Real.rpow_natCast]
    norm_num
    field_simp [hε.ne']
  exact le_trans hdiv (le_of_eq halg)

/-- Borel-Cantelli plus Theorem 10.1 turns the summable Chebyshev tail bounds
into almost-sure convergence. -/
private theorem prob_11_5_of_tail_summability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hTail : prob_11_5_tailSummabilitySupport P X) :
    ConvergesAlmostSurely P (prob_11_5_scaledSeq X) (fun _ => 0) := by
  refine (thm_10_1 P (prob_11_5_scaledSeq X) (fun _ : Ω => 0)).2 ?_
  intro ε hε
  simpa [prob_11_5_tailSummabilitySupport, deviationInfinitelyOften] using
    (thm_5_8 P
      (fun n : ℕ =>
        almostSureDeviationEvent (prob_11_5_scaledSeq X) (fun _ : Ω => 0) n ε)
      (hTail ε hε))

/-- Problem 11.5: under the printed zero-mean and variance-growth assumptions,
the scaled variables `X_n / n` converge almost surely to zero.

The Chebyshev tail bound is formalized above.  The textbook calculus step,
comparison with the summable p-series `sum n^(-3/2)`, is discharged by
`prob_11_5_tailSummability_of_variance_growth`; from that point
Borel-Cantelli and Theorem 10.1 finish the proof. -/
theorem prob_11_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (_hInd : def_5_10_randomVariables P X)
    (hMemLp : ∀ n : ℕ, MemLp (X n) 2 P)
    (hMean : ∀ n : ℕ, P[X n] = 0)
    (hVarGrowth : ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, _root_.variance P (X n) ≤ c * Real.sqrt ((n : ℝ) + 1)) :
    ConvergesAlmostSurely P (prob_11_5_scaledSeq X) (fun _ => 0) := by
  exact prob_11_5_of_tail_summability P X
    (prob_11_5_tailSummability_of_variance_growth P X hMemLp hMean hVarGrowth)
