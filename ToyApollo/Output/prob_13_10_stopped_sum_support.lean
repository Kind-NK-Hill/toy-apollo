import Mathlib
import ToyApollo.Output.chapter13_stopping_support

open MeasureTheory
open scoped BigOperators

noncomputable section

/-!
Problem 13.10 compatibility wrappers for reusable Chapter 13 stopped-sum
support.
-/

/-- Problem-local name for the shared one-indexed stopped sum. -/
def prob_13_10_stoppedSum {Ω : Type*}
    (X : ℕ → Ω → ℝ) (τ : Ω → ℕ) : Ω → ℝ :=
  chapter13_stoppedNatSum X τ

@[simp]
theorem prob_13_10_stoppedSum_zero {Ω : Type*}
    (X : ℕ → Ω → ℝ) (τ : Ω → ℕ) {ω : Ω}
    (hτ : τ ω = 0) :
    prob_13_10_stoppedSum X τ ω = 0 := by
  simpa [prob_13_10_stoppedSum] using
    chapter13_stoppedNatSum_zero X τ hτ

theorem prob_13_10_stoppedSum_succ {Ω : Type*}
    (X : ℕ → Ω → ℝ) (τ : Ω → ℕ) {ω : Ω} {n : ℕ}
    (hτ : τ ω = n + 1) :
    prob_13_10_stoppedSum X τ ω =
      prob_13_10_stoppedSum X (fun _ => n) ω + X (n + 1) ω := by
  simpa [prob_13_10_stoppedSum] using
    chapter13_stoppedNatSum_succ X τ hτ

/-- Centering commutes with the stopped finite sum:
`sum_{k < τ} (X_{k+1} - μ) = sum_{k < τ} X_{k+1} - μ τ`. -/
theorem prob_13_10_stoppedSum_centered_eq {Ω : Type*}
    (X : ℕ → Ω → ℝ) (τ : Ω → ℕ) (μ : ℝ) (ω : Ω) :
    prob_13_10_stoppedSum (fun n ω => X n ω - μ) τ ω =
      prob_13_10_stoppedSum X τ ω - μ * (τ ω : ℝ) := by
  simpa [prob_13_10_stoppedSum] using
    chapter13_stoppedSum_centered_eq X τ μ ω

/-- A fixed finite prefix form of the stopped sum. -/
theorem prob_13_10_stoppedSum_eq_sum_indicator_range {Ω : Type*}
    (X : ℕ → Ω → ℝ) (τ : Ω → ℕ) (N : ℕ) {ω : Ω}
    (hτN : τ ω ≤ N) :
    prob_13_10_stoppedSum X τ ω =
      ∑ k ∈ Finset.range N,
        if k < τ ω then X (k + 1) ω else (0 : ℝ) := by
  simpa [prob_13_10_stoppedSum] using
    chapter13_stoppedNatSum_eq_sum_indicator_range X τ N hτN
