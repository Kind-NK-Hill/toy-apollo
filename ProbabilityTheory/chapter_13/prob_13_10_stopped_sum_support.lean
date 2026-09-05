/-
TASK ID: prob_13_10_stopped_sum_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.common_support.chapter13_stopping_support

open MeasureTheory
open scoped BigOperators

noncomputable section




 
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



theorem prob_13_10_stoppedSum_centered_eq {Ω : Type*}
    (X : ℕ → Ω → ℝ) (τ : Ω → ℕ) (μ : ℝ) (ω : Ω) :
    prob_13_10_stoppedSum (fun n ω => X n ω - μ) τ ω =
      prob_13_10_stoppedSum X τ ω - μ * (τ ω : ℝ) := by
  simpa [prob_13_10_stoppedSum] using
    chapter13_stoppedSum_centered_eq X τ μ ω

 
theorem prob_13_10_stoppedSum_eq_sum_indicator_range {Ω : Type*}
    (X : ℕ → Ω → ℝ) (τ : Ω → ℕ) (N : ℕ) {ω : Ω}
    (hτN : τ ω ≤ N) :
    prob_13_10_stoppedSum X τ ω =
      ∑ k ∈ Finset.range N,
        if k < τ ω then X (k + 1) ω else (0 : ℝ) := by
  simpa [prob_13_10_stoppedSum] using
    chapter13_stoppedNatSum_eq_sum_indicator_range X τ N hτN
