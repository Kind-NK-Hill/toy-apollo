import Mathlib

/-!
Foundational triangular-array notation support for Chapter 14.

This file owns the task-neutral row-length and variance notation introduced
immediately before Theorem 14.8.  It deliberately avoids importing the Poisson
example or the theorem statement itself.
-/

open Filter
open scoped BigOperators Topology

noncomputable section

/-- The triangular-array row and variance notation introduced before Theorem
14.8.  It records row lengths `k_n`, cell variances `σ_{n,i}^2`, row variances
`s_n^2`, and the source assumption `s_n^2 -> ∞`. -/
structure chapter14_TriangularArrayNotation where
  rowLength : ℕ → ℕ
  rowLength_pos : ∀ n : ℕ, 0 < rowLength n
  variance : ∀ n : ℕ, Fin (rowLength n) → ℝ
  totalVariance : ℕ → ℝ
  totalVariance_eq :
    ∀ n : ℕ, totalVariance n = ∑ i : Fin (rowLength n), variance n i
  totalVariance_tendsto_atTop :
    Tendsto totalVariance atTop atTop
