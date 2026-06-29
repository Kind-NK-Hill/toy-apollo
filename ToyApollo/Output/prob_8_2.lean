import Mathlib

/-
TASK ID: prob_8_2
TYPE: Problem
SOURCE PLAN: 35_chap8_problems
TASK CONTENT:
\textbf{8.2.} Apply Fubini's theorem to prove that the order of summation in $\sum_{i=0}^{\infty}\sum_{j=0}^{\infty} a_{ij}$ is irrelevant if $\sum_{i=0}^{\infty}\sum_{j=0}^{\infty} |a_{ij}|$ is finite.
-/

-- WRITE FINAL LEAN CODE BELOW

theorem prob_8_2 (a : ℕ → ℕ → ℝ)
    (h : Summable (Function.uncurry fun i j => |a i j|)) :
    (∑' i : ℕ, ∑' j : ℕ, a i j) = (∑' j : ℕ, ∑' i : ℕ, a i j) := by
  have ha : Summable (Function.uncurry a) := by
    rw [← summable_norm_iff]
    simpa [Function.uncurry, Real.norm_eq_abs] using h
  simpa [Function.uncurry] using (Summable.tsum_comm ha).symm
