/-
TASK ID: prob_8_2
TYPE: Problem
SOURCE PLAN: 35_chap8_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib




-- WRITE FINAL LEAN CODE BELOW

theorem prob_8_2 (a : ℕ → ℕ → ℝ)
    (h : Summable (Function.uncurry fun i j => |a i j|)) :
    (∑' i : ℕ, ∑' j : ℕ, a i j) = (∑' j : ℕ, ∑' i : ℕ, a i j) := by
  have ha : Summable (Function.uncurry a) := by
    rw [← summable_norm_iff]
    change Summable (fun p : ℕ × ℕ => |a p.1 p.2|)
    exact h
  simpa [Function.uncurry] using (Summable.tsum_comm ha).symm
