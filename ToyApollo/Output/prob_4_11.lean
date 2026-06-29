/-
TASK ID: prob_4_11
TYPE: Problem
SOURCE PLAN: 12_chap4_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open Filter Topology

theorem prob_4_11 (a : ℕ → ℝ) (h_nonneg : ∀ k, 0 ≤ a k)
    (h_limsup : limsup (fun k => (a k : EReal)) atTop = (0 : EReal)) :
    Tendsto a atTop (𝓝 0) := by
  rw [← EReal.tendsto_coe]
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_ ?_ ?_
  · exact le_liminf_of_le (by isBoundedDefault)
      (Eventually.of_forall fun k => by exact_mod_cast h_nonneg k)
  · rw [h_limsup]
    norm_num
  · isBoundedDefault
  · isBoundedDefault
