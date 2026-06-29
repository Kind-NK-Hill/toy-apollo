/-
TASK ID: prob_4_5
TYPE: Problem
SOURCE PLAN: 12_chap4_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

theorem prob_4_5 (Ω : Type*) [MeasurableSpace Ω] (n : ℕ)
    (f : Fin n → Ω → ℝ) (hf : ∀ i, Measurable (f i))
    (g : (Fin n → ℝ) → ℝ) (hg : Continuous g) :
    Measurable (fun ω => g (fun i => f i ω)) := by
  exact hg.measurable.comp (measurable_pi_lambda _ hf)
