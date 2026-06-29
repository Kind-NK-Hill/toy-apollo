/-
TASK ID: prob_4_1
TYPE: Problem
SOURCE PLAN: 12_chap4_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

theorem prob_4_1 {Ω : Type _} [MeasurableSpace Ω] (f : Ω → ℝ)
    (h :
      (∀ a : ℝ, MeasurableSet (f ⁻¹' Set.Iio a)) ∨
        (∀ a : ℝ, MeasurableSet (f ⁻¹' Set.Iic a))) :
    Measurable f := by
  rcases h with h1 | h2
  · exact measurable_of_Iio h1
  · exact measurable_of_Iic h2
