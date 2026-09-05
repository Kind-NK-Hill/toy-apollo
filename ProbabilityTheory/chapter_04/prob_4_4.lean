/-
TASK ID: prob_4_4
TYPE: Problem
SOURCE PLAN: 12_chap4_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib




-- WRITE FINAL LEAN CODE BELOW

theorem prob_4_4 {Ω : Type*} [MeasurableSpace Ω]
    (Z : Ω → ℂ) (hZ : Measurable Z) (α : ℂ) :
    Measurable (fun ω => α * Z ω) := by
  exact measurable_const.mul hZ
