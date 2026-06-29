/-
TASK ID: prob_4_12
TYPE: Problem
SOURCE PLAN: 12_chap4_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

theorem prob_4_12 {f : ℝ → ℝ} (hf : UpperSemicontinuous f) :
    Measurable f := by
  exact hf.measurable
