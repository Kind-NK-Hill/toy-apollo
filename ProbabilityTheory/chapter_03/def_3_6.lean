/-
TASK ID: def_3_6
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Data.Real.Basic





 
def IsCompactIntervalSet (s : Set ℝ) : Prop :=
  ∃ a b : ℝ, s = Set.Icc a b
