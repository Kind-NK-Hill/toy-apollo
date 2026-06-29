/-
TASK ID: thm_2_3
TYPE: Theorem_with_Proof
SOURCE PLAN: 42_chap2_measure_functions
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_2_5

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set

theorem thm_2_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A B : Set Ω) :
    μ (A ∪ B) ≤ μ A + μ B := by
  simpa using measure_union_le A B
