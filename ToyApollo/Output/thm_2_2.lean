/-
TASK ID: thm_2_2
TYPE: Theorem_with_Proof
SOURCE PLAN: 42_chap2_measure_functions
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_2_5

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set

theorem thm_2_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {A B : Set Ω} (hAB : A ⊆ B) :
    μ A ≤ μ B := by
  exact measure_mono hAB
