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

theorem thm_2_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    μ A ≤ μ B := by
  have h_disj : Disjoint A (B \ A) := disjoint_sdiff_right
  have h_union : A ∪ (B \ A) = B := union_diff_cancel hAB
  have h_diff_meas : MeasurableSet (B \ A) := hB.diff hA
  have h_add : μ B = μ A + μ (B \ A) := by
    calc
      μ B = μ (A ∪ (B \ A)) := by rw [h_union]
      _ = μ A + μ (B \ A) := measure_union h_disj h_diff_meas
  rw [h_add]
  exact le_add_right le_rfl
