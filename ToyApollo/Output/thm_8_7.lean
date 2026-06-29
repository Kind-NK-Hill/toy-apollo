/-
TASK ID: thm_8_7
TYPE: Theorem_with_Proof
SOURCE PLAN: 34_chap8_total_variation_distance
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_8_1
import ToyApollo.Output.def_8_5

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory Set

noncomputable section

theorem thm_8_7
    {α : Type*} [MeasurableSpace α] {P Q : Measure α}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (π : Coupling P Q) :
    totalVariationDistance P Q ≤ π.μ.real {ω : π.Ω | π.X ω ≠ π.Y ω} := by
  let mismatch : Set π.Ω := {ω : π.Ω | π.X ω ≠ π.Y ω}
  let S : Set ℝ := {d : ℝ | ∃ A : Set α, MeasurableSet A ∧ d = |P.real A - Q.real A|}
  have hnonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨∅, MeasurableSet.empty, ?_⟩
    simp
  have hbound : ∀ d ∈ S, d ≤ π.μ.real mismatch := by
    intro d hd
    rcases hd with ⟨A, hA, rfl⟩
    have hP : P.real A = π.μ.real (π.X ⁻¹' A) := by
      simpa [π.map_X] using
        (MeasureTheory.map_measureReal_apply (μ := π.μ) π.measurable_X hA)
    have hQ : Q.real A = π.μ.real (π.Y ⁻¹' A) := by
      simpa [π.map_Y] using
        (MeasureTheory.map_measureReal_apply (μ := π.μ) π.measurable_Y hA)
    have hsubXY : π.X ⁻¹' A ⊆ π.Y ⁻¹' A ∪ mismatch := by
      intro ω hω
      by_cases hEq : π.X ω = π.Y ω
      · left
        simpa [Set.mem_preimage, hEq] using hω
      · right
        simp [mismatch, hEq]
    have hsubYX : π.Y ⁻¹' A ⊆ π.X ⁻¹' A ∪ mismatch := by
      intro ω hω
      by_cases hEq : π.X ω = π.Y ω
      · left
        simpa [Set.mem_preimage, hEq] using hω
      · right
        simp [mismatch, hEq]
    have hXY_le :
        π.μ.real (π.X ⁻¹' A) ≤ π.μ.real (π.Y ⁻¹' A) + π.μ.real mismatch := by
      refine le_trans (MeasureTheory.measureReal_mono hsubXY) ?_
      exact MeasureTheory.measureReal_union_le (π.Y ⁻¹' A) mismatch
    have hYX_le :
        π.μ.real (π.Y ⁻¹' A) ≤ π.μ.real (π.X ⁻¹' A) + π.μ.real mismatch := by
      refine le_trans (MeasureTheory.measureReal_mono hsubYX) ?_
      exact MeasureTheory.measureReal_union_le (π.X ⁻¹' A) mismatch
    have h1 : π.μ.real (π.X ⁻¹' A) - π.μ.real (π.Y ⁻¹' A) ≤ π.μ.real mismatch := by
      linarith
    have h2 : π.μ.real (π.Y ⁻¹' A) - π.μ.real (π.X ⁻¹' A) ≤ π.μ.real mismatch := by
      linarith
    rw [hP, hQ]
    exact (abs_sub_le_iff.2 ⟨h1, h2⟩)
  unfold totalVariationDistance
  change sSup S ≤ π.μ.real mismatch
  exact csSup_le hnonempty hbound
