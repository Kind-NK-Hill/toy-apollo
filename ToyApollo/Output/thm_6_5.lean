/-
TASK ID: thm_6_5
TYPE: Theorem_with_Proof
SOURCE PLAN: 20_chap6_nonnegative_functions
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.Integral.Lebesgue.Add

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

theorem thm_6_5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {X Y : Ω → ENNReal}
    (hX : Measurable X) (hY : Measurable Y) (c : ENNReal) :
    ∫⁻ ω, X ω + Y ω ∂μ = ∫⁻ ω, X ω ∂μ + ∫⁻ ω, Y ω ∂μ ∧
      ∫⁻ ω, c * X ω ∂μ = c * ∫⁻ ω, X ω ∂μ := by
  refine ⟨?_, ?_⟩
  · exact MeasureTheory.lintegral_add_left hX Y
  · exact MeasureTheory.lintegral_const_mul c hX
