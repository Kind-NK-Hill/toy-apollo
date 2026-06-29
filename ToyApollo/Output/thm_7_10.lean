/-
TASK ID: thm_7_10
TYPE: Theorem_with_Proof
SOURCE PLAN: 28_chap7_pushforward_change_of_variable
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

noncomputable def pushForwardRealMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) : Measure ℝ :=
  Measure.map X μ

theorem thm_7_10 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ)
    (hX : Measurable X) {B : Set ℝ} (hB : MeasurableSet B) :
    pushForwardRealMeasure μ X B = μ (X ⁻¹' B) := by
  simpa [pushForwardRealMeasure] using (Measure.map_apply hX hB)
