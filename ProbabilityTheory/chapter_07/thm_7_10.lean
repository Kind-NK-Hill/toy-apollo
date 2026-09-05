/-
TASK ID: thm_7_10
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real







open MeasureTheory

 
noncomputable def pushForwardRealMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) : Measure ℝ :=
  Measure.map X μ



theorem thm_7_10 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ)
    (hX : Measurable X) {B : Set ℝ} (hB : MeasurableSet B) :
    pushForwardRealMeasure μ X B = μ (X ⁻¹' B) := by
  simpa [pushForwardRealMeasure] using (Measure.map_apply hX hB)
