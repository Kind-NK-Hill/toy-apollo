/-
TASK ID: thm_7_11
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Basic






open MeasureTheory



theorem thm_7_11 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → ℝ} {h : ℝ → ℝ} (hX : Measurable X) (hh : Measurable h) :
    (Integrable (fun ω => h (X ω)) μ ↔ Integrable h (Measure.map X μ)) ∧
      (∫ ω, h (X ω) ∂μ = ∫ x, h x ∂Measure.map X μ) := by
  constructor
  · change Integrable (h ∘ X) μ ↔ Integrable h (Measure.map X μ)
    exact
      (MeasureTheory.integrable_map_measure
        (μ := μ) (f := X) (g := h) hh.aestronglyMeasurable hX.aemeasurable).symm
  · change (∫ ω, (h ∘ X) ω ∂μ) = ∫ x, h x ∂Measure.map X μ
    exact
      (MeasureTheory.integral_map
        (μ := μ) (φ := X) (f := h) hX.aemeasurable hh.aestronglyMeasurable).symm
