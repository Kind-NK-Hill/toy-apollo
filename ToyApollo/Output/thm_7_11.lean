/-
TASK ID: thm_7_11
TYPE: Theorem_with_Proof
SOURCE PLAN: 28_chap7_pushforward_change_of_variable
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

theorem thm_7_11 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → ℝ} {h : ℝ → ℝ} (hX : Measurable X) (hh : Measurable h) :
    (Integrable (fun ω => h (X ω)) μ ↔ Integrable h (Measure.map X μ)) ∧
      (∫ ω, h (X ω) ∂μ = ∫ x, h x ∂Measure.map X μ) := by
  constructor
  · simpa [Function.comp_def] using
      (MeasureTheory.integrable_map_measure
        (μ := μ) (f := X) (g := h) hh.aestronglyMeasurable hX.aemeasurable).symm
  · simpa [Function.comp_def] using
      (MeasureTheory.integral_map
        (μ := μ) (φ := X) (f := h) hX.aemeasurable hh.aestronglyMeasurable).symm
