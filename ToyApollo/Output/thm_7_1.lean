/-
TASK ID: thm_7_1
TYPE: Theorem_with_Proof
SOURCE PLAN: 25_chap7_ae_equality
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

theorem thm_7_1 {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜] (μ : Measure Ω)
    (X : Ω → 𝕜) (_hX : Integrable X μ) :
    ‖∫ ω, X ω ∂μ‖ ≤ ∫ ω, ‖X ω‖ ∂μ := by
  simpa using (MeasureTheory.norm_integral_le_integral_norm (μ := μ) X)
