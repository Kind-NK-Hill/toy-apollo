/-
TASK ID: thm_8_3
TYPE: Theorem_Statement
SOURCE PLAN: 32_chap8_product_measure_fubini
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

open scoped ENNReal

theorem thm_8_3
    {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β)
    [SigmaFinite P] [SigmaFinite Q]
    {f : α × β → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ x, ∫⁻ y, f (x, y) ∂Q ∂P)
      = ∫⁻ y, ∫⁻ x, f (x, y) ∂P ∂Q ∧
    (∫⁻ x, ∫⁻ y, f (x, y) ∂Q ∂P)
      = ∫⁻ z, f z ∂(P.prod Q) := by
  have hfae : AEMeasurable f (P.prod Q) := hf.aemeasurable
  have hswap :
      (∫⁻ x, ∫⁻ y, f (x, y) ∂Q ∂P)
        = ∫⁻ y, ∫⁻ x, f (x, y) ∂P ∂Q := by
    simpa using
      (lintegral_lintegral_swap (μ := P) (ν := Q) (f := fun x y => f (x, y)) hfae)
  have hprod :
      (∫⁻ z, f z ∂(P.prod Q)) = ∫⁻ x, ∫⁻ y, f (x, y) ∂Q ∂P := by
    simpa using (lintegral_prod (μ := P) (ν := Q) f hfae)
  refine ⟨hswap, ?_⟩
  exact hprod.symm
