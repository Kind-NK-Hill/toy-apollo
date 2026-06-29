/-
TASK ID: thm_8_2
TYPE: Theorem_Statement
SOURCE PLAN: 32_chap8_product_measure_fubini
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

theorem thm_8_2
    {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β)
    [SigmaFinite P] [SigmaFinite Q] :
    ∃! R : Measure (α × β),
      ∀ s : Set α, ∀ t : Set β,
        MeasurableSet s → MeasurableSet t → R (s ×ˢ t) = P s * Q t := by
  refine ⟨P.prod Q, ?_, ?_⟩
  · intro s t hs ht
    simpa using Measure.prod_prod (μ := P) (ν := Q) s t
  · intro R hR
    exact (Measure.prod_eq (μ := P) (ν := Q) (μν := R)
      (by intro s t hs ht; exact hR s t hs ht)).symm
