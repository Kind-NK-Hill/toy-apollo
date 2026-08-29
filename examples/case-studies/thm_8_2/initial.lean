import Mathlib

/-!
Sanitized proof-route snapshot for case study `thm_8_2`.
The private source excerpt and prompt-pack metadata are omitted.
-/

open MeasureTheory

/-- Initial shortcut: select Mathlib's finished object, then verify its API. -/
theorem initialThm82
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β) [SigmaFinite P] [SigmaFinite Q] :
    ∃! R : Measure (α × β),
      ∀ s : Set α, ∀ t : Set β,
        MeasurableSet s → MeasurableSet t → R (s ×ˢ t) = P s * Q t := by
  refine ⟨P.prod Q, ?_, ?_⟩
  · intro s t hs ht
    exact Measure.prod_prod (μ := P) (ν := Q) s t
  · intro R hR
    exact (Measure.prod_eq (μ := P) (ν := Q) (μν := R)
      (by intro s t hs ht; exact hR s t hs ht)).symm
