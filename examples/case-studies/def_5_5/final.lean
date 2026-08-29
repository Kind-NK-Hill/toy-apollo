import Mathlib

/-!
Sanitized public Interface slice for case study `def_5_5`.
The private source excerpt and prompt-pack metadata are omitted.
-/

/-- Reviewed textbook-first finite-subfamily definition. -/
def reviewedDef55 {Ω : Type _} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) {n : ℕ} (A : Fin n → Set Ω) : Prop :=
  ∀ s : Finset (Fin n), 2 ≤ s.card →
    μ (⋂ i ∈ s, A i) = ∏ i ∈ s, μ (A i)

/-- Reusable bridge to Mathlib, with its real domain conditions visible. -/
theorem reviewedDef55IffIIndepSet {Ω : Type _} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    (A : Fin n → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    reviewedDef55 μ A ↔ ProbabilityTheory.iIndepSet A μ := by
  rw [ProbabilityTheory.iIndepSet_iff_meas_biInter hA]
  constructor
  · intro h s
    by_cases hs : 2 ≤ s.card
    · exact h s hs
    · have hs_le : s.card ≤ 1 := by omega
      obtain rfl | hs_ne := s.eq_empty_or_nonempty
      · simp
      · have hs_one : s.card = 1 := by
          have hs_pos : 0 < s.card := Finset.card_pos.mpr hs_ne
          omega
        obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hs_one
        simp
  · intro h s hs
    exact h s
