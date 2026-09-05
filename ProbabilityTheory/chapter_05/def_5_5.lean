/-
TASK ID: def_5_5
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_05.def_5_5to10






def def_5_5_finiteIntersectionCriterion {Ω : Type _} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) {n : ℕ} (A : Fin n → Set Ω) : Prop :=
  ∀ s : Finset (Fin n), 2 ≤ s.card →
    μ (⋂ i ∈ s, A i) = ∏ i ∈ s, μ (A i)

theorem def_5_5_finiteIntersectionCriterion_iff_iIndepSet
    {Ω : Type _} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    (A : Fin n → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    def_5_5_finiteIntersectionCriterion μ A ↔ ProbabilityTheory.iIndepSet A μ := by
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
  · intro h s _hs
    exact h s

theorem def_5_5_finiteIntersectionCriterion_iff_def_5_5
    {Ω : Type _} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    (A : Fin n → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    def_5_5_finiteIntersectionCriterion μ A ↔ def_5_5 μ A := by
  simpa [def_5_5] using
    (def_5_5_finiteIntersectionCriterion_iff_iIndepSet μ A hA)

theorem def_5_5_iff_iIndepSet {Ω : Type _} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    (A : Fin n → Set Ω) (_hA : ∀ i, MeasurableSet (A i)) :
    def_5_5 μ A ↔ ProbabilityTheory.iIndepSet A μ := by
  exact Iff.rfl
