/-
TASK ID: prob_2_3
TYPE: Problem
SOURCE PLAN: 45_chap2_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open Set MeasureTheory MeasurableSpace

theorem prob_2_3 :
    borel ℝ = MeasurableSpace.generateFrom {s | ∃ (b : ℝ), s = {x | x ≤ b}} ∧
    borel ℝ = MeasurableSpace.generateFrom {s | ∃ (b : ℝ), s = {x | x < b}} ∧
    borel ℝ = MeasurableSpace.generateFrom {s | ∃ (a : ℝ), s = {x | a < x}} ∧
    borel ℝ = MeasurableSpace.generateFrom {s | ∃ (a : ℝ), s = {x | a ≤ x}} ∧
    borel ℝ = MeasurableSpace.generateFrom {s | ∃ (a b : ℝ), s = {x | a < x ∧ x ≤ b}} := by
  have range_eq_Iic :
      (Set.range (Set.Iic : ℝ → Set ℝ)) = {s | ∃ (b : ℝ), s = {x | x ≤ b}} := by
    ext s
    simp [Set.mem_range, Set.Iic]
    exact ⟨fun ⟨y, h⟩ => ⟨y, h.symm⟩, fun ⟨y, h⟩ => ⟨y, h.symm⟩⟩
  have range_eq_Iio :
      (Set.range (Set.Iio : ℝ → Set ℝ)) = {s | ∃ (b : ℝ), s = {x | x < b}} := by
    ext s
    simp [Set.mem_range, Set.Iio]
    exact ⟨fun ⟨y, h⟩ => ⟨y, h.symm⟩, fun ⟨y, h⟩ => ⟨y, h.symm⟩⟩
  have range_eq_Ioi :
      (Set.range (Set.Ioi : ℝ → Set ℝ)) = {s | ∃ (a : ℝ), s = {x | a < x}} := by
    ext s
    simp [Set.mem_range, Set.Ioi]
    exact ⟨fun ⟨y, h⟩ => ⟨y, h.symm⟩, fun ⟨y, h⟩ => ⟨y, h.symm⟩⟩
  have range_eq_Ici :
      (Set.range (Set.Ici : ℝ → Set ℝ)) = {s | ∃ (a : ℝ), s = {x | a ≤ x}} := by
    ext s
    simp [Set.mem_range, Set.Ici]
    exact ⟨fun ⟨y, h⟩ => ⟨y, h.symm⟩, fun ⟨y, h⟩ => ⟨y, h.symm⟩⟩
  rw [← range_eq_Iic, ← range_eq_Iio, ← range_eq_Ioi, ← range_eq_Ici]
  refine ⟨borel_eq_generateFrom_Iic ℝ, borel_eq_generateFrom_Iio ℝ,
      borel_eq_generateFrom_Ioi ℝ, borel_eq_generateFrom_Ici ℝ, ?_⟩
  rw [borel_eq_generateFrom_Ioc (α := ℝ)]
  apply le_antisymm
  · apply generateFrom_le
    intro s hs
    obtain ⟨l, u, hlu, rfl⟩ := hs
    exact GenerateMeasurable.basic _ ⟨l, u, rfl⟩
  · apply generateFrom_le
    intro s hs
    obtain ⟨a, b, rfl⟩ := hs
    by_cases hab : a < b
    · exact GenerateMeasurable.basic _ ⟨a, b, hab, rfl⟩
    · push_neg at hab
      convert @MeasurableSet.empty _ (generateFrom {S | ∃ l u, l < u ∧ Set.Ioc l u = S})
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false]
      constructor
      · rintro ⟨hax, hxb⟩
        linarith
      · exact False.elim
