/-
TASK ID: ex_8_3_3
TYPE: Example_Proof
SOURCE PLAN: 33_chap8_monge_kantorovich
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set
open scoped ENNReal

noncomputable section

theorem ex_8_3_3 (x₁ y₁ y₂ : ℝ) (hy : y₁ ≠ y₂) :
    ¬ ∃ T : ℝ → ℝ, Measurable T ∧
      Measure.map T ((2 : ℝ≥0∞) • Measure.dirac x₁) = Measure.dirac y₁ + Measure.dirac y₂ := by
  intro h
  rcases h with ⟨T, hT, hmap⟩
  have hy1 : MeasurableSet ({y₁} : Set ℝ) := measurableSet_singleton y₁
  have h_rhs : (Measure.dirac y₁ + Measure.dirac y₂) {y₁} = 1 := by
    simp [Measure.add_apply, hy1, hy]
  by_cases hTy : T x₁ = y₁
  · have h_lhs :
        Measure.map T ((2 : ℝ≥0∞) • Measure.dirac x₁) {y₁} = 2 := by
      rw [Measure.map_apply hT hy1, Measure.smul_apply]
      simp [Set.mem_preimage, hTy]
    have : (2 : ℝ≥0∞) = 1 := by
      calc
        (2 : ℝ≥0∞) = Measure.map T ((2 : ℝ≥0∞) • Measure.dirac x₁) {y₁} := h_lhs.symm
        _ = (Measure.dirac y₁ + Measure.dirac y₂) {y₁} := by rw [hmap]
        _ = 1 := h_rhs
    norm_num at this
  · have h_lhs :
        Measure.map T ((2 : ℝ≥0∞) • Measure.dirac x₁) {y₁} = 0 := by
      rw [Measure.map_apply hT hy1, Measure.smul_apply]
      simp [Set.mem_preimage, hTy]
    have : (0 : ℝ≥0∞) = 1 := by
      calc
        (0 : ℝ≥0∞) = Measure.map T ((2 : ℝ≥0∞) • Measure.dirac x₁) {y₁} := h_lhs.symm
        _ = (Measure.dirac y₁ + Measure.dirac y₂) {y₁} := by rw [hmap]
        _ = 1 := h_rhs
    norm_num at this
