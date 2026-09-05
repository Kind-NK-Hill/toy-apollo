/-
TASK ID: dirichlet_simplex_bridge
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

open MeasureTheory
open scoped BigOperators

noncomputable section

 
def dirichletBridgeSimplex (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) = 1}



theorem dirichletBridgeSimplex_volume_zero (n : ℕ) :
    (volume : Measure (Fin (n + 1) → ℝ)) (dirichletBridgeSimplex n) = 0 := by
  refine measure_mono_null ?_
    (Measure.addHaar_affineSubspace volume (fintypeAffineCoords (Fin (n + 1)) ℝ) ?_)
  · intro y hy
    exact (mem_fintypeAffineCoords_iff_sum).2 hy.2
  · intro htop
    have hzero_mem :
        (0 : Fin (n + 1) → ℝ) ∈ (⊤ : AffineSubspace ℝ (Fin (n + 1) → ℝ)) := by
      simp
    have hzero_mem' :
        (0 : Fin (n + 1) → ℝ) ∈ fintypeAffineCoords (Fin (n + 1)) ℝ := by
      simpa [htop] using hzero_mem
    have hsum : (∑ i : Fin (n + 1), (0 : Fin (n + 1) → ℝ) i) = (1 : ℝ) :=
      (mem_fintypeAffineCoords_iff_sum).1 hzero_mem'
    simp at hsum
