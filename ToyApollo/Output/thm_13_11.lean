/-
TASK ID: thm_13_11
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-discrete-random-variable
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

noncomputable section

theorem thm_13_11 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (A : ℕ → Set Ω)
    (hX : Integrable X P)
    (hA : ∀ i : ℕ, MeasurableSet (A i))
    (hDisjoint : Pairwise fun i j : ℕ => Disjoint (A i) (A j)) :
    (∑' i : ℕ, ∫ ω in A i, X ω ∂P) =
      ∫ ω in ⋃ i : ℕ, A i, X ω ∂P := by
  have hIntOn : IntegrableOn X (⋃ i : ℕ, A i) P := hX.integrableOn
  simpa using
    (integral_iUnion (μ := P) (f := X) hA hDisjoint hIntOn).symm
