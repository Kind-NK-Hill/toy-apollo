/-
TASK ID: def_3_8
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace

open scoped ENNReal

def IsFinitelyAdditive {α : Type _} (F₀ : Set (Set α)) (μ : Set α → ℝ≥0∞) : Prop :=
  ∀ {n : ℕ} (A : Fin n → Set α),
    (∀ i, A i ∈ F₀) →
    (∀ i j, i ≠ j → Disjoint (A i) (A j)) →
    μ (Set.iUnion A) = Finset.sum (Finset.univ : Finset (Fin n)) (fun i => μ (A i))

def IsSigmaSubadditive {α : Type _} (F₀ : Set (Set α)) (μ : Set α → ℝ≥0∞) : Prop :=
  ∀ (A : ℕ → Set α),
    (∀ i, A i ∈ F₀) →
    (Set.iUnion A ∈ F₀) →
    μ (Set.iUnion A) ≤ ∑' i, μ (A i)
