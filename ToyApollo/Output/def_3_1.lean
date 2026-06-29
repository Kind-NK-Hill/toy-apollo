/-
TASK ID: def_3_1
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace

open Set ENNReal Function

structure FieldOfSets (Ω : Type*) where
  carrier : Set (Set Ω)
  empty_mem : ∅ ∈ carrier
  compl_mem : ∀ s ∈ carrier, sᶜ ∈ carrier
  union_mem : ∀ s t, s ∈ carrier → t ∈ carrier → s ∪ t ∈ carrier

structure Premeasure {Ω : Type*} (F₀ : FieldOfSets Ω) where

  μ₀ : {s : Set Ω // s ∈ F₀.carrier} → ℝ≥0∞

  map_empty : μ₀ ⟨∅, F₀.empty_mem⟩ = 0

  sigma_additive : ∀ (A : ℕ → Set Ω) (hA : ∀ i, A i ∈ F₀.carrier) (hU : (⋃ i, A i) ∈ F₀.carrier),
    Pairwise (Disjoint on A) →
    μ₀ ⟨⋃ i, A i, hU⟩ = ∑' i, μ₀ ⟨A i, hA i⟩
