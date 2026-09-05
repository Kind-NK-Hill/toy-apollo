/-
TASK ID: def_3_10
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.MeasureTheory.PiSystem




open Set

variable {Ω : Type*}




def PiSystem {Ω : Type*} (P : Set (Set Ω)) : Prop :=
  P.Nonempty ∧ ∀ ⦃A⦄, A ∈ P → ∀ ⦃B⦄, B ∈ P → A ∩ B ∈ P




structure LambdaSystem (L : Set (Set Ω)) : Prop where
   
  univ_mem : univ ∈ L
   
  compl_mem : ∀ {A}, A ∈ L → Aᶜ ∈ L
   
  iUnion_mem : ∀ {f : ℕ → Set Ω}, Pairwise (fun i j => Disjoint (f i) (f j))
    → (∀ i, f i ∈ L) → (⋃ i, f i) ∈ L



theorem piSystem_iff_isPiSystem {Ω : Type*} {P : Set (Set Ω)} (empty_mem : ∅ ∈ P) :
    PiSystem P ↔ IsPiSystem P := by
  constructor
  · intro h A hA B hB _
    exact h.2 hA hB
  · intro h
    constructor
    · exact ⟨∅, empty_mem⟩
    · intro A hA B hB
      by_cases hAB : (A ∩ B).Nonempty
      · exact h A hA B hB hAB
      · rw [Set.not_nonempty_iff_eq_empty.mp hAB]
        exact empty_mem





theorem lambdaSystem_iff_exists_dynkinSystem {L : Set (Set Ω)} :
    LambdaSystem L ↔
      ∃ d : MeasurableSpace.DynkinSystem Ω, ∀ A : Set Ω, d.Has A ↔ A ∈ L := by
  constructor
  · intro h
    refine ⟨{
      Has := fun A ↦ A ∈ L
      has_empty := by simpa using h.compl_mem h.univ_mem
      has_compl := h.compl_mem
      has_iUnion_nat := h.iUnion_mem
    }, fun _ ↦ Iff.rfl⟩
  · rintro ⟨d, hd⟩
    constructor
    · exact (hd _).mp d.has_univ
    · intro A hA
      exact (hd _).mp (d.has_compl ((hd _).mpr hA))
    · intro f hf hL
      apply (hd _).mp
      exact d.has_iUnion_nat (fun i j hij ↦ by simpa using hf hij) (fun i ↦ (hd _).mpr (hL i))
