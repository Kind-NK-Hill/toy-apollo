/-
TASK ID: ex_2_2_2
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_02.ex_2_1_1
import ProbabilityTheory.chapter_02.def_2_2
import ProbabilityTheory.chapter_02.def_2_3

open Set

 
def cofiniteFamily : Set (Set ℕ) :=
  {A | A.Finite ∨ Aᶜ.Finite}

 
def positiveOddNaturals : Set ℕ :=
  {n | ∃ k : ℕ, n = 2 * k + 1}

 
def evenSingletonSequence (n : ℕ) : Set ℕ :=
  {2 * (n + 1)}

 
structure CoFiniteAlgebraWitness where
  family : Set (Set ℕ)
  witnessSequence : ℕ → Set ℕ
  witnessUnion : Set ℕ

 
def ex_2_2_2 : CoFiniteAlgebraWitness where
  family := cofiniteFamily
  witnessSequence := evenSingletonSequence
  witnessUnion := positiveEvenNaturals

 
theorem cofiniteFamily_example_finite :
    ({1, 2, 3} : Set ℕ) ∈ cofiniteFamily := by
  left
  simp

 
theorem cofiniteFamily_example_cofinite :
    (({2, 3, 5, 7} : Set ℕ)ᶜ) ∈ cofiniteFamily := by
  right
  have hfinite : ({2, 3, 5, 7} : Set ℕ).Finite := by
    simp
  simpa using hfinite

 
theorem cofiniteFamily_univ_mem : Set.univ ∈ cofiniteFamily := by
  right
  simpa using (Set.finite_empty : (∅ : Set ℕ).Finite)

 
theorem cofiniteFamily_compl_mem {A : Set ℕ} (hA : A ∈ cofiniteFamily) :
    Aᶜ ∈ cofiniteFamily := by
  rcases hA with hA | hA
  · right
    simpa using hA
  · left
    exact hA

 
theorem cofiniteFamily_union_mem {A B : Set ℕ}
    (hA : A ∈ cofiniteFamily) (hB : B ∈ cofiniteFamily) :
    A ∪ B ∈ cofiniteFamily := by
  rcases hA with hA | hA
  · rcases hB with hB | hB
    · left
      exact hA.union hB
    · right
      exact Set.Finite.subset hB (by
        intro x hx
        intro hxB
        exact hx (Or.inr hxB))
  · rcases hB with hB | hB
    · right
      exact Set.Finite.subset hA (by
        intro x hx
        intro hxA
        exact hx (Or.inl hxA))
    · right
      simpa [compl_union] using hA.inter_of_left Bᶜ

 
def cofiniteAlgebra : EventAlgebra ℕ where
  carrier := cofiniteFamily
  univ_mem := cofiniteFamily_univ_mem
  union_mem := fun {_ _} => cofiniteFamily_union_mem
  compl_mem := fun {_} => cofiniteFamily_compl_mem

 
theorem evenSingletonSequence_mem (n : ℕ) :
    evenSingletonSequence n ∈ cofiniteFamily := by
  left
  simpa [evenSingletonSequence] using (Set.finite_singleton (2 * (n + 1) : ℕ))

 
theorem iUnion_evenSingletonSequence :
    (⋃ n, evenSingletonSequence n) = positiveEvenNaturals := by
  ext x
  constructor
  · intro hx
    rcases mem_iUnion.mp hx with ⟨n, hn⟩
    simp [evenSingletonSequence, positiveEvenNaturals] at hn ⊢
    exact ⟨n, hn⟩
  · intro hx
    rcases hx with ⟨n, hn⟩
    refine mem_iUnion.mpr ⟨n, ?_⟩
    simp [evenSingletonSequence, hn]

 
theorem positiveEvenNaturals_eq_range :
    positiveEvenNaturals = Set.range (fun k : ℕ => 2 * (k + 1)) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨k, rfl⟩
    exact ⟨k, rfl⟩
  · intro hx
    rcases hx with ⟨k, rfl⟩
    exact ⟨k, rfl⟩

 
theorem positiveOddNaturals_eq_range :
    positiveOddNaturals = Set.range (fun k : ℕ => 2 * k + 1) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨k, rfl⟩
    exact ⟨k, rfl⟩
  · intro hx
    rcases hx with ⟨k, rfl⟩
    exact ⟨k, rfl⟩

 
theorem positiveEvenNaturals_infinite : positiveEvenNaturals.Infinite := by
  rw [positiveEvenNaturals_eq_range]
  exact Set.infinite_range_of_injective (fun m n h => by omega)

 
theorem positiveOddNaturals_infinite : positiveOddNaturals.Infinite := by
  rw [positiveOddNaturals_eq_range]
  exact Set.infinite_range_of_injective (fun m n h => by omega)

 
theorem positiveOddNaturals_subset_compl :
    positiveOddNaturals ⊆ positiveEvenNaturalsᶜ := by
  intro x hx
  rcases hx with ⟨k, rfl⟩
  intro h
  rcases h with ⟨m, hm⟩
  omega

 
theorem positiveEvenNaturals_compl_infinite : positiveEvenNaturalsᶜ.Infinite := by
  exact Set.Infinite.mono positiveOddNaturals_subset_compl positiveOddNaturals_infinite

 
theorem positiveEvenNaturals_not_mem_cofiniteFamily :
    positiveEvenNaturals ∉ cofiniteFamily := by
  intro h
  rcases h with h | h
  · exact h.not_infinite positiveEvenNaturals_infinite
  · exact h.not_infinite positiveEvenNaturals_compl_infinite

 
theorem ex_2_2_2_not_sigma_closed :
    (⋃ n, evenSingletonSequence n) ∉ cofiniteFamily := by
  rw [iUnion_evenSingletonSequence]
  exact positiveEvenNaturals_not_mem_cofiniteFamily



theorem ex_2_2_2_source_spine :
    ({1, 2, 3} : Set ℕ) ∈ cofiniteFamily ∧
      (({2, 3, 5, 7} : Set ℕ)ᶜ) ∈ cofiniteFamily ∧
      (Set.univ : Set ℕ) ∈ cofiniteFamily ∧
      (∀ {A : Set ℕ}, A ∈ cofiniteFamily → Aᶜ ∈ cofiniteFamily) ∧
      (∀ {A B : Set ℕ}, A ∈ cofiniteFamily → B ∈ cofiniteFamily →
        A ∪ B ∈ cofiniteFamily) ∧
      (∀ n, evenSingletonSequence n ∈ cofiniteFamily) ∧
      (⋃ n, evenSingletonSequence n) ∉ cofiniteFamily :=
  ⟨cofiniteFamily_example_finite,
    cofiniteFamily_example_cofinite,
    cofiniteFamily_univ_mem,
    fun {_} => cofiniteFamily_compl_mem,
    fun {_ _} => cofiniteFamily_union_mem,
    evenSingletonSequence_mem,
    ex_2_2_2_not_sigma_closed⟩
