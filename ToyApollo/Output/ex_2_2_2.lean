import Mathlib
import ToyApollo.Output.ex_2_1_1
import ToyApollo.Output.def_2_2
import ToyApollo.Output.def_2_3

open Set

/-- The cofinite family on `ℕ`. -/
def cofiniteFamily : Set (Set ℕ) :=
  {A | A.Finite ∨ Aᶜ.Finite}

/-- Positive odd naturals, used to witness that the complement is infinite. -/
def positiveOddNaturals : Set ℕ :=
  {n | ∃ k : ℕ, n = 2 * k + 1}

/-- The sequence `{2}, {4}, {6}, ...` used to witness failure of sigma-closure. -/
def evenSingletonSequence (n : ℕ) : Set ℕ :=
  {2 * (n + 1)}

/-- Exported data for Example 2.2.2. -/
structure CoFiniteAlgebraWitness where
  family : Set (Set ℕ)
  witnessSequence : ℕ → Set ℕ
  witnessUnion : Set ℕ

/-- Exported declaration for Example 2.2.2. -/
def ex_2_2_2 : CoFiniteAlgebraWitness where
  family := cofiniteFamily
  witnessSequence := evenSingletonSequence
  witnessUnion := positiveEvenNaturals

/-- The concrete finite set `{1,2,3}` belongs to the cofinite family. -/
theorem cofiniteFamily_example_finite :
    ({1, 2, 3} : Set ℕ) ∈ cofiniteFamily := by
  left
  simp

/-- The concrete cofinite set `ℕ \ {2,3,5,7}` belongs to the cofinite family. -/
theorem cofiniteFamily_example_cofinite :
    (({2, 3, 5, 7} : Set ℕ)ᶜ) ∈ cofiniteFamily := by
  right
  have hfinite : ({2, 3, 5, 7} : Set ℕ).Finite := by
    simp
  simpa using hfinite

/-- The cofinite family contains the whole sample space. -/
theorem cofiniteFamily_univ_mem : Set.univ ∈ cofiniteFamily := by
  right
  simpa using (Set.finite_empty : (∅ : Set ℕ).Finite)

/-- The cofinite family is closed under complements. -/
theorem cofiniteFamily_compl_mem {A : Set ℕ} (hA : A ∈ cofiniteFamily) :
    Aᶜ ∈ cofiniteFamily := by
  rcases hA with hA | hA
  · right
    simpa using hA
  · left
    exact hA

/-- The cofinite family is closed under finite unions. -/
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

/-- Therefore the cofinite family defines an algebra of events on `ℕ`. -/
def cofiniteAlgebra : EventAlgebra ℕ where
  carrier := cofiniteFamily
  univ_mem := cofiniteFamily_univ_mem
  union_mem := fun {_ _} => cofiniteFamily_union_mem
  compl_mem := fun {_} => cofiniteFamily_compl_mem

/-- Each singleton even set in the witness sequence lies in the cofinite family. -/
theorem evenSingletonSequence_mem (n : ℕ) :
    evenSingletonSequence n ∈ cofiniteFamily := by
  left
  simpa [evenSingletonSequence] using (Set.finite_singleton (2 * (n + 1) : ℕ))

/-- The union of the singleton-even sequence is the set of positive even naturals. -/
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

/-- Positive even naturals are exactly the range of `n ↦ 2(n+1)`. -/
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

/-- Positive odd naturals are exactly the range of `n ↦ 2n+1`. -/
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

/-- The set of positive even naturals is infinite. -/
theorem positiveEvenNaturals_infinite : positiveEvenNaturals.Infinite := by
  rw [positiveEvenNaturals_eq_range]
  exact Set.infinite_range_of_injective (fun m n h => by omega)

/-- Positive odd naturals are infinite. -/
theorem positiveOddNaturals_infinite : positiveOddNaturals.Infinite := by
  rw [positiveOddNaturals_eq_range]
  exact Set.infinite_range_of_injective (fun m n h => by omega)

/-- Every positive odd natural lies outside the positive-even witness set. -/
theorem positiveOddNaturals_subset_compl :
    positiveOddNaturals ⊆ positiveEvenNaturalsᶜ := by
  intro x hx
  rcases hx with ⟨k, rfl⟩
  intro h
  rcases h with ⟨m, hm⟩
  omega

/-- The complement of the positive even naturals is also infinite, since it contains all odd naturals. -/
theorem positiveEvenNaturals_compl_infinite : positiveEvenNaturalsᶜ.Infinite := by
  exact Set.Infinite.mono positiveOddNaturals_subset_compl positiveOddNaturals_infinite

/-- Hence the witness union is neither finite nor cofinite. -/
theorem positiveEvenNaturals_not_mem_cofiniteFamily :
    positiveEvenNaturals ∉ cofiniteFamily := by
  intro h
  rcases h with h | h
  · exact h.not_infinite positiveEvenNaturals_infinite
  · exact h.not_infinite positiveEvenNaturals_compl_infinite

/-- The cofinite algebra is not a sigma-algebra: the countable union of singleton-even sets leaves the family. -/
theorem ex_2_2_2_not_sigma_closed :
    (⋃ n, evenSingletonSequence n) ∉ cofiniteFamily := by
  rw [iUnion_evenSingletonSequence]
  exact positiveEvenNaturals_not_mem_cofiniteFamily
