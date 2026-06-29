/-
TASK ID: prob_2_12
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.def_2_2

theorem prob_2_12 (Ω : Type _) (𝒜 : Set (Set Ω)) (h_univ : Set.univ ∈ 𝒜)
    (h_diff : ∀ A B, A ∈ 𝒜 → B ∈ 𝒜 → B \ A ∈ 𝒜) :
    ∅ ∈ 𝒜 ∧ (∀ A, A ∈ 𝒜 → Aᶜ ∈ 𝒜) ∧ (∀ A B, A ∈ 𝒜 → B ∈ 𝒜 → A ∪ B ∈ 𝒜) := by
      have h_empty : ∅ ∈ 𝒜 := by
        simpa using h_diff _ _ h_univ h_univ
      have h_compl : ∀ A ∈ 𝒜, Aᶜ ∈ 𝒜 := by
        exact fun A hA => by simpa [ Set.diff_eq ] using h_diff A Set.univ hA h_univ;
      have h_union : ∀ A B, A ∈ 𝒜 → B ∈ 𝒜 → A ∪ B ∈ 𝒜 := by
        intro A B hA hB;
        convert h_compl _ ( h_diff _ _ hA ( h_compl _ hB ) ) using 1 ; ext ; simp +decide ; tauto;
      exact ⟨h_empty, h_compl, h_union⟩

def prob_2_12_eventAlgebra (Ω : Type _) (𝒜 : Set (Set Ω)) (h_univ : Set.univ ∈ 𝒜)
    (h_diff : ∀ A B, A ∈ 𝒜 → B ∈ 𝒜 → B \ A ∈ 𝒜) : EventAlgebra Ω where
  carrier := 𝒜
  univ_mem := h_univ
  union_mem := by
    intro A B hA hB
    exact (prob_2_12 Ω 𝒜 h_univ h_diff).2.2 A B hA hB
  compl_mem := by
    intro A hA
    exact (prob_2_12 Ω 𝒜 h_univ h_diff).2.1 A hA

theorem prob_2_12_is_field (Ω : Type _) (𝒜 : Set (Set Ω)) (h_univ : Set.univ ∈ 𝒜)
    (h_diff : ∀ A B, A ∈ 𝒜 → B ∈ 𝒜 → B \ A ∈ 𝒜) :
    ∃ 𝓕 : EventAlgebra Ω, 𝓕.carrier = 𝒜 := by
  exact ⟨prob_2_12_eventAlgebra Ω 𝒜 h_univ h_diff, rfl⟩
