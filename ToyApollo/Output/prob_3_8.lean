/-
TASK ID: prob_3_8
TYPE: Problem
SOURCE PLAN: 07_chap3_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

open Set

variable {Ω : Type*}

def PiSystem (P : Set (Set Ω)) : Prop :=
  ∀ ⦃A⦄, A ∈ P → ∀ ⦃B⦄, B ∈ P → A ∩ B ∈ P

structure LambdaSystem (L : Set (Set Ω)) : Prop where
  univ_mem : univ ∈ L
  compl_mem : ∀ {A}, A ∈ L → Aᶜ ∈ L
  iUnion_mem :
    ∀ {f : ℕ → Set Ω}, Pairwise (fun i j => Disjoint (f i) (f j)) →
      (∀ i, f i ∈ L) → (⋃ i, f i) ∈ L

variable {L : Set (Set Ω)}

lemma lambda_empty (h_univ : univ ∈ L) (h_compl : ∀ A ∈ L, Aᶜ ∈ L) :
    (∅ : Set Ω) ∈ L := by
  have : univᶜ = (∅ : Set Ω) := compl_univ
  rw [← this]
  exact h_compl _ h_univ

lemma lambda_pi_union (h_compl : ∀ A ∈ L, Aᶜ ∈ L)
    (h_pi : ∀ A B, A ∈ L → B ∈ L → A ∩ B ∈ L)
    {A B : Set Ω} (hA : A ∈ L) (hB : B ∈ L) :
    A ∪ B ∈ L := by
  simpa [Set.compl_inter] using h_compl _ (h_pi _ _ (h_compl _ hA) (h_compl _ hB))

lemma lambda_pi_finset_union (h_univ : univ ∈ L) (h_compl : ∀ A ∈ L, Aᶜ ∈ L)
    (h_pi : ∀ A B, A ∈ L → B ∈ L → A ∩ B ∈ L)
    (f : ℕ → Set Ω) (hf : ∀ i, f i ∈ L) (n : ℕ) :
    (⋃ i ∈ Finset.range n, f i) ∈ L := by
  induction n <;> simp_all +decide [Finset.range_add_one]
  · simpa using h_compl _ h_univ
  · convert lambda_pi_union h_compl (fun A B hA hB => h_pi A B hA hB) (hf _) ‹_› using 1

lemma lambda_pi_diff (h_compl : ∀ A ∈ L, Aᶜ ∈ L)
    (h_pi : ∀ A B, A ∈ L → B ∈ L → A ∩ B ∈ L)
    {A B : Set Ω} (hA : A ∈ L) (hB : B ∈ L) :
    A \ B ∈ L := by
  simpa [Set.diff_eq] using h_pi _ _ hA (h_compl _ hB)

lemma disjointed_pairwise_disjoint (f : ℕ → Set Ω) :
    Pairwise fun i j => Disjoint (disjointed f i) (disjointed f j) := by
  simpa [Function.onFun] using (disjoint_disjointed f)

lemma iUnion_disjointed_eq (f : ℕ → Set Ω) :
    ⋃ i, disjointed f i = ⋃ i, f i := by
  simpa using (iUnion_disjointed (f := f))

lemma disjointed_mem (h_univ : univ ∈ L) (h_compl : ∀ A ∈ L, Aᶜ ∈ L)
    (h_pi : ∀ A B, A ∈ L → B ∈ L → A ∩ B ∈ L)
    (f : ℕ → Set Ω) (hf : ∀ i, f i ∈ L) (n : ℕ) :
    disjointed f n ∈ L := by
  induction' n with n ih
  · simpa using hf 0
  · convert lambda_pi_diff h_compl h_pi (hf (n + 1)) _ using 1
    convert lambda_pi_finset_union h_univ h_compl h_pi f hf (n + 1) using 1
    simp +decide [Finset.ext_iff, Set.ext_iff]

lemma sigma_to_pi (h_univ : univ ∈ L) (h_compl : ∀ A ∈ L, Aᶜ ∈ L)
    (h_union : ∀ (f : ℕ → Set Ω), (∀ i, f i ∈ L) → ⋃ i, f i ∈ L) :
    ∀ A B, A ∈ L → B ∈ L → A ∩ B ∈ L := by
  intro A B hA hB
  have h_union_compl : Aᶜ ∪ Bᶜ ∈ L := by
    convert h_union (fun i => if i = 0 then Aᶜ else if i = 1 then Bᶜ else ∅) _ using 1
    · ext x
      simp [Set.mem_union, Set.mem_compl_iff]
      exact
        ⟨fun h => by
          rcases h with h | h
          · exact ⟨0, h⟩
          · exact ⟨1, h⟩,
        fun ⟨i, hi⟩ => by
          rcases i with (_ | _ | i) <;> aesop⟩
    · intro i
      by_cases hi : i = 0 <;> by_cases hi' : i = 1 <;> simp +decide [*]
      simpa using h_compl _ h_univ
  have h_compl_union : (Aᶜ ∪ Bᶜ)ᶜ ∈ L := by
    exact h_compl _ h_union_compl
  exact (by
    simpa [Set.compl_union] using h_compl_union)

theorem prob_3_8 (Ω : Type _) (L : Set (Set Ω)) :
    let isLambdaSystem := Set.univ ∈ L ∧ (∀ A ∈ L, Aᶜ ∈ L) ∧
        (∀ (f : ℕ → Set Ω), (Pairwise fun i j => Disjoint (f i) (f j)) →
          (∀ i, f i ∈ L) → ⋃ i, f i ∈ L)
    let isPiSystem := ∀ A B, A ∈ L → B ∈ L → A ∩ B ∈ L
    let isSigmaAlgebra := Set.univ ∈ L ∧ (∀ A ∈ L, Aᶜ ∈ L) ∧
        (∀ (f : ℕ → Set Ω), (∀ i, f i ∈ L) → ⋃ i, f i ∈ L)
    isLambdaSystem → (isSigmaAlgebra ↔ isPiSystem) := by
  refine' fun h ↦ ⟨_, _⟩
  · exact fun h => sigma_to_pi h.1 h.2.1 h.2.2
  · intro h_pi
    obtain ⟨h_univ, h_compl, h_disj_union⟩ := h
    use h_univ, h_compl, fun f hf => by
      exact h_disj_union _ (disjointed_pairwise_disjoint f)
        (disjointed_mem h_univ h_compl h_pi _ hf) |>
          fun h => by simpa only [iUnion_disjointed_eq] using h
