/-
TASK ID: prob_3_9
TYPE: Problem
SOURCE PLAN: 07_chap3_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_03.prob_3_8




-- WRITE FINAL LEAN CODE BELOW

open Set

 
lemma lambda_empty_mem {Ω : Type*} {L : Set (Set Ω)}
    (h_univ : Set.univ ∈ L) (h_compl : ∀ A ∈ L, Aᶜ ∈ L) :
    (∅ : Set Ω) ∈ L := by
  simpa using h_compl _ h_univ

 
lemma lambda_union_of_disjoint {Ω : Type*} {L : Set (Set Ω)}
    (h_disj_union : ∀ (f : ℕ → Set Ω), (Pairwise fun i j => Disjoint (f i) (f j)) →
      (∀ i, f i ∈ L) → ⋃ i, f i ∈ L)
    (h_empty : (∅ : Set Ω) ∈ L)
    {A B : Set Ω} (hA : A ∈ L) (hB : B ∈ L) (hAB : Disjoint A B) :
    A ∪ B ∈ L := by
  let f : ℕ → Set Ω := fun i => if i = 0 then A else if i = 1 then B else ∅
  have hf_disjoint : Pairwise (fun i j => Disjoint (f i) (f j)) := by
    intro i j hij
    simp [f] at hij ⊢
    grind +revert
  have hf_mem : ∀ i, f i ∈ L := by
    intro i
    by_cases h0 : i = 0
    · simp [f, h0, hA]
    · by_cases h1 : i = 1
      · simp [f, h0, h1, hB]
      · simp [f, h0, h1, h_empty]
  have hf_union : ⋃ i, f i ∈ L := h_disj_union f hf_disjoint hf_mem
  have h_union : A ∪ B = ⋃ i, f i := by
    ext x
    simp [f]
    exact
      ⟨
        fun hx => hx.elim (fun hxA => ⟨0, by simpa using hxA⟩) (fun hxB => ⟨1, by simpa using hxB⟩),
        fun hx => by
          rcases hx with ⟨i, hi⟩
          rcases i with (_ | _ | i)
          · exact Or.inl (by simpa using hi)
          · exact Or.inr (by simpa using hi)
          · simp at hi
      ⟩
  simpa [h_union] using hf_union



lemma lambda_diff_of_subset {Ω : Type*} {L : Set (Set Ω)}
    (hL : LambdaSystem L)
    {A B : Set Ω} (hA : A ∈ L) (hB : B ∈ L) (hAB : A ⊆ B) :
    B \ A ∈ L := by
  set f : ℕ → Set Ω := fun i => if i = 0 then A else if i = 1 then Bᶜ else ∅
  have hf_disjoint : Pairwise (fun i j => Disjoint (f i) (f j)) := by
    intro i j hij
    simp [f] at hij ⊢
    grind +revert
  have hf_mem : ∀ i, f i ∈ L := by
    intro i
    by_cases h0 : i = 0
    · simp [f, h0, hA]
    · by_cases h1 : i = 1
      · simp [f, h0, h1, hB, hL.compl_mem hB]
      · simp [f, h0, h1]
        simpa using hL.compl_mem hL.univ_mem
  have hf_union : ⋃ i, f i ∈ L := hL.iUnion_mem hf_disjoint hf_mem
  have hf_compl : (⋃ i, f i)ᶜ ∈ L := hL.compl_mem hf_union
  have h_diff : B \ A = (⋃ i, f i)ᶜ := by
    ext x
    simp [f]
    exact
      ⟨
        fun hx i => by
          split_ifs <;> simp_all +decide [Set.subset_def],
        fun hx => ⟨by specialize hx 1; aesop, by specialize hx 0; aesop⟩
      ⟩
  rw [h_diff]
  exact hf_compl

theorem prob_3_9 (Ω : Type _) (P L : Set (Set Ω))
    (_hP_nonempty : P.Nonempty)
    (hP_pi : PiSystem P)
    (hL_lambda : LambdaSystem L)
    (hP_subset_L : P ⊆ L) :
    let isLambdaSystem := fun (S : Set (Set Ω)) => (Set.univ ∈ S) ∧ (∀ A ∈ S, Aᶜ ∈ S) ∧
        (∀ (f : ℕ → Set Ω), (Pairwise fun i j => Disjoint (f i) (f j)) →
          (∀ i, f i ∈ S) → ⋃ i, f i ∈ S)
    let isSigmaAlgebra := fun (S : Set (Set Ω)) => (Set.univ ∈ S) ∧ (∀ A ∈ S, Aᶜ ∈ S) ∧
        (∀ (f : ℕ → Set Ω), (∀ i, f i ∈ S) → ⋃ i, f i ∈ S)
    let L0 := {A : Set Ω | ∀ (M : Set (Set Ω)), M ⊆ L → LambdaSystem M → P ⊆ M → A ∈ M}
    let L1 := {A ∈ L0 | ∀ B ∈ P, A ∩ B ∈ L0}
    let L2 := {A ∈ L1 | ∀ C ∈ L0, A ∩ C ∈ L0}
    isLambdaSystem L0 ∧ L1 = L0 ∧ L2 = L0 ∧ isSigmaAlgebra L0 ∧ P ⊆ L0 := by
  set S := ⋂₀ {M | M ⊆ L ∧ LambdaSystem M ∧ P ⊆ M}
  have hS_lambda_struct : LambdaSystem S := by
    refine ⟨?_, ?_, ?_⟩
    · exact Set.mem_sInter.2 fun M hM => hM.2.1.univ_mem
    · intro A hA
      exact Set.mem_sInter.2 fun M hM => hM.2.1.compl_mem (Set.mem_sInter.1 hA M hM)
    · intro f hf hfs
      exact Set.mem_sInter.2 fun M hM =>
        hM.2.1.iUnion_mem hf fun i => Set.mem_sInter.1 (hfs i) M hM
  have hS_lambda :
      (Set.univ ∈ S) ∧ (∀ A ∈ S, Aᶜ ∈ S) ∧
        (∀ (f : ℕ → Set Ω), (Pairwise fun i j => Disjoint (f i) (f j)) →
          (∀ i, f i ∈ S) → ⋃ i, f i ∈ S) := by
    exact ⟨
      hS_lambda_struct.univ_mem,
      (fun A hA => hS_lambda_struct.compl_mem hA),
      (fun f hf hfs => hS_lambda_struct.iUnion_mem hf hfs)
    ⟩
  have hS_pi : ∀ A B, A ∈ S → B ∈ S → A ∩ B ∈ S := by
    set T := {A ∈ S | ∀ B ∈ P, A ∩ B ∈ S}
    have hT_lambda : LambdaSystem T := by
      refine ⟨?_, ?_, ?_⟩
      · refine ⟨hS_lambda_struct.univ_mem, ?_⟩
        intro B hB
        have hB_S : B ∈ S := by
          change B ∈ ⋂₀ {M | M ⊆ L ∧ LambdaSystem M ∧ P ⊆ M}
          exact Set.mem_sInter.2 fun M hM => hM.2.2 hB
        simpa using hB_S
      · intro A hA
        rcases hA with ⟨hA_mem, hA_inter⟩
        refine ⟨hS_lambda_struct.compl_mem hA_mem, ?_⟩
        intro B hB
        refine Set.mem_sInter.2 ?_
        intro M hM
        rcases hM with ⟨hM_subset_L, hM_lambda, hM_contains_P⟩
        have hAB_mem : A ∩ B ∈ M := by
          exact Set.mem_sInter.1 (hA_inter B hB) M ⟨hM_subset_L, hM_lambda, hM_contains_P⟩
        have hB_mem : B ∈ M := hM_contains_P hB
        have hdiff : B \ (A ∩ B) ∈ M := by
          exact lambda_diff_of_subset hM_lambda hAB_mem hB_mem Set.inter_subset_right
        have hEq : Aᶜ ∩ B = B \ (A ∩ B) := by
          ext x
          simp [Set.mem_diff, Set.mem_inter_iff]
          tauto
        simpa [hEq] using hdiff
      · intro f hf hfT
        refine ⟨hS_lambda_struct.iUnion_mem hf (fun i => (hfT i).1), ?_⟩
        intro B hB
        have hInter : ⋃ i, f i ∩ B ∈ S := by
          exact hS_lambda_struct.iUnion_mem
            (fun i j hij => Disjoint.mono inf_le_left inf_le_left (hf hij))
            (fun i => (hfT i).2 B hB)
        simpa [Set.iUnion_inter] using hInter
    have hS_subset_T : S ⊆ T := by
      refine Set.sInter_subset_of_mem ?_
      refine ⟨?_, hT_lambda, ?_⟩
      · intro x hx
        exact Set.mem_sInter.1 hx.1 L ⟨Set.Subset.refl _, hL_lambda, hP_subset_L⟩
      · intro A hA
        refine ⟨?_, ?_⟩
        · exact Set.mem_sInter.2 fun M hM => hM.2.2 hA
        · intro B hB
          exact Set.mem_sInter.2 fun M hM => hM.2.2 (hP_pi.2 hA hB)
    set U := {A ∈ S | ∀ C ∈ S, A ∩ C ∈ S}
    have hU_lambda : LambdaSystem U := by
      refine ⟨?_, ?_, ?_⟩
      · refine ⟨hS_lambda_struct.univ_mem, ?_⟩
        intro C hC
        simpa using hC
      · intro A hA
        rcases hA with ⟨hA_mem, hA_inter⟩
        refine ⟨hS_lambda_struct.compl_mem hA_mem, ?_⟩
        intro C hC
        have hDiff : C \ (A ∩ C) ∈ S := by
          exact lambda_diff_of_subset hS_lambda_struct (hA_inter C hC) hC Set.inter_subset_right
        have hEq : Aᶜ ∩ C = C \ (A ∩ C) := by
          ext x
          simp [Set.mem_diff, Set.mem_inter_iff]
          tauto
        simpa [hEq] using hDiff
      · intro f hf hfU
        refine ⟨hS_lambda_struct.iUnion_mem hf (fun i => (hfU i).1), ?_⟩
        intro C hC
        have hInter : ⋃ i, f i ∩ C ∈ S := by
          exact hS_lambda_struct.iUnion_mem
            (fun i j hij => Disjoint.mono inf_le_left inf_le_left (hf hij))
            (fun i => (hfU i).2 C hC)
        simpa [Set.iUnion_inter] using hInter
    have hS_subset_U : S ⊆ U := by
      have hP_subset_U : P ⊆ U := by
        intro A hA
        refine ⟨?_, ?_⟩
        · exact Set.mem_sInter.2 fun M hM => hM.2.2 hA
        · intro C hC
          have h := (hS_subset_T hC).2 A hA
          simpa [Set.inter_comm] using h
      refine Set.sInter_subset_of_mem ?_
      refine ⟨?_, hU_lambda, hP_subset_U⟩
      intro x hx
      exact Set.mem_sInter.1 hx.1 L ⟨Set.Subset.refl _, hL_lambda, hP_subset_L⟩
    exact fun A B hA hB => (hS_subset_U hA).2 B hB
  have hS_eq_L0 : S = {A | ∀ M ⊆ L, LambdaSystem M → P ⊆ M → A ∈ M} := by
    ext A
    simp [S]
  have hS_sigma :
      (Set.univ ∈ S) ∧ (∀ A ∈ S, Aᶜ ∈ S) ∧
        (∀ (f : ℕ → Set Ω), (∀ i, f i ∈ S) → ⋃ i, f i ∈ S) := by
    exact ((prob_3_8 Ω S) hS_lambda_struct).2
      ⟨⟨Set.univ, hS_lambda_struct.univ_mem⟩,
        fun {A} hA {B} hB => hS_pi A B hA hB⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hS_eq_L0 ▸ hS_lambda
  · ext A
    constructor
    · exact fun h => h.1
    · intro hA
      refine ⟨hA, ?_⟩
      intro B hB
      exact hS_eq_L0 ▸ hS_pi A B
        (hS_eq_L0 ▸ hA)
        (hS_eq_L0 ▸ fun M hM hM' hM'' => hM'' hB)
  · ext A
    constructor
    · exact fun h => h.1.1
    · intro hA
      refine ⟨⟨hA, ?_⟩, ?_⟩
      · intro B hB
        intro M hM hM' hM''
        convert hS_pi A B
          (hS_eq_L0 ▸ hA)
          (hS_eq_L0 ▸ fun N hN hN' hN'' => hN'' hB)
          |> fun h => hS_eq_L0 ▸ h
          |> fun h => h M hM hM' hM'' using 1
      · grind
  · convert hS_sigma using 1
    exact hS_eq_L0.symm
  · intro A hA
    rw [← hS_eq_L0]
    exact Set.mem_sInter.2 fun M hM => hM.2.2 hA
