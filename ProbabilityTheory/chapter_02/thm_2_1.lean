/-
TASK ID: thm_2_1
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_02.def_2_4









open Set



theorem thm_2_1_part1 {Ω : Type*} (E : ℕ → Set Ω) :
   (∀ ω, ω ∈ setLiminf E ↔ ∃ N : ℕ, ∀ n ≥ N, ω ∈ E n) := by
  intro ω
  constructor
  · intro hω
    rcases mem_iUnion.mp hω with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    exact mem_iInter₂.mp hN n hn
  · rintro ⟨N, hN⟩
    refine mem_iUnion.mpr ⟨N, ?_⟩
    exact mem_iInter₂.mpr hN




theorem thm_2_1_part2 {Ω : Type*} (E : ℕ → Set Ω) :
  (∀ ω, ω ∈ setLimsup E ↔ ∀ N : ℕ, ∃ n ≥ N, ω ∈ E n) := by
  intro ω
  constructor
  · intro hω N
    rw [setLimsup, mem_iInter] at hω
    have hN := hω N
    rw [mem_iUnion] at hN
    rcases hN with ⟨n, hn⟩
    rw [mem_iUnion] at hn
    rcases hn with ⟨hnN, hmem⟩
    exact ⟨n, hnN, hmem⟩
  · intro hω
    rw [setLimsup, mem_iInter]
    intro N
    rcases hω N with ⟨n, hnN, hmem⟩
    rw [mem_iUnion]
    refine ⟨n, ?_⟩
    rw [mem_iUnion]
    exact ⟨hnN, hmem⟩


 
theorem thm_2_1 {Ω : Type*} (E : ℕ → Set Ω) :
    (∀ ω, ω ∈ setLiminf E ↔ ∃ N : ℕ, ∀ n ≥ N, ω ∈ E n) ∧
      (∀ ω, ω ∈ setLimsup E ↔ ∀ N : ℕ, ∃ n ≥ N, ω ∈ E n) := by
  exact ⟨thm_2_1_part1 E, thm_2_1_part2 E⟩
