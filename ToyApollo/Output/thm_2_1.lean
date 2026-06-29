/-
TASK ID: thm_2_1
TYPE: Theorem_with_Proof
SOURCE PLAN: 41_chap2_algebra_of_events
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_2_4

-- WRITE FINAL LEAN CODE BELOW

open Set

theorem thm_2_1 {Ω : Type*} (E : ℕ → Set Ω) :
    (∀ ω, ω ∈ setLiminf E ↔ ∃ N : ℕ, ∀ n ≥ N, ω ∈ E n) ∧
      (∀ ω, ω ∈ setLimsup E ↔ ∀ N : ℕ, ∃ n ≥ N, ω ∈ E n) := by
  constructor
  · intro ω
    constructor
    · intro hω
      rcases mem_iUnion.mp hω with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      intro n hn
      exact mem_iInter₂.mp hN n hn
    · rintro ⟨N, hN⟩
      refine mem_iUnion.mpr ⟨N, ?_⟩
      exact mem_iInter₂.mpr hN
  · intro ω
    constructor
    · intro hω
      intro N
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
