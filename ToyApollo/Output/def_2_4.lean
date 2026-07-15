/-
TASK ID: def_2_4
TYPE: Definition
SOURCE PLAN: 41_chap2_algebra_of_events
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open Set

def setLiminf {Ω : Type*} (E : ℕ → Set Ω) : Set Ω :=
  ⋃ n : ℕ, ⋂ m ∈ Set.Ici n, E m

def setLimsup {Ω : Type*} (E : ℕ → Set Ω) : Set Ω :=
  ⋂ n : ℕ, ⋃ m ∈ Set.Ici n, E m

def setSeqLimitExists {Ω : Type*} (E : ℕ → Set Ω) : Prop :=
  setLiminf E = setLimsup E

theorem setLiminf_subset_setLimsup {Ω : Type*} (E : ℕ → Set Ω) :
    setLiminf E ⊆ setLimsup E := by
  intro x hx
  rcases mem_iUnion.mp hx with ⟨j, hj⟩
  rw [setLimsup, mem_iInter]
  intro n
  rw [mem_iUnion]
  refine ⟨max n j, ?_⟩
  rw [mem_iUnion]
  refine ⟨le_max_left n j, ?_⟩
  exact mem_iInter₂.mp hj (max n j) (le_max_right n j)

def def_2_4 {Ω : Type*} (E : ℕ → Set Ω)
    (_h : setSeqLimitExists E) : Set Ω :=
  setLiminf E

@[simp] theorem def_2_4_eq_setLiminf {Ω : Type*} (E : ℕ → Set Ω)
    (h : setSeqLimitExists E) :
    def_2_4 E h = setLiminf E := rfl

theorem def_2_4_eq_setLimsup {Ω : Type*} (E : ℕ → Set Ω)
    (h : setSeqLimitExists E) :
    def_2_4 E h = setLimsup E := by
  exact h
