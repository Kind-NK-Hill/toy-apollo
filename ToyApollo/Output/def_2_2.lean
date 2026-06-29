/-
TASK ID: def_2_2
TYPE: Definition
SOURCE PLAN: 41_chap2_algebra_of_events
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open Set

structure EventAlgebra (Ω : Type*) where
  carrier : Set (Set Ω)
  univ_mem : Set.univ ∈ carrier
  union_mem : ∀ {A B : Set Ω}, A ∈ carrier → B ∈ carrier → A ∪ B ∈ carrier
  compl_mem : ∀ {A : Set Ω}, A ∈ carrier → Aᶜ ∈ carrier

def IsEvent {Ω : Type*} (𝓕 : EventAlgebra Ω) (A : Set Ω) : Prop :=
  A ∈ 𝓕.carrier

def def_2_2 (Ω : Type*) : Type _ :=
  EventAlgebra Ω
