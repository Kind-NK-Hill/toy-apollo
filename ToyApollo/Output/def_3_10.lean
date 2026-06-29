/-
TASK ID: def_3_10
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Pairwise.Basic

open Set

variable {Ω : Type*}

def PiSystem (P : Set (Set Ω)) : Prop :=
  ∀ ⦃A⦄, A ∈ P → ∀ ⦃B⦄, B ∈ P → A ∩ B ∈ P

structure LambdaSystem (L : Set (Set Ω)) : Prop where

  univ_mem : univ ∈ L

  compl_mem : ∀ {A}, A ∈ L → Aᶜ ∈ L

  iUnion_mem : ∀ {f : ℕ → Set Ω}, Pairwise (fun i j => Disjoint (f i) (f j)) → (∀ i, f i ∈ L) → (⋃ i, f i) ∈ L
