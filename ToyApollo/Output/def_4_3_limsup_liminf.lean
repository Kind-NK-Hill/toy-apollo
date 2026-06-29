/-
TASK ID: def_4_3_limsup_liminf
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_4_3_sup_inf

noncomputable def tailSup {α : Type*} [CompleteLattice α] (a : ℕ → α) (n : ℕ) : α :=
  ⨆ k : ℕ, a (n + k)

noncomputable def tailInf {α : Type*} [CompleteLattice α] (a : ℕ → α) (n : ℕ) : α :=
  ⨅ k : ℕ, a (n + k)

noncomputable def seqLimsup {α : Type*} [CompleteLattice α] (a : ℕ → α) : α :=
  ⨅ n : ℕ, tailSup a n

noncomputable def seqLiminf {α : Type*} [CompleteLattice α] (a : ℕ → α) : α :=
  ⨆ n : ℕ, tailInf a n
