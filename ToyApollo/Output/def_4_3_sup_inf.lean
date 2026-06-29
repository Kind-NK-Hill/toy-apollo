/-
TASK ID: def_4_3_sup_inf
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

open Set

abbrev IsSupremum (A : Set ℝ) (r : ℝ) : Prop :=
  IsLUB A r

abbrev IsInfimum (A : Set ℝ) (s : ℝ) : Prop :=
  IsGLB A s

noncomputable def seqSup {α : Type*} [CompleteLattice α] (a : ℕ → α) : α :=
  iSup a

noncomputable def seqInf {α : Type*} [CompleteLattice α] (a : ℕ → α) : α :=
  iInf a

noncomputable def setSupEReal (A : Set ℝ) : EReal :=
  sSup ((fun x : ℝ => (x : EReal)) '' A)

noncomputable def setInfEReal (A : Set ℝ) : EReal :=
  sInf ((fun x : ℝ => (x : EReal)) '' A)
