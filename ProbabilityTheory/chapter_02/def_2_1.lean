/-
TASK ID: def_2_1
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Tactic








open Set

noncomputable section countable_set



def SameCardinality {α β : Type*} (A : Set α) (B : Set β) : Prop :=
  Nonempty (A ≃ B)

 
def IsCountableSet {α : Type*} (A : Set α) : Prop :=
  SameCardinality A (Set.univ : Set ℕ)




def IsAtMostCountableSet {α : Type*} (A : Set α) : Prop :=
  A.Countable

 
def IsUncountableSet {α : Type*} (A : Set α) : Prop :=
  A.Infinite ∧ ¬ IsCountableSet A




def def_2_1 {α : Type*} (A : Set α) : Prop :=
  IsCountableSet A

end countable_set
