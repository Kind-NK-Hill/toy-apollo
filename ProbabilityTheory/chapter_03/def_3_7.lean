/-
TASK ID: def_3_7
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Topology.Basic
import Mathlib.Data.Real.Basic




open Set

variable {X : Type*} [TopologicalSpace X]



def IsOpenCover (A : Set X) {ι : Type*} (u : ι → Set X) : Prop :=
  (∀ i, IsOpen (u i)) ∧ A ⊆ ⋃ i, u i



def IsSubcover (A : Set X) {ι : Type*} (u : ι → Set X) (J : Set ι) : Prop :=
  IsOpenCover A (fun (j : J) => u j)

 
def IsFiniteCover (A : Set X) {ι : Type*} (u : ι → Set X) : Prop :=
  IsOpenCover A u ∧ Finite ι
