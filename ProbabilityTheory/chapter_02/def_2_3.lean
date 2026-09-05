/-
TASK ID: def_2_3
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.MeasurableSpace.Defs












open Set

 
abbrev SigmaField (Ω : Type*) := MeasurableSpace Ω

 
def IsMeasurableIn {Ω : Type*} (𝓕 : SigmaField Ω) (A : Set Ω) : Prop :=
  @MeasurableSet Ω 𝓕 A



def IsSubSigmaField {Ω : Type*} (𝓖 𝓕 : SigmaField Ω) : Prop :=
  ∀ ⦃A : Set Ω⦄, IsMeasurableIn 𝓖 A → IsMeasurableIn 𝓕 A



def def_2_3 (Ω : Type*) : Type _ :=
  SigmaField Ω
