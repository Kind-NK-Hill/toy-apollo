/-
TASK ID: def_2_7
TYPE: Definition
SOURCE PLAN: 43_chap2_borel_sets
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_2_6

-- WRITE FINAL LEAN CODE BELOW

open Set MeasureTheory

@[reducible]
def generatedSigmaField {Ω : Type*} (C : Set (Set Ω)) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom C

@[reducible]
def generatedSigmaFieldSeq {Ω : Type*} (B : ℕ → Set Ω) : MeasurableSpace Ω :=
  generatedSigmaField (Set.range B)

theorem generatedSigmaField_contains {Ω : Type*} (C : Set (Set Ω)) :
    ∀ s ∈ C, @MeasurableSet Ω (generatedSigmaField C) s :=
  (thm_2_6 C).1

theorem generatedSigmaFieldSeq_contains {Ω : Type*} (B : ℕ → Set Ω) (n : ℕ) :
    @MeasurableSet Ω (generatedSigmaFieldSeq B) (B n) := by
  exact generatedSigmaField_contains (Set.range B) (B n) ⟨n, rfl⟩

def def_2_7 {Ω : Type*} (C : Set (Set Ω)) : MeasurableSpace Ω :=
  generatedSigmaField C
