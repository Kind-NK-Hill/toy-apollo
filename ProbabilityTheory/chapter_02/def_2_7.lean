/-
TASK ID: def_2_7
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Tactic
import ProbabilityTheory.chapter_02.thm_2_6








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



@[reducible]
def def_2_7 {Ω : Type*} (C : Set (Set Ω)) : MeasurableSpace Ω :=
  generatedSigmaField C
