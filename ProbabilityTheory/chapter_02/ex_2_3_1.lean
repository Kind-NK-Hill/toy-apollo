/-
TASK ID: ex_2_3_1
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_02.def_2_5

open MeasureTheory Set

noncomputable section

 
abbrev countingSigmaField (Ω : Type*) : MeasurableSpace Ω := ⊤

 
def countingMeasureOn (Ω : Type*) : @Measure Ω (countingSigmaField Ω) := by
  letI : MeasurableSpace Ω := countingSigmaField Ω
  exact Measure.count

 
theorem countingMeasureOn_apply (Ω : Type*) (A : Set Ω) :
    countingMeasureOn Ω A = A.encard := by
  letI : MeasurableSpace Ω := countingSigmaField Ω
  simpa [countingMeasureOn, countingSigmaField] using
    (Measure.count_apply (s := A) (by simp : MeasurableSet A))

 
def ex_2_3_1 (Ω : Type*) : @Measure Ω (countingSigmaField Ω) :=
  countingMeasureOn Ω

 
def ex_2_3_1_measureSpace (Ω : Type*) : @MeasureSpaceData Ω (countingSigmaField Ω) := by
  letI : MeasurableSpace Ω := countingSigmaField Ω
  exact ⟨ex_2_3_1 Ω⟩
