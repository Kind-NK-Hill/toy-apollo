import Mathlib
import ToyApollo.Output.def_2_5

open MeasureTheory Set

noncomputable section

/-- The power-set sigma-field on a countable sample space. -/
abbrev countingSigmaField (Ω : Type*) : MeasurableSpace Ω := ⊤

/-- Counting measure on the full sigma-field. -/
def countingMeasureOn (Ω : Type*) : @Measure Ω (countingSigmaField Ω) := by
  letI : MeasurableSpace Ω := countingSigmaField Ω
  exact Measure.count

/-- Under the power-set sigma-field, counting measure agrees with cardinality. -/
theorem countingMeasureOn_apply (Ω : Type*) (A : Set Ω) :
    countingMeasureOn Ω A = A.encard := by
  letI : MeasurableSpace Ω := countingSigmaField Ω
  simpa [countingMeasureOn, countingSigmaField] using
    (Measure.count_apply (s := A) (by simp : MeasurableSet A))

/-- Exported declaration for Example 2.3.1. -/
def ex_2_3_1 (Ω : Type*) : @Measure Ω (countingSigmaField Ω) :=
  countingMeasureOn Ω

/-- The counting measure example indeed packages a measure on the full sigma-field. -/
def ex_2_3_1_measureSpace (Ω : Type*) : @MeasureSpaceData Ω (countingSigmaField Ω) := by
  letI : MeasurableSpace Ω := countingSigmaField Ω
  exact ⟨ex_2_3_1 Ω⟩
