/-
TASK ID: def_2_5
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Tactic
-- import Mathlib.MeasureTheory.MeasurableSpace.Defs
-- import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open MeasureTheory Set

abbrev MeasureOn (Ω : Type*) [MeasurableSpace Ω] := Measure Ω

def IsFiniteMeasureOn {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) : Prop :=
  μ Set.univ < ⊤

def IsProbabilityMeasureOn {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) : Prop :=
  IsProbabilityMeasure μ

structure MeasureSpaceData (Ω : Type*) [MeasurableSpace Ω] where
  measure : Measure Ω

structure ProbabilitySpaceData (Ω : Type*) [MeasurableSpace Ω]
  extends MeasureSpaceData Ω where
  (is_probability : IsProbabilityMeasure measure)

-- structure ProbabilitySpaceData (Ω : Type*) [MeasurableSpace Ω] where
--   measure : Measure Ω
--   is_probability : IsProbabilityMeasure measure

def def_2_5 {Ω : Type*} [MeasurableSpace Ω] := Measure Ω

section checking_ENNReal

open ENNReal

-- c + ∞ = ∞
example (c : ENNReal) : c + ∞ = ∞ := by
  exact add_top c

-- ∞ · ∞ = ∞
example : ∞ * ∞ = ∞ := by
  exact top_mul_top

end checking_ENNReal
