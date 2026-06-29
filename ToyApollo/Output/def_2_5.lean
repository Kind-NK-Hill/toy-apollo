/-
TASK ID: def_2_5
TYPE: Definition
SOURCE PLAN: 42_chap2_measure_functions
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set

abbrev MeasureOn (Ω : Type*) [MeasurableSpace Ω] := Measure Ω

def IsFiniteMeasureOn {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) : Prop :=
  μ Set.univ < ⊤

def IsProbabilityMeasureOn {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) : Prop :=
  IsProbabilityMeasure μ

structure MeasureSpaceData (Ω : Type*) [MeasurableSpace Ω] where
  measure : Measure Ω

structure ProbabilitySpaceData (Ω : Type*) [MeasurableSpace Ω] where
  measure : Measure Ω
  is_probability : IsProbabilityMeasure measure

def def_2_5 {Ω : Type*} [MeasurableSpace Ω] := Measure Ω
