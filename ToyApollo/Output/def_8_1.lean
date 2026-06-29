/-
TASK ID: def_8_1
TYPE: Definition
SOURCE PLAN: 31_chap8_coupling
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory

structure Coupling
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] where
  Ω : Type*
  instMeasurableSpaceΩ : MeasurableSpace Ω
  μ : Measure Ω
  instIsProbabilityMeasureμ : IsProbabilityMeasure μ
  X : Ω → α
  Y : Ω → β
  measurable_X : Measurable X
  measurable_Y : Measurable Y
  map_X : Measure.map X μ = P
  map_Y : Measure.map Y μ = Q

attribute [instance] Coupling.instMeasurableSpaceΩ Coupling.instIsProbabilityMeasureμ

noncomputable def def_8_1
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :=
  Coupling P Q
