/-
TASK ID: def_8_2
TYPE: Definition
SOURCE PLAN: 31_chap8_coupling
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_8_1

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory

structure DeterministicCoupling
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    extends Coupling P Q where
  T : α → β
  measurable_T : Measurable T
  Y_eq_transport : Y = T ∘ X

noncomputable def TransportMap
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {P : Measure α} {Q : Measure β} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (π : DeterministicCoupling P Q) : α → β :=
  π.T

noncomputable def def_8_2
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :=
  DeterministicCoupling P Q
