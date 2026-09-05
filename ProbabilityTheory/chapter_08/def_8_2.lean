/-
TASK ID: def_8_2
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_08.def_8_1









open MeasureTheory




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
