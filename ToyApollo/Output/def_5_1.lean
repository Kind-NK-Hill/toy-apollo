/-
TASK ID: def_5_1
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

def def_5_1 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (A B : Set Ω) : Prop :=
  ProbabilityTheory.IndepSet A B μ
