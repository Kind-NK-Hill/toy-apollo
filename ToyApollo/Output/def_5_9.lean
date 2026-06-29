/-
TASK ID: def_5_9
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

def def_5_9 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (F : ℕ → Set (Set Ω)) : Prop :=
  ProbabilityTheory.iIndepSets F μ
