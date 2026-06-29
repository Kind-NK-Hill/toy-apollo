/-
TASK ID: def_5_7
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

def def_5_7 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) {n : ℕ}
    (F : Fin n → Set (Set Ω)) : Prop :=
  ProbabilityTheory.iIndepSets F μ
