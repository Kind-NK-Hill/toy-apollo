/-
TASK ID: def_5_8
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

def def_5_8 {Ω β : Type _} [MeasurableSpace Ω] [MeasurableSpace β] (μ : MeasureTheory.Measure Ω) {n : ℕ}
    (X : Fin n → Ω → β) : Prop :=
  ProbabilityTheory.iIndepFun X μ
