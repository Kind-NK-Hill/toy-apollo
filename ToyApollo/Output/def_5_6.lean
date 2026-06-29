/-
TASK ID: def_5_6
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

def def_5_6 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) {n : ℕ}
    (A : Fin n → Set Ω) : Prop :=
  Pairwise (fun i j => ProbabilityTheory.IndepSet (A i) (A j) μ)
