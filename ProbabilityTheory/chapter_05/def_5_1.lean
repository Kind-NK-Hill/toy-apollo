/-
TASK ID: def_5_1
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Probability.Independence.Basic



def def_5_1 {Ω : Type _} [MeasurableSpace Ω]
  (μ : MeasureTheory.Measure Ω) (A B : Set Ω) : Prop :=
  ProbabilityTheory.IndepSet A B μ




example {Ω : Type _} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    def_5_1 μ A B ↔ μ (A ∩ B) = μ A * μ B := by
  simpa [def_5_1] using
    (ProbabilityTheory.indepSet_iff_measure_inter_eq_mul hA hB μ)
