import Mathlib

def def_5_7 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) {n : ℕ}
    (F : Fin n → Set (Set Ω)) : Prop :=
  ProbabilityTheory.iIndepSets F μ
