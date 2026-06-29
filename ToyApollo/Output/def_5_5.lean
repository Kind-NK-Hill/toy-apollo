import Mathlib

def def_5_5 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) {n : ℕ}
    (A : Fin n → Set Ω) : Prop :=
  ProbabilityTheory.iIndepSet A μ
