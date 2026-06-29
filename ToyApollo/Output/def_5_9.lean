import Mathlib

def def_5_9 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (F : ℕ → Set (Set Ω)) : Prop :=
  ProbabilityTheory.iIndepSets F μ
