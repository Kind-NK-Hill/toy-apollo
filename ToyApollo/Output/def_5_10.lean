import Mathlib

def def_5_10 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (A : ℕ → Set Ω) : Prop :=
  ProbabilityTheory.iIndepSet A μ

def def_5_10_randomVariables {Ω β : Type _} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : MeasureTheory.Measure Ω) (X : ℕ → Ω → β) : Prop :=
  ProbabilityTheory.iIndepFun X μ
