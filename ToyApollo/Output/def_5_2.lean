import Mathlib
import ToyApollo.Output.def_5_1

def def_5_2 {Ω β γ : Type _} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : MeasureTheory.Measure Ω) (X : Ω → β) (Y : Ω → γ) : Prop :=
  ProbabilityTheory.IndepFun X Y μ
