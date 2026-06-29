import Mathlib
import ToyApollo.Output.def_5_1

def def_5_4 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (F₁ F₂ : Set (Set Ω)) : Prop :=
  ProbabilityTheory.IndepSets F₁ F₂ μ
