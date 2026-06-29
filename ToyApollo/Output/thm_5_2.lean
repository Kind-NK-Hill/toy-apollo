import Mathlib
import ToyApollo.Output.def_5_2

theorem thm_5_2 {Ω β γ β' γ' : Type _}
    [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace β'] [MeasurableSpace γ']
    (μ : MeasureTheory.Measure Ω) (X : Ω → β) (Y : Ω → γ)
    (f : β → β') (g : γ → γ')
    (hXY : def_5_2 μ X Y) (hf : Measurable f) (hg : Measurable g) :
    def_5_2 μ (f ∘ X) (g ∘ Y) := by
  have hxy : ProbabilityTheory.IndepFun X Y μ := by
    simpa [def_5_2] using hXY
  simpa [def_5_2, Function.comp] using (ProbabilityTheory.IndepFun.comp (hfg := hxy) hf hg)
