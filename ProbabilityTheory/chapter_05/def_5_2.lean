/-
TASK ID: def_5_2
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_05.def_5_1




def def_5_2 {Ω β γ : Type _}
    [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : MeasureTheory.Measure Ω) (X : Ω → β) (Y : Ω → γ) : Prop :=
  ProbabilityTheory.IndepFun X Y μ
