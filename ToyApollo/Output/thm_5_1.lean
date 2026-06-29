/-
TASK ID: thm_5_1
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_5_2
import ToyApollo.Output.def_5_3
import ToyApollo.Output.def_5_4

theorem thm_5_1 {Ω β γ : Type _} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsZeroOrProbabilityMeasure μ]
    (X : Ω → β) (Y : Ω → γ) :
    def_5_2 μ X Y ↔
      def_5_4 μ {s | @MeasurableSet Ω (def_5_3 X) s} {t | @MeasurableSet Ω (def_5_3 Y) t} := by
  simpa [def_5_2, def_5_3, def_5_4] using
    (ProbabilityTheory.IndepFun_iff_Indep X Y μ)
