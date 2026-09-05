/-
TASK ID: def_10_5
TYPE: Definition
SOURCE PLAN: chapter10-distribution-total-variation
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_08.def_8_5
import ProbabilityTheory.chapter_10.def_10_4




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory



noncomputable def MeasuresConvergeInTotalVariation {Ω : Type*} [MeasurableSpace Ω]
    (Pn : ℕ → Measure Ω) (P : Measure Ω) : Prop :=
  ∃ hPn : ∀ n : ℕ, IsProbabilityMeasure (Pn n),
    ∃ hP : IsProbabilityMeasure P,
      Tendsto
        (fun n : ℕ =>
          letI := hPn n
          letI := hP
          totalVariationDistance (Pn n) P)
        atTop (nhds 0)



noncomputable def RandomVariablesConvergeInTotalVariation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  IsProbabilityMeasure μ ∧
    (∀ n : ℕ, Measurable (Xn n)) ∧
      Measurable X ∧
        MeasuresConvergeInTotalVariation
          (fun n => Measure.map (Xn n) μ) (Measure.map X μ)

 
noncomputable def def_10_5 :=
  (@MeasuresConvergeInTotalVariation, @RandomVariablesConvergeInTotalVariation)
