/-
TASK ID: def_7_2
TYPE: Definition
SOURCE PLAN: 28_chap7_pushforward_change_of_variable
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_7_10

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory

noncomputable def PushForwardMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) : Measure ℝ :=
  pushForwardRealMeasure μ X

noncomputable def ImageMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) : Measure ℝ :=
  PushForwardMeasure μ X

noncomputable def InducedMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) : Measure ℝ :=
  PushForwardMeasure μ X

noncomputable def RandomVariableDistribution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (X : Ω → ℝ) : Measure ℝ :=
  PushForwardMeasure μ X

theorem distribution_isProbabilityMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X) :
    IsProbabilityMeasure (RandomVariableDistribution μ X) := by
  simpa [RandomVariableDistribution, PushForwardMeasure, pushForwardRealMeasure] using
    (Measure.isProbabilityMeasure_map hX.aemeasurable)

noncomputable def def_7_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) : Measure ℝ :=
  PushForwardMeasure μ X
