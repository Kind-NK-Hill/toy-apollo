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
    (X : Ω → ℝ) (hX : Measurable X) : Measure ℝ :=
  Thm710Support.constructedPushForward μ X hX

theorem PushForwardMeasure_apply {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (hX : Measurable X) {B : Set ℝ} (hB : MeasurableSet B) :
    PushForwardMeasure μ X hX B = μ (X ⁻¹' B) :=
  Thm710Support.constructedPushForward_apply μ X hX hB

noncomputable def ImageMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (hX : Measurable X) : Measure ℝ :=
  PushForwardMeasure μ X hX

noncomputable def InducedMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (hX : Measurable X) : Measure ℝ :=
  PushForwardMeasure μ X hX

noncomputable def RandomVariableDistribution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) : Measure ℝ :=
  PushForwardMeasure μ X hX

theorem distribution_isProbabilityMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X) :
    IsProbabilityMeasure (RandomVariableDistribution μ X hX) := by
  rw [RandomVariableDistribution, PushForwardMeasure,
    ← pushForwardRealMeasure_eq_constructed μ X hX]
  unfold pushForwardRealMeasure
  exact Measure.isProbabilityMeasure_map hX.aemeasurable

noncomputable def def_7_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (hX : Measurable X) : Measure ℝ :=
  PushForwardMeasure μ X hX
