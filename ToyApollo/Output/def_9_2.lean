/-
TASK ID: def_9_2
TYPE: Definition
SOURCE PLAN: chapter9-moments-mgf
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_9_1

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def momentGeneratingFunction {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (_hX : AEMeasurable X μ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (Real.exp (t * X ω)) ∂μ

def HasMomentGeneratingFunction {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : AEMeasurable X μ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    ∀ t : ℝ, |t| < δ →
      momentGeneratingFunction μ X hX t < ⊤

def HasFiniteMomentGeneratingFunctionAt {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : AEMeasurable X μ) (t : ℝ) : Prop :=
  momentGeneratingFunction μ X hX t < ⊤

theorem momentGeneratingFunction_eq_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : AEMeasurable X μ) (t : ℝ) :
    momentGeneratingFunction μ X hX t =
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * X ω)) ∂μ := by
  rfl

noncomputable def def_9_2 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : AEMeasurable X μ) : ℝ → ℝ≥0∞ :=
  momentGeneratingFunction μ X hX
