/-
TASK ID: def_14_1
TYPE: Definition
SOURCE PLAN: chapter14-weak-convergence
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_7_11

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology

noncomputable section

def def_14_1_weakConvergence
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ) : Prop :=
  ∀ h : BoundedContinuousFunction ℝ ℝ,
    Tendsto (fun n : ℕ => ∫ x, h x ∂(Pseq n : Measure ℝ)) atTop
      (𝓝 (∫ x, h x ∂(P : Measure ℝ)))

def def_14_1
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ) : Prop :=
  def_14_1_weakConvergence Pseq P

theorem def_14_1_iff_tendsto
    {Pseq : ℕ → ProbabilityMeasure ℝ} {P : ProbabilityMeasure ℝ} :
    def_14_1 Pseq P ↔ Tendsto Pseq atTop (𝓝 P) := by
  simpa [def_14_1, def_14_1_weakConvergence] using
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto
      (F := atTop) (μs := Pseq) (μ := P)).symm

def def_14_1_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) : ProbabilityMeasure ℝ :=
  ⟨Measure.map X μ, Measure.isProbabilityMeasure_map hX.aemeasurable⟩

def def_14_1_laws {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ n : ℕ, Measurable (X n)) :
    ℕ → ProbabilityMeasure ℝ :=
  fun n => def_14_1_law μ (X n) (hX n)

theorem def_14_1_changeOfVariables_boundedContinuous
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → ℝ} (hX : Measurable X)
    (h : BoundedContinuousFunction ℝ ℝ) :
    ∫ ω, h (X ω) ∂μ = ∫ x, h x ∂Measure.map X μ := by
  exact (thm_7_11 μ hX (map_continuous h).measurable).2

def def_14_1_randomVariableWeakConvergence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X) : Prop :=
  ∀ h : BoundedContinuousFunction ℝ ℝ,
    Tendsto (fun n : ℕ => ∫ x, h x ∂Measure.map (Xseq n) μ) atTop
      (𝓝 (∫ x, h x ∂Measure.map X μ))

theorem def_14_1_randomVariableWeakConvergence_iff_expectations
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Xseq : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X) :
    def_14_1_randomVariableWeakConvergence μ Xseq X hXseq hX ↔
      ∀ h : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun n : ℕ => ∫ ω, h (Xseq n ω) ∂μ) atTop
          (𝓝 (∫ ω, h (X ω) ∂μ)) := by
  constructor
  · intro hWeak h
    have hLaw := hWeak h
    convert hLaw using 1
    · ext n
      exact def_14_1_changeOfVariables_boundedContinuous μ (hXseq n) h
    · exact congrArg (fun y : ℝ => 𝓝 y)
        (def_14_1_changeOfVariables_boundedContinuous μ hX h)
  · intro hExp
    intro h
    have hOriginal := hExp h
    convert hOriginal using 1
    · ext n
      exact (def_14_1_changeOfVariables_boundedContinuous μ (hXseq n) h).symm
    · exact congrArg (fun y : ℝ => 𝓝 y)
        (def_14_1_changeOfVariables_boundedContinuous μ hX h).symm
