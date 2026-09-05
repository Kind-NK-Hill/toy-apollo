/-
TASK ID: def_14_2
TYPE: Definition
SOURCE PLAN: chapter14-weak-convergence
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_14.def_14_1




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology

noncomputable section



def def_14_2
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X) : Prop :=
  def_14_1_randomVariableWeakConvergence μ Xseq X hXseq hX



def def_14_2_lawWeakConvergence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X) : Prop :=
  def_14_1 (def_14_1_laws μ Xseq hXseq) (def_14_1_law μ X hX)

 
theorem def_14_2_iff_expectations
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Xseq : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X) :
    def_14_2 μ Xseq X hXseq hX ↔
      ∀ h : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun n : ℕ => ∫ ω, h (Xseq n ω) ∂μ) atTop
          (𝓝 (∫ ω, h (X ω) ∂μ)) := by
  exact def_14_1_randomVariableWeakConvergence_iff_expectations μ hXseq hX



def def_14_2_mathlibConvergence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  TendstoInDistribution Xseq atTop X (fun _ : ℕ => μ) μ



theorem def_14_2_mathlibConvergence_tendsto_laws
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Xseq : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (h : def_14_2_mathlibConvergence μ Xseq X) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n : ℕ =>
        ⟨Measure.map (Xseq n) μ, Measure.isProbabilityMeasure_map
          (h.forall_aemeasurable n)⟩)
      atTop
      (𝓝 ⟨Measure.map X μ, Measure.isProbabilityMeasure_map h.aemeasurable_limit⟩) :=
  h.tendsto
