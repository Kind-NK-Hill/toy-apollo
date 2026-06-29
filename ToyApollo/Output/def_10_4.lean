/-
TASK ID: def_10_4
TYPE: Definition
SOURCE PLAN: chapter10-distribution-total-variation
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set

def CdfConvergesInDistribution (Fn : ℕ → ℝ → ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, ContinuousAt F x → Tendsto (fun n : ℕ => Fn n x) atTop (nhds (F x))

noncomputable def measureCdf (μ : Measure ℝ) (x : ℝ) : ℝ :=
  μ.real (Iic x)

noncomputable def MeasuresConvergeInDistribution (μn : ℕ → Measure ℝ) (μ : Measure ℝ) :
    Prop :=
  CdfConvergesInDistribution (fun n x => measureCdf (μn n) x) (measureCdf μ)

noncomputable def RandomVariablesConvergeInDistribution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  MeasuresConvergeInDistribution (fun n => Measure.map (Xn n) μ) (Measure.map X μ)

noncomputable def def_10_4 :=
  (@CdfConvergesInDistribution, @MeasuresConvergeInDistribution,
    @RandomVariablesConvergeInDistribution)
