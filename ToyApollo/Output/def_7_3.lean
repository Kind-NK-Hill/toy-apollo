/-
TASK ID: def_7_3
TYPE: Definition
SOURCE PLAN: 29_chap7_product_expectation
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_7_13

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory

def Uncorrelated {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  ∫ ω, X ω * Y ω ∂μ = (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ

noncomputable def Covariance {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → ℝ) : ℝ :=
  ProbabilityTheory.covariance X Y μ

theorem covariance_zero_iff_uncorrelated {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Covariance μ X Y = 0 ↔ Uncorrelated μ X Y := by
  rw [Covariance, ProbabilityTheory.covariance_eq_sub hX hY, Uncorrelated]
  rw [sub_eq_zero]
  simpa [Pi.mul_apply]

theorem independent_uncorrelated {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℝ}
    (hXY : def_5_2 μ X Y) (hX : Integrable X μ) (hY : Integrable Y μ)
    (hXY_int : Integrable (fun ω => X ω * Y ω) μ) :
    Uncorrelated μ X Y := by
  exact thm_7_13 hXY hX hY hXY_int

def def_7_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  Uncorrelated μ X Y
