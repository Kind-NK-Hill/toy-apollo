/-
TASK ID: thm_7_13
TYPE: Theorem_with_Proof
SOURCE PLAN: 29_chap7_product_expectation
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_6_3
import ToyApollo.Output.thm_5_2

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

theorem thm_7_13 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} (hXY : def_5_2 μ X Y) (hX : Integrable X μ) (hY : Integrable Y μ)
    (hXY_int : Integrable (fun ω => X ω * Y ω) μ) :
    ∫ ω, X ω * Y ω ∂μ = (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ := by
  have hIndep : ProbabilityTheory.IndepFun X Y μ := by
    simpa [def_5_2] using hXY
  have hXm : AEStronglyMeasurable X μ := hX.1
  have hYm : AEStronglyMeasurable Y μ := hY.1
  have hNoFallback : Integrable (fun ω => X ω * Y ω) μ := hXY_int
  have hFactor :=
    hIndep.integral_bilin' (𝕜 := ℝ) hXm hYm
      (ContinuousLinearMap.lsmul ℝ ℝ) 1 (by simp) (by simp [norm_smul])
  simpa using hFactor
