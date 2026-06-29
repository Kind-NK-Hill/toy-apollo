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
    (_hXY_int : Integrable (fun ω => X ω * Y ω) μ) :
    ∫ ω, X ω * Y ω ∂μ = (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ := by
  simpa [def_5_2] using
    (ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral
      (μ := μ) (X := X) (Y := Y) hXY hX.1 hY.1)
