import Mathlib
import ToyApollo.Output.def_5_2

/-- The discrete transform in Example 5.1.1. -/
noncomputable def ex_5_1_1_U (x : ℝ) : ℤ := Int.floor (10 * x)

/-- The continuous transform in Example 5.1.1. -/
noncomputable def ex_5_1_1_V (y : ℝ) : ℝ := (0 : ℝ) - Real.log y

theorem measurable_ex_5_1_1_U : Measurable ex_5_1_1_U := by
  simpa [ex_5_1_1_U] using (measurable_const.mul measurable_id).floor

theorem measurable_ex_5_1_1_V : Measurable ex_5_1_1_V := by
  simpa [ex_5_1_1_V] using (measurable_const.sub Real.measurable_log)

/--
Example 5.1.1: if `X` and `Y` are independent, then applying the textbook transforms
`⌊10X⌋` and `-log Y` still yields independent random variables, even though one is discrete
and the other is continuous.
-/
theorem ex_5_1_1 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (X Y : Ω → ℝ) (hXY : def_5_2 μ X Y) :
    def_5_2 μ (fun ω => ex_5_1_1_U (X ω)) (fun ω => ex_5_1_1_V (Y ω)) := by
  have hxy : ProbabilityTheory.IndepFun X Y μ := by
    simpa [def_5_2] using hXY
  change ProbabilityTheory.IndepFun (fun ω => ex_5_1_1_U (X ω)) (fun ω => ex_5_1_1_V (Y ω)) μ
  simpa [Function.comp] using
    (ProbabilityTheory.IndepFun.comp (hfg := hxy) measurable_ex_5_1_1_U measurable_ex_5_1_1_V)
