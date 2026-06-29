/-
TASK ID: ex_5_1_1
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_5_2

noncomputable def ex_5_1_1_U (x : ℝ) : ℤ := Int.floor (10 * x)

noncomputable def ex_5_1_1_V (y : ℝ) : ℝ := (0 : ℝ) - Real.log y

theorem measurable_ex_5_1_1_U : Measurable ex_5_1_1_U := by
  simpa [ex_5_1_1_U] using (measurable_const.mul measurable_id).floor

theorem measurable_ex_5_1_1_V : Measurable ex_5_1_1_V := by
  simpa [ex_5_1_1_V] using (measurable_const.sub Real.measurable_log)

theorem ex_5_1_1 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (X Y : Ω → ℝ) (hXY : def_5_2 μ X Y) :
    def_5_2 μ (fun ω => ex_5_1_1_U (X ω)) (fun ω => ex_5_1_1_V (Y ω)) := by
  have hxy : ProbabilityTheory.IndepFun X Y μ := by
    simpa [def_5_2] using hXY
  change ProbabilityTheory.IndepFun (fun ω => ex_5_1_1_U (X ω)) (fun ω => ex_5_1_1_V (Y ω)) μ
  simpa [Function.comp] using
    (ProbabilityTheory.IndepFun.comp (hfg := hxy) measurable_ex_5_1_1_U measurable_ex_5_1_1_V)
