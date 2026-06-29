/-
TASK ID: thm_3_3
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.def_3_5
import Mathlib

open MeasureTheory Set ENNReal

theorem temp_blala (F : StieltjesMeasureFunction) :
    ∃! μ : Measure ℝ, ∀ a b : ℝ, μ (Ioc a b) = ENNReal.ofReal (F b - F a) := by
  refine ⟨F.toStieltjesFunction.measure, ?_, ?_⟩
  · intro a b
    simpa [StieltjesMeasureFunction.toStieltjesFunction] using
      (F.toStieltjesFunction.measure_Ioc a b)
  · intro ν hν
    symm
    apply Measure.ext_of_Ioc F.toStieltjesFunction.measure ν
    intro a b hab
    rw [hν a b]
    simpa [StieltjesMeasureFunction.toStieltjesFunction] using
      (F.toStieltjesFunction.measure_Ioc a b)
