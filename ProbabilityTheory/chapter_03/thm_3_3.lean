/-
TASK ID: thm_3_3
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_03.def_3_5




open MeasureTheory Set ENNReal



theorem thm_3_3 (F : StieltjesMeasureFunction) :
    ∃! μ : Measure ℝ, ∀ a b : ℝ, μ (Ioc a b) = ENNReal.ofReal (F b - F a) := by
  refine ⟨F.toStieltjesFunction.measure, ?_, ?_⟩
  · intro a b
    simp [StieltjesMeasureFunction.toStieltjesFunction]
  · intro ν hν
    symm
    apply Measure.ext_of_Ioc F.toStieltjesFunction.measure ν
    intro a b hab
    rw [hν a b]
    simp [StieltjesMeasureFunction.toStieltjesFunction]
