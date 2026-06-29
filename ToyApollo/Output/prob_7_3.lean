/-
TASK ID: prob_7_3
TYPE: Problem
SOURCE PLAN: 30_chap7_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.prob_7_3_proof_support

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set Filter

noncomputable section

theorem prob_7_3
    {a b : ℝ} {f : ℝ → ℝ} {α : StieltjesFunction ℝ}
    (hab : a < b)
    (hBounded : ∃ M, ∀ x ∈ Icc a b, |f x| ≤ M)
    (hAtom : α.measure {a} = 0) :
    (RSIntegrable f α a b ↔
      ∀ᵐ x ∂(α.measure.restrict (Icc a b)), ContinuousWithinAt f (Icc a b) x) ∧
    (∀ hRS : RSIntegrable f α a b,
      IntegrableOn (fun x : NullMeasurableSpace ℝ α.measure => f x) (Icc a b)
          α.measure.completion ∧
        rsIntegral f α a b hRS =
          ∫ x in Icc a b, (fun x : NullMeasurableSpace ℝ α.measure => f x) x
            ∂α.measure.completion) := by
  simpa using prob_7_3_support_result
    (a := a) (b := b) (f := f) (α := α) hab hBounded hAtom
