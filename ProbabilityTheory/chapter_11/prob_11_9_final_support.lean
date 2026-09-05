/-
TASK ID: prob_11_9_final_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_11.prob_11_9_probability_support

open Filter MeasureTheory ProbabilityTheory

noncomputable section

open scoped BigOperators



theorem prob_11_9_support_result {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (boxes k : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ)
    (hModel : prob_11_9_finiteIndependentUniformEmptyBoxModel P boxes k X)
    (hRegime : prob_11_9_asymptoticRegime boxes k a)
    (hX :
      ∀ n : ℕ, Measurable ((prob_11_9_emptyBoxRatio boxes X) n)) :
    ConvergesInMeanSquare P (prob_11_9_emptyBoxRatio boxes X)
        (fun _ : Ω => Real.exp (-a)) ∧
      ConvergesInProbability P (prob_11_9_emptyBoxRatio boxes X)
        (fun _ : Ω => Real.exp (-a)) := by
  let hMS := prob_11_9_quadratic_mean P boxes k X a hModel hRegime
    (fun n => (hX n).aestronglyMeasurable)
  exact ⟨hMS, prob_11_9_probability P boxes X a hMS hX⟩
