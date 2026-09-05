/-
TASK ID: prob_14_1
TYPE: Problem
SOURCE PLAN: chapter14-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_14.prob_14_1_proof_support




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators ENNReal Asymptotics

noncomputable section



theorem prob_14_1
    (S : prob_14_1_PolyaUrnBetaSetup) :
    (∀ i k : ℕ, 1 ≤ i → k ≤ i →
      (S.whiteCountLaws i : Measure ℝ) {x : ℝ | x = (k : ℝ)} =
        ENNReal.ofReal (prob_14_1_polyaWhiteMassFormula S.w S.b i k)) ∧
      Tendsto (prob_14_1_whiteFractionLaws S.whiteCountLaws) atTop (𝓝 S.beta.law) ∧
        def_14_1 (prob_14_1_whiteFractionLaws S.whiteCountLaws) S.beta.law := by
  simpa using prob_14_1_support_result S
