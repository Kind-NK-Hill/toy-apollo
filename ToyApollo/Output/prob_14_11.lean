/-
TASK ID: prob_14_11
TYPE: Problem
SOURCE PLAN: chapter14-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.prob_14_11_support

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

noncomputable section

theorem prob_14_11
    (S : prob_14_11_CouponRatioTriangularArraySetup)
    (H : thm_14_8_ProofBeyondBook (prob_14_11_theoremSetupExact S)) :
    prob_14_11_ExactStandardizedConvergence S := by
  exact ⟨prob_14_11_exact_standardized_sum_law_representation_proof S,
    prob_14_11_asymptoticNormality S H⟩
