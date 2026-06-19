import ToyApollo.Output.prob_14_11_support

/-
TASK ID: prob_14_11
TYPE: Problem
SOURCE PLAN: chapter14-problems
TASK CONTENT:
\textbf{14.11.} Generalize Example 14.4.3 to the case when m/n approaches a fixed

constant r,f o r0 <r < 1.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

noncomputable section

/-- Problem 14.11: Example 14.4.3 generalizes from `m/n -> 1/2` to any
fixed `r` with `0 < r < 1`, using the exact row centering and variance
normalization required by Theorem 14.8.  The fixed-`r` textbook centering is
not asserted from the ratio-only hypothesis. -/
theorem prob_14_11
    (S : prob_14_11_CouponRatioTriangularArraySetup)
    (H : thm_14_8_ProofBeyondBook (prob_14_11_theoremSetupExact S)) :
    prob_14_11_ExactStandardizedConvergence S := by
  exact ⟨prob_14_11_exact_standardized_sum_law_representation_proof S,
    prob_14_11_asymptoticNormality S H⟩
