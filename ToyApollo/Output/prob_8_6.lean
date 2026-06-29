/-
TASK ID: prob_8_6
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.prob_8_6_proof_support

open Real Nat Finset
open MeasureTheory ProbabilityTheory Set
open TVCore

noncomputable section

theorem prob_8_6 (n : ℕ+) (lam : Set.Icc (0 : ℝ) (n : ℝ)) :
    d_TV (Binom (n : ℕ) (lam.1 / (n : ℝ))) (Poi lam.1) ≤ lam.1 ^ 2 / (n : ℝ) :=
  prob_8_6_support_result n lam

end
