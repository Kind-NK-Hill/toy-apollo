import ToyApollo.Output.prob_8_6_proof_support

/-!
# Problem 8.6: Poisson Approximation of Binomial Distribution

We prove that the total variation distance between Binom(n, lambda/n) and Poi(lambda)
is at most lambda^2/n (Le Cam's inequality).
-/

open Real Nat Finset
open MeasureTheory ProbabilityTheory Set
open TVCore

noncomputable section

/-- Exported wrapper for Problem 8.6. -/
theorem prob_8_6 (n : ℕ+) (lam : Set.Icc (0 : ℝ) (n : ℝ)) :
    d_TV (Binom (n : ℕ) (lam.1 / (n : ℝ))) (Poi lam.1) ≤ lam.1 ^ 2 / (n : ℝ) :=
  prob_8_6_support_result n lam

end
