import ToyApollo.Output.ex_14_4_1_proof_support

/-
TASK ID: ex_14_4_1
TYPE: Example_Proof
SOURCE PLAN: chapter14-central-limit-theorems
TASK CONTENT:
\textbf{Example 14.4.1 (Normal Approximation of Binomial Distribution)} \\

Suppose Xn's are iid. Bernoulli random variables with success probability p The mean and

variance of. Xn are p andp(1- p), respectively.
The sumSn =X 1 +X2 +\cdot\cdot\cdot+ Xn has distribution

Binom(n, p)By the central limit theorem,

Sn -np\sqrt np(1- p)

D

-\to N( 0,1).
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

/-- Example 14.4.1: for iid Bernoulli variables with success probability `p`,
the standardized binomial finite-sum laws converge in distribution to the
standard normal law.  The proof layer is kept in the parent-owned support file. -/
theorem ex_14_4_1
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω)
    (hSource : ex_14_4_1_bernoulliSourceLaw S) :
    Tendsto (ex_14_4_1_standardizedBinomialLaws S)
      atTop (𝓝 thm_14_7_standardNormalLaw) := by
  simpa using ex_14_4_1_support_result S hSource
