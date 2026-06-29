import ToyApollo.Output.prob_14_8_proof_support

/-
TASK ID: prob_14_8
TYPE: Problem
SOURCE PLAN: chapter14-problems
TASK CONTENT:
\textbf{14.8.} Let (X n)\infty

n=1 be a sequence of random variables satisfying the following

properties:

(i) For all n , the moment generating function mXn (t) of Xn is defined for t \in

[-\delta, \delta].

(ii) For all t \in[ - \delta, \delta], the moment generating functions mXn (t) converge to the

moment generating function mX(t) of random variable X:

(a) Prove that the sequence (Xn)n\geq1 is tight.

(b) Prove that Xn converges to X in distribution.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set ProbabilityTheory
open scoped Topology Uniformity

noncomputable section

/-- Problem 14.8: MGF convergence on a neighborhood of zero implies tightness
and convergence in distribution to the target law. -/
theorem prob_14_8
    (S : prob_14_8_MgfConvergenceSetup) :
    def_14_3 S.laws ∧ Tendsto S.laws atTop (𝓝 S.targetLaw) := by
  simpa using prob_14_8_support_result S
