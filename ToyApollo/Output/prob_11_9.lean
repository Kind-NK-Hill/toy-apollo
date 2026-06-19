import ToyApollo.Output.prob_11_9_proof_support

/-
TASK ID: prob_11_9
TYPE: Problem
SOURCE PLAN: chapter11-problems
TASK CONTENT:
\textbf{11.9.} Consider the experiment of throwing k distinct balls into n
distinct boxes.

Assume the locations of the balls are independent and uniformly chosen among
{1, 2,...,n}. We consider an asymptotic scenario in which k and n increase
simultaneously with k/n \to a, for some positive constant a. Let Xn denote the
number of empty boxes when the number of boxes is n. Prove that Xn/n \to e-a in
quadratic mean, and hence in probability as n \to\infty.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory

noncomputable section

open scoped BigOperators

/-- Problem 11.9: in the independent uniform occupancy experiment with
`k_n / n → a > 0`, the proportion of empty boxes converges to `e^{-a}` in
quadratic mean and hence in probability. -/
theorem prob_11_9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (boxes k : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ)
    (hModel : prob_11_9_finiteIndependentUniformEmptyBoxModel P boxes k X)
    (hRegime : prob_11_9_asymptoticRegime boxes k a)
    (hX :
      ∀ n : ℕ, AEStronglyMeasurable ((prob_11_9_emptyBoxRatio boxes X) n) P) :
    ConvergesInMeanSquare P (prob_11_9_emptyBoxRatio boxes X)
        (fun _ : Ω => Real.exp (-a)) ∧
      ConvergesInProbability P (prob_11_9_emptyBoxRatio boxes X)
        (fun _ : Ω => Real.exp (-a)) :=
  prob_11_9_support_result P boxes k X a hModel hRegime hX
