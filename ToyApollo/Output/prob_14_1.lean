import ToyApollo.Output.prob_14_1_proof_support

/-
TASK ID: prob_14_1
TYPE: Problem
SOURCE PLAN: chapter14-problems
TASK CONTENT:
\textbf{14.1.} Continue with the probabilistic model of Polya's urn in Problem 13.11F o r

i = 1 ,2,3,... ,l e tXi and Yi , respectively, be numbers of white and black balls

drawn in the first i steps. They satisfy Xi \geq 0, Yi \geq 0, and Xi + Yi = i for all i:

(a) Show that, for k = 1,2,3,... ,i, the probability of Xi = k is

P(Xi =k) =

( i

k

) w(w+ 1 )\cdot\cdot\cdot (w+ k - 1 )b(b+ 1 )\cdot\cdot\cdot (b+ i - k - 1 )

(b+ w)(b + w + 1 )\cdot\cdot\cdot (b+ w + i - 1 ) .

(b) Hence, show that Xi/i converges in distribution to Beta(w, b).

(Hint: Use Stirling's approximation and ( x + a)/ (x +b) xa-b.)
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators ENNReal Asymptotics

noncomputable section

/-- Problem 14.1: Polya's urn has the displayed finite-time white-count
probability formula, and the scaled white count converges to the Beta law. -/
theorem prob_14_1
    (S : prob_14_1_PolyaUrnBetaSetup) :
    (∀ i k : ℕ, 1 ≤ i → k ≤ i →
      (S.whiteCountLaws i : Measure ℝ) {x : ℝ | x = (k : ℝ)} =
        ENNReal.ofReal (prob_14_1_polyaWhiteMassFormula S.w S.b i k)) ∧
      Tendsto (prob_14_1_whiteFractionLaws S.whiteCountLaws) atTop (𝓝 S.beta.law) ∧
        def_14_1 (prob_14_1_whiteFractionLaws S.whiteCountLaws) S.beta.law := by
  simpa using prob_14_1_support_result S
