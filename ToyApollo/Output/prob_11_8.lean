import Mathlib
import ToyApollo.Output.def_5_10
import ToyApollo.Output.thm_11_2
import ToyApollo.Output.prob_11_7

/-
TASK ID: prob_11_8
TYPE: Problem
SOURCE PLAN: chapter11-problems
TASK CONTENT:
\textbf{11.8.} Define a first-order autocorrelation process by X0 = 0 and Xi = \rhoXi- 1 + Ni

for i \geq 1, where \rho is a constant with \vert\rho\vert < 1 and Ni is a Gaussian random variable

N( 0,\sigma 2)Assume that the random variables Ni 's are independent. Show that

(X1 + X2 +\cdot\cdot\cdot+ Xi)/i converges to 0 in probability as i \to\infty .
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory

/-- The AR(1) assumptions from Problem 11.8, with the Gaussian innovation facts
encoded by their mean/variance and independence consequences. -/
def prob_11_8_ar1Assumptions {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X N : ℕ → Ω → ℝ) (ρ σ2 : ℝ) : Prop :=
  (∀ ω : Ω, X 0 ω = 0) ∧
    |ρ| < 1 ∧
    0 ≤ σ2 ∧
    (∀ i : ℕ, X (i + 1) = fun ω => ρ * X i ω + N (i + 1) ω) ∧
    (∀ i : ℕ, P[N i] = 0) ∧
    (∀ i : ℕ, _root_.variance P (N i) = σ2) ∧
    def_5_10_randomVariables P N

/-- Internalized open math debt: derive the geometric covariance-decay package
for a stable AR(1) process from the recursion and independent Gaussian
innovations.  The current local interface records only the moments and
independence of the innovations, so this calculation is not yet theorem-level
formalized. -/
private axiom prob_11_8_covarianceDecaySupport_internal {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X N : ℕ → Ω → ℝ) (ρ σ2 : ℝ)
    (_hAR : prob_11_8_ar1Assumptions P X N ρ σ2) :
    ∃ K : ℝ, ∃ a : ℕ → ℝ, prob_11_7_covarianceDecayAssumptions P X 0 K a

/-- Problem 11.8: the sample averages of the stable first-order
autocorrelation process converge to `0` in probability. -/
theorem prob_11_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X N : ℕ → Ω → ℝ) (ρ σ2 : ℝ)
    (hAR : prob_11_8_ar1Assumptions P X N ρ σ2) :
    ConvergesInProbability P (fun n => thm_11_5_sampleMean X n) (fun _ => 0) := by
  rcases prob_11_8_covarianceDecaySupport_internal P X N ρ σ2 hAR with
    ⟨K, a, hDecay⟩
  exact prob_11_7 P X 0 K a hDecay
