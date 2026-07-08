import Mathlib
import ToyApollo.Output.prob_13_4_support

/-
TASK ID: prob_13_4
TYPE: Problem
SOURCE PLAN: chapter13-problems
TASK CONTENT:
\textbf{13.4.} Suppose $X$ and $Y$ are jointly Gaussian random variables. Find the conditional expectation of $X$ given $Y$, in terms of the means, variances, and the covariance of $X$ and $Y$.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- Problem 13.4: for jointly Gaussian real random variables, the conditional
expectation of `X` given `Y` is the usual affine regression formula. -/
theorem prob_13_4 {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Ω → ℝ}
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
    (hXmeas : Measurable X) (hYmeas : Measurable Y)
    (hVarY : Var[Y; P] ≠ 0) :
    def_13_4 P Y (def_13_4_sigma_subSigma_of_measurable hYmeas) X
      (fun ω => (∫ ω, X ω ∂P) + (cov[X, Y; P] / Var[Y; P]) *
        (Y ω - ∫ ω, Y ω ∂P)) :=
  prob_13_4_jointlyGaussian_affine_condExp_regression hXY hXmeas hYmeas hVarY
