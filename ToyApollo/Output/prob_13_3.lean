import Mathlib
import ToyApollo.Output.prob_13_4

/-
TASK ID: prob_13_3
TYPE: Problem
SOURCE PLAN: chapter13-problems
TASK CONTENT:
\textbf{13.3.} The joint pdf of two jointly Gaussian random variables $X_1$ and $X_2$ is given in (1.3). Find the conditional expectation of $X_2$ given $X_1=x$.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- The conditional mean of `X_2` given `X_1 = x` for the zero-mean
bivariate Gaussian density in (1.3). -/
def prob_13_3_condExpX2GivenX1
    (sigma1 sigma2 rho x : ℝ) : ℝ :=
  (rho * sigma2 / sigma1) * x

/-- Problem 13.3: for the zero-mean bivariate Gaussian density (1.3), the
conditional expectation of `X_2` given `X_1` is the linear regression function
`x ↦ rho * sigma2 / sigma1 * x`. -/
theorem prob_13_3 {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X1 X2 : Ω → ℝ}
    {sigma1 sigma2 rho : ℝ}
    (hXY : HasGaussianLaw (fun ω => (X2 ω, X1 ω)) P)
    (hX1meas : Measurable X1) (hX2meas : Measurable X2)
    (hsigma1 : 0 < sigma1) (_hsigma2 : 0 < sigma2)
    (_hrho_left : -1 < rho) (_hrho_right : rho < 1)
    (hMean1 : ∫ ω, X1 ω ∂P = 0)
    (hMean2 : ∫ ω, X2 ω ∂P = 0)
    (hVar1 : Var[X1; P] = sigma1 ^ 2)
    (hCov21 : cov[X2, X1; P] = rho * sigma1 * sigma2) :
    def_13_4 P X1 (def_13_4_sigma_subSigma_of_measurable hX1meas) X2
      (fun ω => prob_13_3_condExpX2GivenX1 sigma1 sigma2 rho (X1 ω)) := by
  have hVar_ne : Var[X1; P] ≠ 0 := by
    rw [hVar1]
    exact pow_ne_zero 2 (ne_of_gt hsigma1)
  have hCE := prob_13_4 (P := P) (X := X2) (Y := X1)
    hXY hX2meas hX1meas hVar_ne
  convert hCE using 1
  ext ω
  rw [hMean1, hMean2, hVar1, hCov21]
  unfold prob_13_3_condExpX2GivenX1
  field_simp [ne_of_gt hsigma1]
  ring
