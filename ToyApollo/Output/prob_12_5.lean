import Mathlib
import ToyApollo.Output.def_12_2
import ToyApollo.Output.thm_12_5

/-
TASK ID: prob_12_5
TYPE: Problem
SOURCE PLAN: chapter12-problems
TASK CONTENT:
\textbf{12.5.} We model the temperature in a forest by a random variable X. Suppose that

the mean \mu and the variance \sigma2

0 are known. The temperature is measured by a

sensor. The output of the sensor Y 1 = X + N1 is corrupted by Gaussian noise

N1 N( 0,\sigma 2

1 )Assume that N1 and X are independent, and the variance \sigma2

1 is

known.

(a) We can estimate X by \alpha(Y1 - \mu)+\mu. Find the optimal choice of constant \alpha that

minimizes the mean-squared error E[(X - \mu - \alpha(Y1 - \mu))2].

(b) We install another temperature sensor. The measurement of the second sensor is

Y2 = X + N2, where N2 N(0,\sigma 2

2 )Assume X, N1, and N2 are independent,

and the variance \sigma 2

2 is known. Find the optimal values of \alpha and \beta that minimize

E[(X - \mu - \alpha(Y1 - \mu) - \beta(Y2 - \mu))2].
-/

-- WRITE FINAL LEAN CODE BELOW

noncomputable section

/-- The one-sensor mean-squared error after centering by the known mean.
Here `v0`, `v1` denote the variances `σ₀²`, `σ₁²`. The independence and
zero-mean-noise assumptions reduce the expectation to this quadratic form. -/
def prob_12_5_oneSensorMSE (v0 v1 α : ℝ) : ℝ :=
  (1 - α) ^ 2 * v0 + α ^ 2 * v1

/-- The optimal one-sensor linear coefficient. -/
def prob_12_5_oneSensorAlpha (v0 v1 : ℝ) : ℝ :=
  v0 / (v0 + v1)

/-- The two-sensor mean-squared error after centering by the known mean.
Here `v0`, `v1`, `v2` denote `σ₀²`, `σ₁²`, `σ₂²`. -/
def prob_12_5_twoSensorMSE (v0 v1 v2 α β : ℝ) : ℝ :=
  (1 - α - β) ^ 2 * v0 + α ^ 2 * v1 + β ^ 2 * v2

/-- The common denominator in the two-sensor optimum. -/
def prob_12_5_twoSensorDen (v0 v1 v2 : ℝ) : ℝ :=
  v0 * v1 + v0 * v2 + v1 * v2

/-- The optimal coefficient of the first centered sensor output. -/
def prob_12_5_twoSensorAlpha (v0 v1 v2 : ℝ) : ℝ :=
  v0 * v2 / prob_12_5_twoSensorDen v0 v1 v2

/-- The optimal coefficient of the second centered sensor output. -/
def prob_12_5_twoSensorBeta (v0 v1 v2 : ℝ) : ℝ :=
  v0 * v1 / prob_12_5_twoSensorDen v0 v1 v2

/-- Completing the square for the one-sensor objective. -/
theorem prob_12_5_oneSensorMSE_sub_opt
    {v0 v1 : ℝ} (hden : v0 + v1 ≠ 0) (α : ℝ) :
    prob_12_5_oneSensorMSE v0 v1 α -
        prob_12_5_oneSensorMSE v0 v1 (prob_12_5_oneSensorAlpha v0 v1) =
      (v0 + v1) * (α - prob_12_5_oneSensorAlpha v0 v1) ^ 2 := by
  unfold prob_12_5_oneSensorMSE prob_12_5_oneSensorAlpha
  field_simp [hden]
  ring_nf

/-- The one-sensor optimal coefficient minimizes the centered MSE. -/
theorem prob_12_5_oneSensorAlpha_optimal
    {v0 v1 : ℝ} (hpos : 0 < v0 + v1) (α : ℝ) :
    prob_12_5_oneSensorMSE v0 v1 (prob_12_5_oneSensorAlpha v0 v1) ≤
      prob_12_5_oneSensorMSE v0 v1 α := by
  have hden : v0 + v1 ≠ 0 := ne_of_gt hpos
  have hdiff := prob_12_5_oneSensorMSE_sub_opt (v0 := v0) (v1 := v1) hden α
  have hnonneg :
      0 ≤ prob_12_5_oneSensorMSE v0 v1 α -
        prob_12_5_oneSensorMSE v0 v1 (prob_12_5_oneSensorAlpha v0 v1) := by
    rw [hdiff]
    exact mul_nonneg (le_of_lt hpos)
      (sq_nonneg (α - prob_12_5_oneSensorAlpha v0 v1))
  linarith

/-- The two-sensor square completion for any coefficients satisfying the
normal equations. -/
theorem prob_12_5_twoSensorMSE_sub_stationary
    {v0 v1 v2 α0 β0 : ℝ}
    (hα : v1 * α0 = v0 * (1 - α0 - β0))
    (hβ : v2 * β0 = v0 * (1 - α0 - β0)) (α β : ℝ) :
    prob_12_5_twoSensorMSE v0 v1 v2 α β -
        prob_12_5_twoSensorMSE v0 v1 v2 α0 β0 =
      v0 * ((1 - α - β) - (1 - α0 - β0)) ^ 2 +
        v1 * (α - α0) ^ 2 +
        v2 * (β - β0) ^ 2 := by
  have hlinear :
      v0 * (1 - α0 - β0) * ((1 - α - β) - (1 - α0 - β0)) * 2 +
          v1 * α0 * (α - α0) * 2 +
          v2 * β0 * (β - β0) * 2 = 0 := by
    rw [hα, hβ]
    ring
  calc
    prob_12_5_twoSensorMSE v0 v1 v2 α β -
        prob_12_5_twoSensorMSE v0 v1 v2 α0 β0 =
      (v0 * ((1 - α - β) - (1 - α0 - β0)) ^ 2 +
          v1 * (α - α0) ^ 2 +
          v2 * (β - β0) ^ 2) +
        (v0 * (1 - α0 - β0) * ((1 - α - β) - (1 - α0 - β0)) * 2 +
          v1 * α0 * (α - α0) * 2 +
          v2 * β0 * (β - β0) * 2) := by
        unfold prob_12_5_twoSensorMSE
        ring
    _ = v0 * ((1 - α - β) - (1 - α0 - β0)) ^ 2 +
        v1 * (α - α0) ^ 2 +
        v2 * (β - β0) ^ 2 := by
      rw [hlinear]
      ring

/-- The explicit two-sensor coefficients satisfy the normal equations. -/
theorem prob_12_5_twoSensorCoefficients_stationary
    {v0 v1 v2 : ℝ} (hden : prob_12_5_twoSensorDen v0 v1 v2 ≠ 0) :
    v1 * prob_12_5_twoSensorAlpha v0 v1 v2 =
        v0 * (1 - prob_12_5_twoSensorAlpha v0 v1 v2 -
          prob_12_5_twoSensorBeta v0 v1 v2) ∧
      v2 * prob_12_5_twoSensorBeta v0 v1 v2 =
        v0 * (1 - prob_12_5_twoSensorAlpha v0 v1 v2 -
          prob_12_5_twoSensorBeta v0 v1 v2) := by
  let D := prob_12_5_twoSensorDen v0 v1 v2
  have hD : D ≠ 0 := by
    simpa [D] using hden
  have hresidual :
      1 - v0 * v2 / D - v0 * v1 / D = v1 * v2 / D := by
    dsimp [D]
    field_simp [prob_12_5_twoSensorDen, hden]
    unfold prob_12_5_twoSensorDen
    ring_nf
  constructor
  · change v1 * (v0 * v2 / D) =
      v0 * (1 - v0 * v2 / D - v0 * v1 / D)
    rw [hresidual]
    field_simp [hD]
  · change v2 * (v0 * v1 / D) =
      v0 * (1 - v0 * v2 / D - v0 * v1 / D)
    rw [hresidual]
    field_simp [hD]

/-- Completing the square for the two-sensor objective. -/
theorem prob_12_5_twoSensorMSE_sub_opt
    {v0 v1 v2 : ℝ} (hden : prob_12_5_twoSensorDen v0 v1 v2 ≠ 0)
    (α β : ℝ) :
    prob_12_5_twoSensorMSE v0 v1 v2 α β -
        prob_12_5_twoSensorMSE v0 v1 v2
          (prob_12_5_twoSensorAlpha v0 v1 v2)
          (prob_12_5_twoSensorBeta v0 v1 v2) =
      v0 *
          ((1 - α - β) -
            (1 - prob_12_5_twoSensorAlpha v0 v1 v2 -
              prob_12_5_twoSensorBeta v0 v1 v2)) ^ 2 +
        v1 * (α - prob_12_5_twoSensorAlpha v0 v1 v2) ^ 2 +
        v2 * (β - prob_12_5_twoSensorBeta v0 v1 v2) ^ 2 := by
  have hstat := prob_12_5_twoSensorCoefficients_stationary
    (v0 := v0) (v1 := v1) (v2 := v2) hden
  exact prob_12_5_twoSensorMSE_sub_stationary
    hstat.1 hstat.2 α β

/-- The two-sensor optimal coefficients minimize the centered MSE. -/
theorem prob_12_5_twoSensorCoefficients_optimal
    {v0 v1 v2 : ℝ} (hv0 : 0 ≤ v0) (hv1 : 0 ≤ v1) (hv2 : 0 ≤ v2)
    (hden : prob_12_5_twoSensorDen v0 v1 v2 ≠ 0) (α β : ℝ) :
    prob_12_5_twoSensorMSE v0 v1 v2
        (prob_12_5_twoSensorAlpha v0 v1 v2)
        (prob_12_5_twoSensorBeta v0 v1 v2) ≤
      prob_12_5_twoSensorMSE v0 v1 v2 α β := by
  have hdiff :=
    prob_12_5_twoSensorMSE_sub_opt
      (v0 := v0) (v1 := v1) (v2 := v2) hden α β
  have hnonneg :
      0 ≤ prob_12_5_twoSensorMSE v0 v1 v2 α β -
        prob_12_5_twoSensorMSE v0 v1 v2
          (prob_12_5_twoSensorAlpha v0 v1 v2)
          (prob_12_5_twoSensorBeta v0 v1 v2) := by
    rw [hdiff]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg hv0 (sq_nonneg _))
        (mul_nonneg hv1 (sq_nonneg _)))
      (mul_nonneg hv2 (sq_nonneg _))
  linarith

/-- Problem 12.5: the optimal one-sensor coefficient is
`σ₀² / (σ₀² + σ₁²)`. With two independent sensors, the optimal coefficients are
`σ₀² σ₂² / (σ₀² σ₁² + σ₀² σ₂² + σ₁² σ₂²)` and
`σ₀² σ₁² / (σ₀² σ₁² + σ₀² σ₂² + σ₁² σ₂²)`. -/
theorem prob_12_5
    {v0 v1 v2 : ℝ} (hv0 : 0 < v0) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    (∀ α : ℝ,
      prob_12_5_oneSensorMSE v0 v1 (prob_12_5_oneSensorAlpha v0 v1) ≤
        prob_12_5_oneSensorMSE v0 v1 α) ∧
    (∀ α β : ℝ,
      prob_12_5_twoSensorMSE v0 v1 v2
          (prob_12_5_twoSensorAlpha v0 v1 v2)
          (prob_12_5_twoSensorBeta v0 v1 v2) ≤
        prob_12_5_twoSensorMSE v0 v1 v2 α β) := by
  constructor
  · intro α
    exact prob_12_5_oneSensorAlpha_optimal
      (v0 := v0) (v1 := v1) (by positivity) α
  · intro α β
    have hden_pos : 0 < prob_12_5_twoSensorDen v0 v1 v2 := by
      have h01 : 0 < v0 * v1 := mul_pos hv0 hv1
      have h02 : 0 < v0 * v2 := mul_pos hv0 hv2
      have h12 : 0 < v1 * v2 := mul_pos hv1 hv2
      unfold prob_12_5_twoSensorDen
      nlinarith [h01, h02, h12]
    exact prob_12_5_twoSensorCoefficients_optimal
      (v0 := v0) (v1 := v1) (v2 := v2)
      (le_of_lt hv0) (le_of_lt hv1) (le_of_lt hv2)
      (ne_of_gt hden_pos) α β
