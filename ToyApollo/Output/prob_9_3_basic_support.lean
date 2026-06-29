import Mathlib
import ToyApollo.Output.def_9_3
import ToyApollo.Output.thm_9_3

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

noncomputable section

noncomputable def sourceScaleGammaMeasure (alpha beta : ℝ) : Measure ℝ :=
  gammaMeasure alpha beta⁻¹

theorem sourceScaleGammaMeasure_isProbabilityMeasure
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    IsProbabilityMeasure (sourceScaleGammaMeasure alpha beta) := by
  simpa [sourceScaleGammaMeasure] using
    isProbabilityMeasure_gammaMeasure halpha (inv_pos.mpr hbeta)

/-- Scale-`beta` Gamma characteristic-function formula:
`(1 - i beta t)^(-alpha)`, written in the exponential-log form used by the
prompt-pack characteristic-function route. -/
noncomputable def gammaCharacteristicFunctionFormula
    (alpha beta t : ℝ) : ℂ :=
  Complex.exp ((alpha : ℂ) *
    Complex.log ((1 : ℂ) /
      ((1 : ℂ) - Complex.I * (beta : ℂ) * (t : ℂ))))

/-- Rate-`r` Gamma characteristic-function formula in Mathlib's parameter
convention. This is only a formula helper; it does not assert that
`gammaMeasure alpha r` has this characteristic function. -/
noncomputable def gammaCharacteristicFunctionRateFormula
    (alpha r t : ℝ) : ℂ :=
  Complex.exp ((alpha : ℂ) *
    Complex.log ((r : ℂ) / ((r : ℂ) - Complex.I * (t : ℂ))))

/-- The open right half-plane for complex-rate parameters. This is the natural
domain for a contour-free analytic-continuation route from Mathlib's positive
real-rate Gamma integral to the needed complex-rate integral. -/
def complexRightHalfPlane : Set ℂ := {z : ℂ | 0 < z.re}

/-- The complex-rate domain is open, so pointwise differentiability on this
domain can be upgraded to analytic-on-neighborhood statements. -/
theorem complexRightHalfPlane_isOpen :
    IsOpen complexRightHalfPlane := by
  simpa [complexRightHalfPlane] using
    (isOpen_lt continuous_const Complex.continuous_re :
      IsOpen {z : ℂ | 0 < z.re})

/-- The complex-rate domain is preconnected. This is one of the geometric
hypotheses needed by Mathlib's analytic identity theorem. -/
theorem complexRightHalfPlane_isPreconnected :
    IsPreconnected complexRightHalfPlane := by
  simpa [complexRightHalfPlane] using
    (Convex.isPreconnected (convex_halfSpace_re_gt 0) :
      IsPreconnected {z : ℂ | 0 < z.re})

/-- A right-half-plane rate is nonzero. -/
theorem complexRightHalfPlane_ne_zero
    {z : ℂ} (hz : z ∈ complexRightHalfPlane) :
    z ≠ 0 := by
  intro h
  have hzpos : 0 < z.re := hz
  rw [h] at hzpos
  exact (lt_irrefl (0 : ℝ)) hzpos

/-- The reciprocal of a right-half-plane rate is still in the right half-plane.
This is the branch-control fact needed for the candidate value
`(1 / z)^alpha * Gamma alpha` on the same analytic-continuation domain. -/
theorem complexRightHalfPlane_inv_mem
    {z : ℂ} (hz : z ∈ complexRightHalfPlane) :
    z⁻¹ ∈ complexRightHalfPlane := by
  have hz_ne : z ≠ 0 := complexRightHalfPlane_ne_zero hz
  have hnorm : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz_ne
  change 0 < z⁻¹.re
  rw [Complex.inv_re]
  exact div_pos hz hnorm

/-- The characteristic-function complex rate belongs to the right half-plane. -/
theorem complex_rate_mem_rightHalfPlane
    {r t : ℝ} (hr : 0 < r) :
    (r : ℂ) - Complex.I * (t : ℂ) ∈ complexRightHalfPlane := by
  simpa [complexRightHalfPlane] using hr

/-- In shape `1`, the rate-form Gamma characteristic-function formula reduces
to the elementary exponential-law formula `r / (r - i t)`. -/
theorem gammaCharacteristicFunctionRateFormula_one
    {r t : ℝ} (hr : 0 < r) :
    gammaCharacteristicFunctionRateFormula 1 r t =
      (r : ℂ) / ((r : ℂ) - Complex.I * (t : ℂ)) := by
  unfold gammaCharacteristicFunctionRateFormula
  have hden : (r : ℂ) - Complex.I * (t : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hnum : (r : ℂ) ≠ 0 := by
    exact_mod_cast hr.ne'
  have hquot :
      (r : ℂ) / ((r : ℂ) - Complex.I * (t : ℂ)) ≠ 0 :=
    div_ne_zero hnum hden
  simpa using Complex.exp_log hquot

/-- The complex rate `r - i t` stays in the open right half-plane when
`0 < r`. This is the positivity hypothesis needed by complex Laplace
integral estimates. -/
theorem complex_rate_re_pos
    {r t : ℝ} (hr : 0 < r) :
    0 < ((r : ℂ) - Complex.I * (t : ℂ)).re := by
  simpa using hr

/-- A positive real part rules out the zero complex rate. -/
theorem complex_rate_ne_zero
    {r t : ℝ} (hr : 0 < r) :
    (r : ℂ) - Complex.I * (t : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  linarith

/-- The quotient appearing in the rate-form characteristic-function formula is
nonzero. This lets subsequent proofs rewrite the exponential-log expression as
a genuine complex power. -/
theorem complex_rate_quot_ne_zero
    {r t : ℝ} (hr : 0 < r) :
    (r : ℂ) / ((r : ℂ) - Complex.I * (t : ℂ)) ≠ 0 := by
  have hnum : (r : ℂ) ≠ 0 := by
    exact_mod_cast hr.ne'
  exact div_ne_zero hnum (complex_rate_ne_zero hr)

/-- The quotient `r / (r - i t)` also lies in the open right half-plane. This
is a branch-control fact for later complex-log and complex-power algebra. -/
theorem complex_rate_quot_re_pos
    {r t : ℝ} (hr : 0 < r) :
    0 < ((r : ℂ) / ((r : ℂ) - Complex.I * (t : ℂ))).re := by
  rw [Complex.div_re]
  simp
  have hnum : 0 < r * r := mul_pos hr hr
  have hden : 0 < Complex.normSq ((r : ℂ) - Complex.I * (t : ℂ)) := by
    exact Complex.normSq_pos.mpr (complex_rate_ne_zero hr)
  exact div_pos hnum hden

/-- The exponential-log formula is the usual complex-power expression on the
nonzero quotient `r / (r - i t)`. -/
theorem gammaCharacteristicFunctionRateFormula_eq_cpow
    {alpha r t : ℝ} (hr : 0 < r) :
    gammaCharacteristicFunctionRateFormula alpha r t =
      ((r : ℂ) / ((r : ℂ) - Complex.I * (t : ℂ))) ^ (alpha : ℂ) := by
  unfold gammaCharacteristicFunctionRateFormula
  rw [Complex.cpow_def_of_ne_zero (complex_rate_quot_ne_zero hr)]
  ring_nf

/-- The reciprocal of the complex rate is nonzero. This is the factor supplied
by a future unnormalized complex-rate Gamma/Laplace integral. -/
theorem complex_rate_inv_ne_zero
    {r t : ℝ} (hr : 0 < r) :
    (1 : ℂ) / ((r : ℂ) - Complex.I * (t : ℂ)) ≠ 0 := by
  exact div_ne_zero one_ne_zero (complex_rate_ne_zero hr)

/-- Multiplying the future unnormalized value `(1 / (r - i t))^alpha` by the
real normalizing factor `r^alpha` gives the characteristic-function quotient
power. The proof uses the principal-log branch only through multiplication by a
positive real scalar. -/
theorem complex_rate_cpow_mul_inv_eq_quot_cpow
    {alpha r t : ℝ} (hr : 0 < r) :
    (r : ℂ) ^ (alpha : ℂ) *
        ((1 : ℂ) / ((r : ℂ) - Complex.I * (t : ℂ))) ^ (alpha : ℂ) =
      ((r : ℂ) / ((r : ℂ) - Complex.I * (t : ℂ))) ^ (alpha : ℂ) := by
  let z : ℂ := (r : ℂ) - Complex.I * (t : ℂ)
  have hrC : (r : ℂ) ≠ 0 := by
    exact_mod_cast hr.ne'
  have hinv : (1 : ℂ) / z ≠ 0 := by
    dsimp [z]
    exact complex_rate_inv_ne_zero hr
  have hquot : (r : ℂ) / z ≠ 0 := by
    dsimp [z]
    exact complex_rate_quot_ne_zero hr
  rw [Complex.cpow_def_of_ne_zero hrC, Complex.cpow_def_of_ne_zero hinv,
    Complex.cpow_def_of_ne_zero hquot]
  rw [← Complex.exp_add]
  congr 1
  rw [show (r : ℂ) / z = (r : ℂ) * ((1 : ℂ) / z) by ring]
  rw [Complex.log_ofReal_mul hr hinv, ← Complex.ofReal_log hr.le]
  ring
