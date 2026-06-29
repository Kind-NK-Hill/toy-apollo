/-
TASK ID: prob_9_3_basic_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

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

noncomputable def gammaCharacteristicFunctionFormula
    (alpha beta t : ℝ) : ℂ :=
  Complex.exp ((alpha : ℂ) *
    Complex.log ((1 : ℂ) /
      ((1 : ℂ) - Complex.I * (beta : ℂ) * (t : ℂ))))

noncomputable def gammaCharacteristicFunctionRateFormula
    (alpha r t : ℝ) : ℂ :=
  Complex.exp ((alpha : ℂ) *
    Complex.log ((r : ℂ) / ((r : ℂ) - Complex.I * (t : ℂ))))

def complexRightHalfPlane : Set ℂ := {z : ℂ | 0 < z.re}

theorem complexRightHalfPlane_isOpen :
    IsOpen complexRightHalfPlane := by
  simpa [complexRightHalfPlane] using
    (isOpen_lt continuous_const Complex.continuous_re :
      IsOpen {z : ℂ | 0 < z.re})

theorem complexRightHalfPlane_isPreconnected :
    IsPreconnected complexRightHalfPlane := by
  simpa [complexRightHalfPlane] using
    (Convex.isPreconnected (convex_halfSpace_re_gt 0) :
      IsPreconnected {z : ℂ | 0 < z.re})

theorem complexRightHalfPlane_ne_zero
    {z : ℂ} (hz : z ∈ complexRightHalfPlane) :
    z ≠ 0 := by
  intro h
  have hzpos : 0 < z.re := hz
  rw [h] at hzpos
  exact (lt_irrefl (0 : ℝ)) hzpos

theorem complexRightHalfPlane_inv_mem
    {z : ℂ} (hz : z ∈ complexRightHalfPlane) :
    z⁻¹ ∈ complexRightHalfPlane := by
  have hz_ne : z ≠ 0 := complexRightHalfPlane_ne_zero hz
  have hnorm : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz_ne
  change 0 < z⁻¹.re
  rw [Complex.inv_re]
  exact div_pos hz hnorm

theorem complex_rate_mem_rightHalfPlane
    {r t : ℝ} (hr : 0 < r) :
    (r : ℂ) - Complex.I * (t : ℂ) ∈ complexRightHalfPlane := by
  simpa [complexRightHalfPlane] using hr

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

theorem complex_rate_re_pos
    {r t : ℝ} (hr : 0 < r) :
    0 < ((r : ℂ) - Complex.I * (t : ℂ)).re := by
  simpa using hr

theorem complex_rate_ne_zero
    {r t : ℝ} (hr : 0 < r) :
    (r : ℂ) - Complex.I * (t : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  linarith

theorem complex_rate_quot_ne_zero
    {r t : ℝ} (hr : 0 < r) :
    (r : ℂ) / ((r : ℂ) - Complex.I * (t : ℂ)) ≠ 0 := by
  have hnum : (r : ℂ) ≠ 0 := by
    exact_mod_cast hr.ne'
  exact div_ne_zero hnum (complex_rate_ne_zero hr)

theorem complex_rate_quot_re_pos
    {r t : ℝ} (hr : 0 < r) :
    0 < ((r : ℂ) / ((r : ℂ) - Complex.I * (t : ℂ))).re := by
  rw [Complex.div_re]
  simp
  have hnum : 0 < r * r := mul_pos hr hr
  have hden : 0 < Complex.normSq ((r : ℂ) - Complex.I * (t : ℂ)) := by
    exact Complex.normSq_pos.mpr (complex_rate_ne_zero hr)
  exact div_pos hnum hden

theorem gammaCharacteristicFunctionRateFormula_eq_cpow
    {alpha r t : ℝ} (hr : 0 < r) :
    gammaCharacteristicFunctionRateFormula alpha r t =
      ((r : ℂ) / ((r : ℂ) - Complex.I * (t : ℂ))) ^ (alpha : ℂ) := by
  unfold gammaCharacteristicFunctionRateFormula
  rw [Complex.cpow_def_of_ne_zero (complex_rate_quot_ne_zero hr)]
  ring_nf

theorem complex_rate_inv_ne_zero
    {r t : ℝ} (hr : 0 < r) :
    (1 : ℂ) / ((r : ℂ) - Complex.I * (t : ℂ)) ≠ 0 := by
  exact div_ne_zero one_ne_zero (complex_rate_ne_zero hr)

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
