/-
TASK ID: ex_9_2_2
TYPE: Example_Proof
SOURCE PLAN: chapter9-characteristic-functions
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_09.def_9_3




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped ENNReal Interval

noncomputable section

 
def symmetricUniformDensity (a : ℝ) (x : ℝ) : ℝ :=
  if x ∈ Set.Icc (-a) a then (2 * a)⁻¹ else 0

 
def symmetricUniformLaw (a : ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (symmetricUniformDensity a x)

 
def symmetricUniformCharacteristicSource (a t : ℝ) : ℂ :=
  (1 / (2 * (a : ℂ))) *
    ∫ x in -a..a, Complex.exp (Complex.I * ((x * t : ℝ) : ℂ))

 
def symmetricUniformCharacteristicFormula (a t : ℝ) : ℂ :=
  if t = 0 then 1 else (Real.sin (a * t) / (a * t) : ℝ)

 
theorem symmetricUniformDensity_measurable (a : ℝ) :
    Measurable (symmetricUniformDensity a) := by
  unfold symmetricUniformDensity
  exact Measurable.ite measurableSet_Icc measurable_const measurable_const

 
theorem symmetricUniformDensity_nonneg {a : ℝ} (ha : 0 < a) :
    ∀ x, 0 ≤ symmetricUniformDensity a x := by
  intro x
  unfold symmetricUniformDensity
  split_ifs <;> positivity



theorem symmetricUniformLaw_eq_normalized_restrict {a : ℝ} (ha : 0 < a) :
    symmetricUniformLaw a =
      (ENNReal.ofReal (2 * a))⁻¹ • volume.restrict (Set.Icc (-a) a) := by
  have h2a : 0 < 2 * a := by positivity
  have hdensity :
      (fun x : ℝ => ENNReal.ofReal (symmetricUniformDensity a x)) =
        (Set.Icc (-a) a).indicator
          (fun _ : ℝ => ENNReal.ofReal ((2 * a)⁻¹)) := by
    funext x
    by_cases hx : x ∈ Set.Icc (-a) a <;>
      simp [symmetricUniformDensity, Set.indicator, hx]
  unfold symmetricUniformLaw
  rw [hdensity, withDensity_indicator measurableSet_Icc, withDensity_const,
    ENNReal.ofReal_inv_of_pos h2a]

 
theorem symmetricUniformLaw_isProbabilityMeasure {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (symmetricUniformLaw a) := by
  refine ⟨?_⟩
  rw [symmetricUniformLaw_eq_normalized_restrict ha, Measure.smul_apply,
    Measure.restrict_apply_univ, Real.volume_Icc, smul_eq_mul]
  have hlength : a - -a = 2 * a := by ring
  rw [hlength]
  exact ENNReal.inv_mul_cancel
    (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top

theorem symmetricUniformCharacteristicSource_eq_sinc
    {a t : ℝ} (_ha : 0 < a) (ht : t ≠ 0) :
    symmetricUniformCharacteristicSource a t =
      (Real.sin (a * t) / (a * t) : ℝ) := by
  unfold symmetricUniformCharacteristicSource
  have hsubst :
      (∫ x in -a..a, Complex.exp (Complex.I * ((x * t : ℝ) : ℂ))) =
        t⁻¹ • ∫ x in -a * t..a * t,
          Complex.exp (Complex.I * (x : ℂ)) := by
    exact
      (intervalIntegral.integral_comp_mul_right
        (f := fun y : ℝ => Complex.exp (Complex.I * (y : ℂ)))
        (a := -a) (b := a) (c := t) ht)
  have hint :
      (∫ x in -a * t..a * t, Complex.exp (Complex.I * (x : ℂ))) =
        2 * Real.sin (a * t) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      integral_exp_mul_I_eq_sin (a * t)
  rw [hsubst, hint]
  rw [Complex.real_smul]
  simp [div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv]
  ring_nf

theorem symmetricUniformCharacteristicSource_zero {a : ℝ} (ha : 0 < a) :
    symmetricUniformCharacteristicSource a 0 = 1 := by
  unfold symmetricUniformCharacteristicSource
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  simp [div_eq_mul_inv]
  field_simp [haC] <;> ring



theorem symmetricUniformCharacteristicIntegral_eq_source
    {a t : ℝ} (ha : 0 < a) :
    (∫ x : ℝ,
        Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) *
          (symmetricUniformDensity a x : ℂ)) =
      symmetricUniformCharacteristicSource a t := by
  have hle : -a ≤ a := by linarith
  have hintegrand :
      (fun x : ℝ =>
        Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) *
          (symmetricUniformDensity a x : ℂ)) =
        (Set.Icc (-a) a).indicator (fun x : ℝ =>
          Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) *
            (((2 * a)⁻¹ : ℝ) : ℂ)) := by
    funext x
    by_cases hx : x ∈ Set.Icc (-a) a <;>
      simp [symmetricUniformDensity, Set.indicator, hx]
  rw [hintegrand, integral_indicator measurableSet_Icc, integral_mul_const]
  unfold symmetricUniformCharacteristicSource
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  have hcoef : ((((2 * a)⁻¹ : ℝ) : ℂ)) = 1 / (2 * (a : ℂ)) := by
    simp [Complex.ofReal_inv, Complex.ofReal_mul, one_div]
  rw [hcoef, mul_comm]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _hx
  simp [Complex.ofReal_mul, mul_assoc]



theorem symmetricUniformCharacteristicFunction_eq_source
    {a : ℝ} (ha : 0 < a) (t : ℝ) :
    characteristicFunction (symmetricUniformLaw a) t =
      symmetricUniformCharacteristicSource a t := by
  letI : IsProbabilityMeasure (symmetricUniformLaw a) :=
    symmetricUniformLaw_isProbabilityMeasure ha
  rw [characteristicFunction_eq_integral_of_pdf
    (symmetricUniformLaw a) (symmetricUniformDensity a)
    (symmetricUniformDensity_measurable a)
    (symmetricUniformDensity_nonneg ha) rfl t]
  exact symmetricUniformCharacteristicIntegral_eq_source ha

theorem ex_9_2_2_nonzero {a t : ℝ} (ha : 0 < a) (ht : t ≠ 0) :
    characteristicFunction (symmetricUniformLaw a) t =
      symmetricUniformCharacteristicFormula a t := by
  rw [symmetricUniformCharacteristicFunction_eq_source ha]
  simp [symmetricUniformCharacteristicFormula, ht,
    symmetricUniformCharacteristicSource_eq_sinc (a := a) (t := t) ha ht]

theorem ex_9_2_2_zero {a : ℝ} (ha : 0 < a) :
    characteristicFunction (symmetricUniformLaw a) 0 =
      symmetricUniformCharacteristicFormula a 0 := by
  rw [symmetricUniformCharacteristicFunction_eq_source ha]
  simp [symmetricUniformCharacteristicFormula,
    symmetricUniformCharacteristicSource_zero (a := a) ha]

theorem ex_9_2_2 {a t : ℝ} (ha : 0 < a) :
    characteristicFunction (symmetricUniformLaw a) t =
      symmetricUniformCharacteristicFormula a t := by
  by_cases ht : t = 0
  · subst t
    exact ex_9_2_2_zero (a := a) ha
  · exact ex_9_2_2_nonzero (a := a) (t := t) ha ht
