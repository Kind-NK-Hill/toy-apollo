import Mathlib
import ToyApollo.Output.def_9_3

/-
TASK ID: ex_9_2_2
TYPE: Example_Proof
SOURCE PLAN: chapter9-characteristic-functions
TASK CONTENT:
\textbf{Example 9.2.2 (Characteristic Function of Uniform Random Variable)} \\
Suppose $X$ is a continuous random variable that is uniformly distributed on the interval $[-a,a]$, where $a$ is a positive constant. The characteristic function of $X$ is
\[
\phi_X(t)=\frac{1}{2a}\int_{-a}^{a} e^{ixt}\,dx
=\frac{1}{2a}\frac{e^{iat}-e^{-iat}}{it}
=\frac{\sin(at)}{at},
\]
for $t\neq 0$. When $t=0$, $\phi_X(0)$ is equal to $1$.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped Interval

noncomputable abbrev symmetricUniformDensity (a : ℝ) (x : ℝ) : ℝ :=
  if x ∈ Set.Icc (-a) a then (2 * a)⁻¹ else 0

noncomputable abbrev symmetricUniformCharacteristicSource (a t : ℝ) : ℂ :=
  (1 / (2 * (a : ℂ))) *
    ∫ x in -a..a, Complex.exp (Complex.I * ((x * t : ℝ) : ℂ))

noncomputable abbrev symmetricUniformCharacteristicFormula (a t : ℝ) : ℂ :=
  if t = 0 then 1 else (Real.sin (a * t) / (a * t) : ℝ)

theorem symmetricUniformCharacteristicSource_eq_sinc
    {a t : ℝ} (ha : a ≠ 0) (ht : t ≠ 0) :
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

theorem symmetricUniformCharacteristicSource_zero {a : ℝ} (ha : a ≠ 0) :
    symmetricUniformCharacteristicSource a 0 = 1 := by
  unfold symmetricUniformCharacteristicSource
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  simp [div_eq_mul_inv, haC]
  change ((a + a : ℝ) : ℂ) * ((a : ℂ)⁻¹ * 2⁻¹) = 1
  field_simp [haC, Complex.ofReal_mul]
  ring_nf
  norm_num [Complex.ofReal_mul]

theorem ex_9_2_2_nonzero {a t : ℝ} (ha : a ≠ 0) (ht : t ≠ 0) :
    symmetricUniformCharacteristicSource a t =
      symmetricUniformCharacteristicFormula a t := by
  simp [symmetricUniformCharacteristicFormula, ht,
    symmetricUniformCharacteristicSource_eq_sinc (a := a) (t := t) ha ht]

theorem ex_9_2_2_zero {a : ℝ} (ha : a ≠ 0) :
    symmetricUniformCharacteristicSource a 0 =
      symmetricUniformCharacteristicFormula a 0 := by
  simp [symmetricUniformCharacteristicFormula, symmetricUniformCharacteristicSource_zero (a := a) ha]

theorem ex_9_2_2 {a t : ℝ} (ha : a ≠ 0) :
    symmetricUniformCharacteristicSource a t =
      symmetricUniformCharacteristicFormula a t := by
  by_cases ht : t = 0
  · subst t
    exact ex_9_2_2_zero (a := a) ha
  · exact ex_9_2_2_nonzero (a := a) (t := t) ha ht
