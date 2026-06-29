import ToyApollo.Output.prob_9_3_kernel_support

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

noncomputable section

/-- The arbitrary-shape complex-rate Gamma kernel is integrable on `(0, ∞)`.
This proves the analytic side condition needed before evaluating the remaining
complex-rate Gamma integral. -/
theorem complex_rate_gamma_kernel_integrableOn
    {alpha r : ℝ} (halpha : 0 < alpha) (hr : 0 < r) (t : ℝ) :
    IntegrableOn (fun x : ℝ =>
      ((x ^ (alpha - 1) : ℝ) : ℂ) *
        Complex.exp (-(((r : ℂ) - Complex.I * (t : ℂ)) * (x : ℂ))))
      (Set.Ioi (0 : ℝ)) := by
  exact rightHalfPlane_gamma_kernel_integrableOn halpha
    (complex_rate_mem_rightHalfPlane hr)

/-- The normalized complex-rate Gamma density integrand from the remaining
analytic theorem is integrable on `(0, ∞)`. -/
theorem complex_rate_gammaPDF_integrand_integrableOn
    {alpha r : ℝ} (halpha : 0 < alpha) (hr : 0 < r) (t : ℝ) :
    IntegrableOn
      (fun x : ℝ =>
        (((r ^ alpha : ℝ) : ℂ) / (Real.Gamma alpha : ℂ)) *
          ((x ^ (alpha - 1) : ℝ) : ℂ) *
          Complex.exp (-(((r : ℂ) - Complex.I * (t : ℂ)) * (x : ℂ))))
      (Set.Ioi (0 : ℝ)) := by
  have hkernel := complex_rate_gamma_kernel_integrableOn halpha hr t
  simpa [mul_assoc] using
    hkernel.const_mul (((r ^ alpha : ℝ) : ℂ) / (Real.Gamma alpha : ℂ))

/-- Mathlib's complex exponential integral proves the complex-rate Gamma
integral in the shape-one case. The general blocker is the corresponding
complex-rate integral with the extra `x^(alpha - 1)` Gamma factor. -/
theorem integral_exp_neg_complex_rate_Ioi
    {r t : ℝ} (hr : 0 < r) :
    ∫ x in Set.Ioi (0 : ℝ),
        Complex.exp
          (-(((r : ℂ) - Complex.I * (t : ℂ)) * (x : ℂ))) =
      (1 : ℂ) / ((r : ℂ) - Complex.I * (t : ℂ)) := by
  let z : ℂ := (r : ℂ) - Complex.I * (t : ℂ)
  have hz_re : 0 < z.re := by
    dsimp [z]
    simp [hr]
  have hneg_re : (-z).re < 0 := by
    simp [hz_re]
  have h :=
    integral_exp_mul_complex_Ioi (c := (0 : ℝ)) (a := -z) hneg_re
  calc
    ∫ x in Set.Ioi (0 : ℝ),
        Complex.exp
          (-(((r : ℂ) - Complex.I * (t : ℂ)) * (x : ℂ))) =
        ∫ x in Set.Ioi (0 : ℝ), Complex.exp ((-z) * (x : ℂ)) := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro x hx
          apply congrArg Complex.exp
          dsimp [z]
          ring_nf
    _ = -Complex.exp ((-z) * (0 : ℂ)) / (-z) := h
    _ = (1 : ℂ) / z := by
          simp

/-- A sharper reduction target for the remaining analytic gap: after expanding
`gammaPDFReal` and deleting the null boundary/outside-support part, it is
enough to prove the normalized complex-rate Gamma integral on `(0, ∞)`. -/
theorem gammaPDFReal_fourier_integral_of_complex_rate_gammaPDF_integral
    (hcomplex : ∀ {alpha r : ℝ}, 0 < alpha -> 0 < r -> ∀ t : ℝ,
      ∫ x in Set.Ioi (0 : ℝ),
          (((r ^ alpha : ℝ) : ℂ) / (Real.Gamma alpha : ℂ) *
            ((x ^ (alpha - 1) : ℝ) : ℂ) *
            Complex.exp
              (-(((r : ℂ) - Complex.I * (t : ℂ)) * (x : ℂ)))) =
        gammaCharacteristicFunctionRateFormula alpha r t) :
    ∀ {alpha r : ℝ}, 0 < alpha -> 0 < r -> ∀ t : ℝ,
      ∫ x : ℝ,
          Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
            (ProbabilityTheory.gammaPDFReal alpha r x : ℂ) =
        gammaCharacteristicFunctionRateFormula alpha r t := by
  intro alpha r halpha hr t
  let f : ℝ → ℂ := fun x =>
    Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
      (ProbabilityTheory.gammaPDFReal alpha r x : ℂ)
  calc
    ∫ x : ℝ,
        Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
          (ProbabilityTheory.gammaPDFReal alpha r x : ℂ) =
        ∫ x in Set.Ici (0 : ℝ), f x := by
          rw [← MeasureTheory.integral_indicator measurableSet_Ici]
          refine integral_congr_ae (ae_of_all _ ?_)
          intro x
          by_cases hx : 0 ≤ x
          · simp [f, Set.indicator, hx]
          · simp [f, Set.indicator, ProbabilityTheory.gammaPDFReal, hx]
    _ = ∫ x in Set.Ioi (0 : ℝ), f x := by
          rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    _ = ∫ x in Set.Ioi (0 : ℝ),
          (((r ^ alpha : ℝ) : ℂ) / (Real.Gamma alpha : ℂ) *
            ((x ^ (alpha - 1) : ℝ) : ℂ) *
            Complex.exp
              (-(((r : ℂ) - Complex.I * (t : ℂ)) * (x : ℂ)))) := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro x hx
          have hx_nonneg : 0 ≤ x := le_of_lt hx
          dsimp [f]
          simp [ProbabilityTheory.gammaPDFReal, hx_nonneg, Complex.ofReal_exp]
          calc
            Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
                (((r ^ alpha : ℝ) : ℂ) / (Real.Gamma alpha : ℂ) *
                  ((x ^ (alpha - 1) : ℝ) : ℂ) *
                  Complex.exp (-((r : ℂ) * (x : ℂ)))) =
                ((r ^ alpha : ℝ) : ℂ) / (Real.Gamma alpha : ℂ) *
                  ((x ^ (alpha - 1) : ℝ) : ℂ) *
                  (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
                    Complex.exp (-((r : ℂ) * (x : ℂ)))) := by
                  ring
            _ = ((r ^ alpha : ℝ) : ℂ) / (Real.Gamma alpha : ℂ) *
                  ((x ^ (alpha - 1) : ℝ) : ℂ) *
                  Complex.exp
                    ((t : ℂ) * (x : ℂ) * Complex.I + (-((r : ℂ) * (x : ℂ)))) := by
                  rw [Complex.exp_add]
            _ = ((r ^ alpha : ℝ) : ℂ) / (Real.Gamma alpha : ℂ) *
                  ((x ^ (alpha - 1) : ℝ) : ℂ) *
                  Complex.exp (-(((r : ℂ) - Complex.I * (t : ℂ)) * (x : ℂ))) := by
                  congr 1
                  ring_nf
    _ = gammaCharacteristicFunctionRateFormula alpha r t := hcomplex halpha hr t

/-- The normalized complex-rate Gamma density integral follows from the
right-half-plane Gamma kernel value identity. -/
theorem gammaPDFReal_complex_rate_gammaPDF_integral
    {alpha r : ℝ} (halpha : 0 < alpha) (hr : 0 < r) (t : ℝ) :
    ∫ x in Set.Ioi (0 : ℝ),
        (((r ^ alpha : ℝ) : ℂ) / (Real.Gamma alpha : ℂ) *
          ((x ^ (alpha - 1) : ℝ) : ℂ) *
          Complex.exp
            (-(((r : ℂ) - Complex.I * (t : ℂ)) * (x : ℂ)))) =
      gammaCharacteristicFunctionRateFormula alpha r t :=
  gammaPDFReal_complex_rate_gammaPDF_integral_of_kernel_integral
    halpha hr t
    (complex_gamma_kernel_integral_complex_rate halpha hr t)

/-- Fourier integral of Mathlib's real rate-`r` Gamma density. -/
theorem gammaPDFReal_fourier_integral
    {alpha r : ℝ} (halpha : 0 < alpha) (hr : 0 < r) (t : ℝ) :
    ∫ x : ℝ,
        Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
          (ProbabilityTheory.gammaPDFReal alpha r x : ℂ) =
      gammaCharacteristicFunctionRateFormula alpha r t :=
  gammaPDFReal_fourier_integral_of_complex_rate_gammaPDF_integral
    (fun halpha hr t =>
      gammaPDFReal_complex_rate_gammaPDF_integral halpha hr t)
    halpha hr t

/-- The zero-frequency case of the Gamma density Fourier integral is available
from Mathlib's normalization of `gammaPDF`. -/
theorem gammaCharacteristicFunctionRateFormula_zero
    {alpha r : ℝ} (hr : 0 < r) :
    gammaCharacteristicFunctionRateFormula alpha r 0 = 1 := by
  unfold gammaCharacteristicFunctionRateFormula
  simp [hr.ne']

theorem integral_gammaPDFReal_eq_one
    {alpha r : ℝ} (halpha : 0 < alpha) (hr : 0 < r) :
    ∫ x : ℝ, ProbabilityTheory.gammaPDFReal alpha r x = 1 := by
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (fun x => ProbabilityTheory.gammaPDFReal_nonneg halpha hr x))
    (ProbabilityTheory.measurable_gammaPDFReal alpha r).aestronglyMeasurable]
  change (∫⁻ x : ℝ, ProbabilityTheory.gammaPDF alpha r x).toReal = 1
  rw [ProbabilityTheory.lintegral_gammaPDF_eq_one halpha hr]
  norm_num

/-- The remaining half-line complex-rate Gamma integral is already settled at
zero frequency. This is the same expanded positive-half-line target as the
general blocker, specialized to `t = 0`. -/
theorem gammaPDFReal_complex_rate_gammaPDF_integral_zero
    {alpha r : ℝ} (halpha : 0 < alpha) (hr : 0 < r) :
    ∫ x in Set.Ioi (0 : ℝ),
        (((r ^ alpha : ℝ) : ℂ) / (Real.Gamma alpha : ℂ) *
          ((x ^ (alpha - 1) : ℝ) : ℂ) *
          Complex.exp
            (-(((r : ℂ) - Complex.I * (0 : ℂ)) * (x : ℂ)))) =
      gammaCharacteristicFunctionRateFormula alpha r 0 := by
  rw [gammaCharacteristicFunctionRateFormula_zero hr]
  let f : ℝ → ℂ := fun x =>
    (ProbabilityTheory.gammaPDFReal alpha r x : ℂ)
  calc
    ∫ x in Set.Ioi (0 : ℝ),
        (((r ^ alpha : ℝ) : ℂ) / (Real.Gamma alpha : ℂ) *
          ((x ^ (alpha - 1) : ℝ) : ℂ) *
          Complex.exp
            (-(((r : ℂ) - Complex.I * (0 : ℂ)) * (x : ℂ)))) =
        ∫ x in Set.Ioi (0 : ℝ), f x := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro x hx
          have hx_nonneg : 0 ≤ x := le_of_lt hx
          dsimp [f]
          simp [ProbabilityTheory.gammaPDFReal, hx_nonneg, Complex.ofReal_exp]
    _ = ∫ x in Set.Ici (0 : ℝ), f x := by
          rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    _ = ∫ x : ℝ, f x := by
          symm
          rw [← MeasureTheory.integral_indicator measurableSet_Ici]
          refine integral_congr_ae (ae_of_all _ ?_)
          intro x
          by_cases hx : 0 ≤ x
          · simp [f, Set.indicator, hx]
          · simp [f, Set.indicator, ProbabilityTheory.gammaPDFReal, hx]
    _ = Complex.ofReal
          (∫ x : ℝ, ProbabilityTheory.gammaPDFReal alpha r x) := by
          exact (integral_ofReal (𝕜 := ℂ)
            (f := fun x : ℝ => ProbabilityTheory.gammaPDFReal alpha r x))
    _ = 1 := by
          rw [integral_gammaPDFReal_eq_one halpha hr]
          norm_num

theorem gammaPDFReal_fourier_integral_zero
    {alpha r : ℝ} (halpha : 0 < alpha) (hr : 0 < r) :
    ∫ x : ℝ,
        Complex.exp ((0 : ℂ) * (x : ℂ) * Complex.I) *
          (ProbabilityTheory.gammaPDFReal alpha r x : ℂ) =
      gammaCharacteristicFunctionRateFormula alpha r 0 := by
  rw [gammaCharacteristicFunctionRateFormula_zero hr]
  calc
    ∫ x : ℝ,
        Complex.exp ((0 : ℂ) * (x : ℂ) * Complex.I) *
          (ProbabilityTheory.gammaPDFReal alpha r x : ℂ) =
        ∫ x : ℝ, (ProbabilityTheory.gammaPDFReal alpha r x : ℂ) := by
          simp
    _ = Complex.ofReal (∫ x : ℝ, ProbabilityTheory.gammaPDFReal alpha r x) := by
          exact (integral_ofReal (𝕜 := ℂ)
            (f := fun x : ℝ => ProbabilityTheory.gammaPDFReal alpha r x))
    _ = 1 := by
          rw [integral_gammaPDFReal_eq_one halpha hr]
          norm_num

/-- Shape one is the exponential-distribution case. Mathlib's
`integral_exp_mul_complex_Ioi` closes the full Fourier integral here; the
remaining blocker is genuinely the arbitrary-shape complex-rate Gamma
integral. -/
theorem gammaPDFReal_fourier_integral_one
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    ∫ x : ℝ,
        Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
          (ProbabilityTheory.gammaPDFReal 1 r x : ℂ) =
      gammaCharacteristicFunctionRateFormula 1 r t := by
  rw [gammaCharacteristicFunctionRateFormula_one hr]
  let f : ℝ → ℂ := fun x =>
    Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
      (ProbabilityTheory.gammaPDFReal 1 r x : ℂ)
  calc
    ∫ x : ℝ,
        Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
          (ProbabilityTheory.gammaPDFReal 1 r x : ℂ) =
        ∫ x in Set.Ici (0 : ℝ), f x := by
          rw [← MeasureTheory.integral_indicator measurableSet_Ici]
          refine integral_congr_ae (ae_of_all _ ?_)
          intro x
          by_cases hx : 0 ≤ x
          · simp [f, Set.indicator, hx]
          · simp [f, Set.indicator, ProbabilityTheory.gammaPDFReal, hx]
    _ = ∫ x in Set.Ioi (0 : ℝ), f x := by
          rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    _ = ∫ x in Set.Ioi (0 : ℝ),
          (r : ℂ) *
            Complex.exp
              (-(((r : ℂ) - Complex.I * (t : ℂ)) * (x : ℂ))) := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro x hx
          have hx_nonneg : 0 ≤ x := le_of_lt hx
          dsimp [f]
          simp [ProbabilityTheory.gammaPDFReal, hx_nonneg, Real.Gamma_one, Complex.ofReal_exp]
          calc
            Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
                ((r : ℂ) * Complex.exp (-((r : ℂ) * (x : ℂ)))) =
                (r : ℂ) * (Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
                  Complex.exp (-((r : ℂ) * (x : ℂ)))) := by
                  ring
            _ = (r : ℂ) *
                  Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I +
                    (-((r : ℂ) * (x : ℂ)))) := by
                  rw [Complex.exp_add]
            _ = (r : ℂ) *
                  Complex.exp (-(((r : ℂ) - Complex.I * (t : ℂ)) * (x : ℂ))) := by
                  congr 1
                  ring_nf
    _ = (r : ℂ) *
          ∫ x in Set.Ioi (0 : ℝ),
            Complex.exp
              (-(((r : ℂ) - Complex.I * (t : ℂ)) * (x : ℂ))) := by
          simpa using
            (MeasureTheory.integral_const_mul
              (μ := volume.restrict (Set.Ioi (0 : ℝ)))
              (r := (r : ℂ))
              (fun x : ℝ =>
                Complex.exp
                  (-(((r : ℂ) - Complex.I * (t : ℂ)) * (x : ℂ)))))
    _ = (r : ℂ) * ((1 : ℂ) / ((r : ℂ) - Complex.I * (t : ℂ))) := by
          rw [integral_exp_neg_complex_rate_Ioi hr]
    _ = (r : ℂ) / ((r : ℂ) - Complex.I * (t : ℂ)) := by
          ring

/-- The measure-theoretic part of `gammaMeasure_charFun_rate` reduces to the
Fourier integral of Mathlib's real Gamma density. This avoids bundling the
`withDensity` expansion into the remaining analytic blocker. -/
theorem gammaMeasure_charFun_rate_of_gammaPDFReal_fourier_integral
    (hpdf : ∀ {alpha r : ℝ}, 0 < alpha -> 0 < r -> ∀ t : ℝ,
      ∫ x : ℝ,
          Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
            (ProbabilityTheory.gammaPDFReal alpha r x : ℂ) =
        gammaCharacteristicFunctionRateFormula alpha r t) :
    ∀ {alpha r : ℝ}, 0 < alpha -> 0 < r -> ∀ t : ℝ,
      charFun (gammaMeasure alpha r) t =
        gammaCharacteristicFunctionRateFormula alpha r t := by
  intro alpha r halpha hr t
  rw [MeasureTheory.charFun_apply_real, ProbabilityTheory.gammaMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul]
  · trans ∫ x : ℝ,
        Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
          (ProbabilityTheory.gammaPDFReal alpha r x : ℂ)
    · refine integral_congr_ae ?_
      refine ae_of_all _ ?_
      intro x
      have hnonneg := ProbabilityTheory.gammaPDFReal_nonneg halpha hr x
      simp [ProbabilityTheory.gammaPDF, ENNReal.toReal_ofReal hnonneg]
      change (ProbabilityTheory.gammaPDFReal alpha r x : ℂ) *
          Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) =
        Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
          (ProbabilityTheory.gammaPDFReal alpha r x : ℂ)
      ring
    · exact hpdf halpha hr t
  · exact (ProbabilityTheory.measurable_gammaPDFReal alpha r).ennreal_ofReal
  · exact ae_of_all _ (fun x => by simp [ProbabilityTheory.gammaPDF])

/-- Characteristic function of Mathlib's rate-`r` Gamma measure. -/
theorem gammaMeasure_charFun_rate
    {alpha r : ℝ} (halpha : 0 < alpha) (hr : 0 < r) (t : ℝ) :
    charFun (gammaMeasure alpha r) t =
      gammaCharacteristicFunctionRateFormula alpha r t :=
  gammaMeasure_charFun_rate_of_gammaPDFReal_fourier_integral
    (fun halpha hr t => gammaPDFReal_fourier_integral halpha hr t)
    halpha hr t

/-- The rate-form Gamma characteristic-function formula specializes to the
source scale-`beta` formula when Mathlib's rate is `beta^-1`. This discharges
only the scale/rate algebra; the Gamma-measure characteristic-function theorem
is still a separate analytic obligation. -/
theorem gammaCharacteristicFunctionRateFormula_inv_eq_scale
    {alpha beta t : ℝ} (hbeta : beta ≠ 0) :
    gammaCharacteristicFunctionRateFormula alpha beta⁻¹ t =
      gammaCharacteristicFunctionFormula alpha beta t := by
  unfold gammaCharacteristicFunctionRateFormula gammaCharacteristicFunctionFormula
  congr 1
  congr 1
  have hbetaC : (beta : ℂ) ≠ 0 := by
    exact_mod_cast hbeta
  have hbetaInv : beta⁻¹ ≠ 0 := inv_ne_zero hbeta
  have hrateC : (beta⁻¹ : ℂ) ≠ 0 := by
    exact_mod_cast hbetaInv
  have hdenRate :
      (beta⁻¹ : ℂ) - Complex.I * (t : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    exact hbeta hre
  have hdenScale :
      (1 : ℂ) - Complex.I * (t : ℂ) * (beta : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  apply congrArg Complex.log
  field_simp [hbetaC, hrateC, hdenRate, hdenScale]
  have hmul : ((1 / beta : ℝ) : ℂ) * (beta : ℂ) = 1 := by
    exact_mod_cast (div_mul_cancel₀ (1 : ℝ) hbeta)
  calc
    ((1 / beta : ℝ) : ℂ) *
          ((1 : ℂ) - Complex.I * (t : ℂ) * (beta : ℂ))
        = ((1 / beta : ℝ) : ℂ) - (((1 / beta : ℝ) : ℂ) * (beta : ℂ)) *
            (Complex.I * (t : ℂ)) := by ring
    _ = ((1 / beta : ℝ) : ℂ) - Complex.I * (t : ℂ) := by
      rw [hmul]
      ring
