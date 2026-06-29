import ToyApollo.Output.prob_9_3_basic_support

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

noncomputable section

/-- A future unnormalized right-half-plane Gamma integral value immediately
gives the normalized expanded Gamma-density integral needed for the
characteristic-function calculation. This isolates the remaining analytic
blocker to the single unnormalized complex-rate Laplace integral. -/
theorem gammaPDFReal_complex_rate_gammaPDF_integral_of_kernel_integral
    {alpha r : ℝ} (halpha : 0 < alpha) (hr : 0 < r) (t : ℝ)
    (hkernel :
      ∫ x in Set.Ioi (0 : ℝ),
          ((x ^ (alpha - 1) : ℝ) : ℂ) *
            Complex.exp
              (-(((r : ℂ) - Complex.I * (t : ℂ)) * (x : ℂ))) =
        ((1 : ℂ) / ((r : ℂ) - Complex.I * (t : ℂ))) ^ (alpha : ℂ) *
          (Real.Gamma alpha : ℂ)) :
    ∫ x in Set.Ioi (0 : ℝ),
        (((r ^ alpha : ℝ) : ℂ) / (Real.Gamma alpha : ℂ) *
          ((x ^ (alpha - 1) : ℝ) : ℂ) *
          Complex.exp
            (-(((r : ℂ) - Complex.I * (t : ℂ)) * (x : ℂ)))) =
      gammaCharacteristicFunctionRateFormula alpha r t := by
  rw [gammaCharacteristicFunctionRateFormula_eq_cpow hr]
  have hgamma : (Real.Gamma alpha : ℂ) ≠ 0 := by
    exact_mod_cast (Real.Gamma_pos_of_pos halpha).ne'
  have hconst :
      ((r ^ alpha : ℝ) : ℂ) / (Real.Gamma alpha : ℂ) =
        (r : ℂ) ^ (alpha : ℂ) / (Real.Gamma alpha : ℂ) := by
    rw [Complex.ofReal_cpow hr.le]
  calc
    ∫ x in Set.Ioi (0 : ℝ),
        (((r ^ alpha : ℝ) : ℂ) / (Real.Gamma alpha : ℂ) *
          ((x ^ (alpha - 1) : ℝ) : ℂ) *
          Complex.exp
            (-(((r : ℂ) - Complex.I * (t : ℂ)) * (x : ℂ)))) =
        (((r ^ alpha : ℝ) : ℂ) / (Real.Gamma alpha : ℂ)) *
          ∫ x in Set.Ioi (0 : ℝ),
            ((x ^ (alpha - 1) : ℝ) : ℂ) *
              Complex.exp
                (-(((r : ℂ) - Complex.I * (t : ℂ)) * (x : ℂ))) := by
          simpa [mul_assoc] using
            (MeasureTheory.integral_const_mul
              (μ := volume.restrict (Set.Ioi (0 : ℝ)))
              (r := (((r ^ alpha : ℝ) : ℂ) / (Real.Gamma alpha : ℂ)))
              (fun x : ℝ =>
                ((x ^ (alpha - 1) : ℝ) : ℂ) *
                  Complex.exp
                    (-(((r : ℂ) - Complex.I * (t : ℂ)) * (x : ℂ)))))
    _ = (((r ^ alpha : ℝ) : ℂ) / (Real.Gamma alpha : ℂ)) *
          (((1 : ℂ) / ((r : ℂ) - Complex.I * (t : ℂ))) ^ (alpha : ℂ) *
            (Real.Gamma alpha : ℂ)) := by
          rw [hkernel]
    _ = (r : ℂ) ^ (alpha : ℂ) *
          ((1 : ℂ) / ((r : ℂ) - Complex.I * (t : ℂ))) ^ (alpha : ℂ) := by
          rw [hconst]
          field_simp [hgamma]
    _ = ((r : ℂ) / ((r : ℂ) - Complex.I * (t : ℂ))) ^ (alpha : ℂ) := by
          exact complex_rate_cpow_mul_inv_eq_quot_cpow hr

/-- Mathlib's complex-shape Gamma integral, specialized to the exact
real-rate kernel shape used by this prompt pack. This is the strongest direct
reuse of `Complex.integral_cpow_mul_exp_neg_mul_Ioi` available before the rate
is allowed to become genuinely complex. -/
theorem complex_gamma_kernel_integral_real_rate
    {alpha r : ℝ} (halpha : 0 < alpha) (hr : 0 < r) :
    ∫ x in Set.Ioi (0 : ℝ),
        ((x ^ (alpha - 1) : ℝ) : ℂ) *
          Complex.exp (-((r : ℂ) * (x : ℂ))) =
      ((1 : ℂ) / (r : ℂ)) ^ (alpha : ℂ) *
        (Real.Gamma alpha : ℂ) := by
  have h :=
    Complex.integral_cpow_mul_exp_neg_mul_Ioi
      (a := (alpha : ℂ)) (r := r)
      (by simpa using halpha) hr
  calc
    ∫ x in Set.Ioi (0 : ℝ),
        ((x ^ (alpha - 1) : ℝ) : ℂ) *
          Complex.exp (-((r : ℂ) * (x : ℂ))) =
        ∫ x in Set.Ioi (0 : ℝ),
          (x : ℂ) ^ ((alpha : ℂ) - 1) *
            Complex.exp (-(r * x : ℝ)) := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro x hx
          dsimp
          rw [Complex.ofReal_cpow (le_of_lt hx)]
          norm_num [Complex.ofReal_sub, Complex.ofReal_exp,
            Complex.ofReal_mul]
    _ = ((1 : ℂ) / (r : ℂ)) ^ (alpha : ℂ) *
        (Real.Gamma alpha : ℂ) := by
          simpa [Complex.Gamma_ofReal] using h

/-- On the real integration line, the modulus of the complex-rate exponential
kernel is exactly the real-rate exponential kernel with rate `r`. -/
theorem norm_exp_neg_complex_rate_mul_ofReal
    (r t x : ℝ) :
    ‖Complex.exp (-(((r : ℂ) - Complex.I * (t : ℂ)) * (x : ℂ)))‖ =
      Real.exp (-(r * x)) := by
  rw [Complex.norm_exp]
  simp

/-- If the real part of a complex rate is bounded below by `c`, then the
modulus of the Gamma kernel is dominated by the real-rate kernel with rate
`c`. This is the local dominated-bound estimate needed for a right-half-plane
parameter-integral analyticity route. -/
theorem rightHalfPlane_gamma_kernel_norm_le_of_re_ge
    {alpha c : ℝ} {z : ℂ} {x : ℝ}
    (hx : 0 ≤ x) (hz : c ≤ z.re) :
    ‖((x ^ (alpha - 1) : ℝ) : ℂ) *
        Complex.exp (-(z * (x : ℂ)))‖ ≤
      x ^ (alpha - 1) * Real.exp (-(c * x)) := by
  have hpow_nonneg : 0 ≤ x ^ (alpha - 1) :=
    Real.rpow_nonneg hx _
  have hexp_le :
      Real.exp (-(z.re * x)) ≤ Real.exp (-(c * x)) := by
    refine Real.exp_le_exp.mpr ?_
    have hmul : c * x ≤ z.re * x :=
      mul_le_mul_of_nonneg_right hz hx
    linarith
  calc
    ‖((x ^ (alpha - 1) : ℝ) : ℂ) *
        Complex.exp (-(z * (x : ℂ)))‖ =
        x ^ (alpha - 1) * Real.exp (-(z.re * x)) := by
          rw [norm_mul, Complex.norm_exp]
          simp [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg]
    _ ≤ x ^ (alpha - 1) * Real.exp (-(c * x)) :=
        mul_le_mul_of_nonneg_left hexp_le hpow_nonneg

/-- Pointwise complex differentiability of the complex-rate Gamma kernel with
respect to the rate parameter. This is the pointwise derivative input for the
dominated parameter-integral route. -/
theorem rightHalfPlane_gamma_kernel_hasDerivAt
    (alpha x : ℝ) (z : ℂ) :
    HasDerivAt
      (fun w : ℂ =>
        ((x ^ (alpha - 1) : ℝ) : ℂ) *
          Complex.exp (-(w * (x : ℂ))))
      (((x ^ (alpha - 1) : ℝ) : ℂ) *
        (-(x : ℂ) * Complex.exp (-(z * (x : ℂ))))) z := by
  have hlin :
      HasDerivAt (fun w : ℂ => -(w * (x : ℂ))) (-(x : ℂ)) z := by
    simpa using ((hasDerivAt_id z).mul_const (x : ℂ)).neg
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    (hlin.cexp.const_mul ((x ^ (alpha - 1) : ℝ) : ℂ))

/-- If the real part of a complex rate is bounded below by `c`, then the
pointwise rate-derivative of the Gamma kernel is dominated by the next Gamma
kernel with real rate `c`. -/
theorem rightHalfPlane_gamma_kernel_deriv_norm_le_of_re_ge
    {alpha c : ℝ} {z : ℂ} {x : ℝ}
    (hx : 0 < x) (hz : c ≤ z.re) :
    ‖((x ^ (alpha - 1) : ℝ) : ℂ) *
        (-(x : ℂ) * Complex.exp (-(z * (x : ℂ))))‖ ≤
      x ^ alpha * Real.exp (-(c * x)) := by
  have hx_nonneg : 0 ≤ x := le_of_lt hx
  have hpow_nonneg : 0 ≤ x ^ (alpha - 1) :=
    Real.rpow_nonneg hx_nonneg _
  have hexp_le :
      Real.exp (-(z.re * x)) ≤ Real.exp (-(c * x)) := by
    refine Real.exp_le_exp.mpr ?_
    have hmul : c * x ≤ z.re * x :=
      mul_le_mul_of_nonneg_right hz hx_nonneg
    linarith
  have hpow_mul : x ^ (alpha - 1) * x = x ^ alpha := by
    calc
      x ^ (alpha - 1) * x = x ^ (alpha - 1 + 1) := by
        rw [Real.rpow_add_one hx.ne' (alpha - 1)]
      _ = x ^ alpha := by ring_nf
  calc
    ‖((x ^ (alpha - 1) : ℝ) : ℂ) *
        (-(x : ℂ) * Complex.exp (-(z * (x : ℂ))))‖ =
        (x ^ (alpha - 1) * x) * Real.exp (-(z.re * x)) := by
          rw [norm_mul, norm_mul, Complex.norm_exp]
          simp [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg, abs_of_pos hx]
          ring
    _ = x ^ alpha * Real.exp (-(z.re * x)) := by
          rw [hpow_mul]
    _ ≤ x ^ alpha * Real.exp (-(c * x)) :=
        mul_le_mul_of_nonneg_left hexp_le
          (Real.rpow_nonneg hx_nonneg _)

/-- The real-rate bound for the pointwise rate-derivative is integrable on
`(0, ∞)`. Together with
`rightHalfPlane_gamma_kernel_deriv_norm_le_of_re_ge`, this is the uniform
domination ingredient needed for differentiating the parameterized kernel
integral. -/
theorem rightHalfPlane_gamma_kernel_deriv_bound_integrableOn
    {alpha c : ℝ} (halpha : 0 < alpha) (hc : 0 < c) :
    IntegrableOn
      (fun x : ℝ => x ^ alpha * Real.exp (-(c * x)))
      (Set.Ioi (0 : ℝ)) := by
  simpa [Real.rpow_one] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := alpha) (b := c)
      (by linarith) (by norm_num) hc)

/-- Around every right-half-plane rate `z₀`, the pointwise rate-derivative of
the Gamma kernel has a uniform Gamma-kernel bound on the ball of radius
`z₀.re / 2`. This is the local domination shape required by Mathlib's
parameter-integral differentiation theorem. -/
theorem rightHalfPlane_gamma_kernel_deriv_norm_le_on_ball
    {alpha : ℝ} {z₀ w : ℂ} {x : ℝ}
    (_hz₀ : z₀ ∈ complexRightHalfPlane)
    (hw : w ∈ Metric.ball z₀ (z₀.re / 2)) (hx : 0 < x) :
    ‖((x ^ (alpha - 1) : ℝ) : ℂ) *
        (-(x : ℂ) * Complex.exp (-(w * (x : ℂ))))‖ ≤
      x ^ alpha * Real.exp (-((z₀.re / 2) * x)) := by
  have hnorm_lt : ‖w - z₀‖ < z₀.re / 2 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hre_lower : z₀.re / 2 ≤ w.re := by
    have hneg_le_norm : -(w - z₀).re ≤ ‖w - z₀‖ := by
      exact (neg_le_abs _).trans (Complex.abs_re_le_norm _)
    have hdiff : z₀.re - w.re ≤ ‖w - z₀‖ := by
      simpa using hneg_le_norm
    linarith
  exact rightHalfPlane_gamma_kernel_deriv_norm_le_of_re_ge hx hre_lower

/-- The local derivative bound from
`rightHalfPlane_gamma_kernel_deriv_norm_le_on_ball` is integrable on
`(0, ∞)` for every right-half-plane center. -/
theorem rightHalfPlane_gamma_kernel_deriv_local_bound_integrableOn
    {alpha : ℝ} {z₀ : ℂ} (halpha : 0 < alpha)
    (hz₀ : z₀ ∈ complexRightHalfPlane) :
    IntegrableOn
      (fun x : ℝ => x ^ alpha * Real.exp (-((z₀.re / 2) * x)))
      (Set.Ioi (0 : ℝ)) := by
  exact rightHalfPlane_gamma_kernel_deriv_bound_integrableOn halpha
    (half_pos hz₀)

/-- The arbitrary-shape Gamma kernel is integrable for every complex rate in
the open right half-plane. This generalizes the characteristic-function rate
`r - i t` and supplies the basic integrability side condition for analytic
continuation in the complex-rate parameter. -/
theorem rightHalfPlane_gamma_kernel_integrableOn
    {alpha : ℝ} {z : ℂ} (halpha : 0 < alpha)
    (hz : z ∈ complexRightHalfPlane) :
    IntegrableOn (fun x : ℝ =>
      ((x ^ (alpha - 1) : ℝ) : ℂ) *
        Complex.exp (-(z * (x : ℂ))))
      (Set.Ioi (0 : ℝ)) := by
  have hz_re : 0 < z.re := hz
  have hreal :
      IntegrableOn
        (fun x : ℝ => x ^ (alpha - 1) * Real.exp (-(z.re * x)))
        (Set.Ioi (0 : ℝ)) := by
    simpa [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := alpha - 1) (b := z.re)
        (by linarith) (by norm_num) hz_re)
  rw [IntegrableOn, ← integrable_norm_iff (by fun_prop)]
  refine hreal.congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hx_nonneg : 0 ≤ x := le_of_lt hx
  have hpow_nonneg : 0 ≤ x ^ (alpha - 1) :=
    Real.rpow_nonneg hx_nonneg _
  change x ^ (alpha - 1) * Real.exp (-(z.re * x)) =
    ‖((x ^ (alpha - 1) : ℝ) : ℂ) *
      Complex.exp (-(z * (x : ℂ)))‖
  symm
  rw [norm_mul, Complex.norm_exp]
  simp [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg]

/-- The arbitrary-shape Gamma kernel integral is complex differentiable with
respect to the right-half-plane rate parameter. This is the local
parameter-integral glue: the pointwise derivative and its integrable local
bound are packaged through Mathlib's dominated derivative-under-integral
theorem. -/
theorem rightHalfPlane_gamma_kernel_integral_hasDerivAt
    {alpha : ℝ} (halpha : 0 < alpha)
    {z₀ : ℂ} (hz₀ : z₀ ∈ complexRightHalfPlane) :
    HasDerivAt
      (fun z : ℂ =>
        ∫ x in Set.Ioi (0 : ℝ),
          ((x ^ (alpha - 1) : ℝ) : ℂ) *
            Complex.exp (-(z * (x : ℂ))))
      (∫ x in Set.Ioi (0 : ℝ),
        ((x ^ (alpha - 1) : ℝ) : ℂ) *
          (-(x : ℂ) * Complex.exp (-(z₀ * (x : ℂ)))))
      z₀ := by
  let F : ℂ → ℝ → ℂ := fun z x =>
    ((x ^ (alpha - 1) : ℝ) : ℂ) *
      Complex.exp (-(z * (x : ℂ)))
  let F' : ℂ → ℝ → ℂ := fun z x =>
    ((x ^ (alpha - 1) : ℝ) : ℂ) *
      (-(x : ℂ) * Complex.exp (-(z * (x : ℂ))))
  let bound : ℝ → ℝ := fun x =>
    x ^ alpha * Real.exp (-((z₀.re / 2) * x))
  have hs : Metric.ball z₀ (z₀.re / 2) ∈ nhds z₀ :=
    Metric.ball_mem_nhds z₀ (half_pos hz₀)
  have hF_meas :
      ∀ᶠ z in nhds z₀,
        AEStronglyMeasurable (F z)
          (volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine Filter.Eventually.of_forall ?_
    intro z
    dsimp [F]
    fun_prop
  have hF_int :
      Integrable (F z₀) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa [F] using
      (rightHalfPlane_gamma_kernel_integrableOn halpha hz₀).integrable
  have hF'_meas :
      AEStronglyMeasurable (F' z₀)
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
    dsimp [F']
    fun_prop
  have h_bound :
      ∀ᵐ x ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ∀ z ∈ Metric.ball z₀ (z₀.re / 2), ‖F' z x‖ ≤ bound x := by
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro x hx z hz
    exact rightHalfPlane_gamma_kernel_deriv_norm_le_on_ball hz₀ hz hx
  have h_bound_integrable :
      Integrable bound (volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa [bound] using
      (rightHalfPlane_gamma_kernel_deriv_local_bound_integrableOn
        halpha hz₀).integrable
  have h_diff :
      ∀ᵐ x ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ∀ z ∈ Metric.ball z₀ (z₀.re / 2),
          HasDerivAt (fun w : ℂ => F w x) (F' z x) z := by
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro x _ z _
    simpa [F, F'] using rightHalfPlane_gamma_kernel_hasDerivAt alpha x z
  have hmain :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (F := F) (F' := F') (bound := bound)
      hs hF_meas hF_int hF'_meas h_bound h_bound_integrable h_diff
  simpa [F, F'] using hmain.2

/-- The right-half-plane Gamma kernel integral is complex differentiable on
the whole rate domain. This packages
`rightHalfPlane_gamma_kernel_integral_hasDerivAt` in the form expected by
Mathlib's analytic-on-neighborhood interface. -/
theorem rightHalfPlane_gamma_kernel_integral_differentiableOn
    {alpha : ℝ} (halpha : 0 < alpha) :
    DifferentiableOn ℂ
      (fun z : ℂ =>
        ∫ x in Set.Ioi (0 : ℝ),
          ((x ^ (alpha - 1) : ℝ) : ℂ) *
            Complex.exp (-(z * (x : ℂ))))
      complexRightHalfPlane := by
  intro z hz
  have h := rightHalfPlane_gamma_kernel_integral_hasDerivAt halpha hz
  rw [hasDerivAt_iff_hasFDerivAt] at h
  exact h.hasFDerivWithinAt.differentiableWithinAt

/-- The right-half-plane Gamma kernel integral is analytic on a neighborhood
of every point of the open right-half-plane. This is the reusable holomorphic
support theorem needed for the identity-continuation route. -/
theorem rightHalfPlane_gamma_kernel_integral_analyticOnNhd
    {alpha : ℝ} (halpha : 0 < alpha) :
    AnalyticOnNhd ℂ
      (fun z : ℂ =>
        ∫ x in Set.Ioi (0 : ℝ),
          ((x ^ (alpha - 1) : ℝ) : ℂ) *
            Complex.exp (-(z * (x : ℂ))))
      complexRightHalfPlane :=
  (rightHalfPlane_gamma_kernel_integral_differentiableOn halpha).analyticOnNhd
    complexRightHalfPlane_isOpen

/-- The candidate value
`(1 / z)^alpha * Gamma alpha` is complex differentiable throughout the
right-half-plane. The reciprocal stays in `Complex.slitPlane` because its real
part is positive there, so principal complex powers are branch-compatible on
this domain. -/
theorem rightHalfPlane_gamma_kernel_candidate_differentiableOn
    (alpha : ℝ) :
    DifferentiableOn ℂ
      (fun z : ℂ =>
        ((1 : ℂ) / z) ^ (alpha : ℂ) * (Real.Gamma alpha : ℂ))
      complexRightHalfPlane := by
  have hinv_diff :
      DifferentiableOn ℂ (fun z : ℂ => (1 : ℂ) / z)
        complexRightHalfPlane := by
    refine DifferentiableOn.div (differentiableOn_const (1 : ℂ))
      differentiableOn_id ?_
    intro z hz
    exact complexRightHalfPlane_ne_zero hz
  have hpow :
      DifferentiableOn ℂ (fun z : ℂ => ((1 : ℂ) / z) ^ (alpha : ℂ))
        complexRightHalfPlane := by
    refine DifferentiableOn.cpow_const hinv_diff ?_
    intro z hz
    rw [Complex.mem_slitPlane_iff]
    left
    simpa [complexRightHalfPlane, div_eq_mul_inv] using
      (complexRightHalfPlane_inv_mem hz)
  exact hpow.mul_const (Real.Gamma alpha : ℂ)

/-- The analytic candidate value for the complex-rate Gamma kernel on the
right half-plane. This is the second analytic input for the future identity
theorem glue against the positive real-rate Gamma integral. -/
theorem rightHalfPlane_gamma_kernel_candidate_analyticOnNhd
    (alpha : ℝ) :
    AnalyticOnNhd ℂ
      (fun z : ℂ =>
        ((1 : ℂ) / z) ^ (alpha : ℂ) * (Real.Gamma alpha : ℂ))
      complexRightHalfPlane :=
  (rightHalfPlane_gamma_kernel_candidate_differentiableOn alpha).analyticOnNhd
    complexRightHalfPlane_isOpen

/-- The existing Mathlib positive-real-rate Gamma integral is exactly the
agreement of the right-half-plane kernel integral with the candidate value on
positive real rates. -/
theorem rightHalfPlane_gamma_kernel_integral_eq_candidate_real_rate
    {alpha r : ℝ} (halpha : 0 < alpha) (hr : 0 < r) :
    (fun z : ℂ =>
      ∫ x in Set.Ioi (0 : ℝ),
        ((x ^ (alpha - 1) : ℝ) : ℂ) *
          Complex.exp (-(z * (x : ℂ)))) (r : ℂ) =
      (fun z : ℂ =>
        ((1 : ℂ) / z) ^ (alpha : ℂ) *
          (Real.Gamma alpha : ℂ)) (r : ℂ) := by
  simpa using complex_gamma_kernel_integral_real_rate halpha hr

/-- Identity-theorem glue for the right-half-plane Gamma kernel. Once the
positive real-rate agreement is packaged as a punctured-neighborhood frequent
equality at any right-half-plane base point, the arbitrary complex-rate value
identity follows on the whole domain. -/
theorem rightHalfPlane_gamma_kernel_integral_eq_candidate_on_rightHalfPlane_of_frequently_eq
    {alpha : ℝ} (halpha : 0 < alpha) {z₀ : ℂ}
    (hz₀ : z₀ ∈ complexRightHalfPlane)
    (hfreq :
      ∃ᶠ z in nhdsWithin z₀ {z₀}ᶜ,
        (fun w : ℂ =>
          ∫ x in Set.Ioi (0 : ℝ),
            ((x ^ (alpha - 1) : ℝ) : ℂ) *
              Complex.exp (-(w * (x : ℂ)))) z =
          (fun w : ℂ =>
            ((1 : ℂ) / w) ^ (alpha : ℂ) *
              (Real.Gamma alpha : ℂ)) z) :
    Set.EqOn
      (fun z : ℂ =>
        ∫ x in Set.Ioi (0 : ℝ),
          ((x ^ (alpha - 1) : ℝ) : ℂ) *
            Complex.exp (-(z * (x : ℂ))))
      (fun z : ℂ =>
        ((1 : ℂ) / z) ^ (alpha : ℂ) *
          (Real.Gamma alpha : ℂ))
      complexRightHalfPlane := by
  exact AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
    (rightHalfPlane_gamma_kernel_integral_analyticOnNhd halpha)
    (rightHalfPlane_gamma_kernel_candidate_analyticOnNhd alpha)
    complexRightHalfPlane_isPreconnected hz₀ hfreq

/-- Positive real rates accumulate at `1` inside the right half-plane, and the
Mathlib real-rate Gamma integral gives equality at all those rates. This is
the frequent-equality package needed by the analytic identity theorem. -/
theorem rightHalfPlane_gamma_kernel_integral_eq_candidate_frequently_real_rate
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∃ᶠ z in nhdsWithin (1 : ℂ) ({(1 : ℂ)}ᶜ),
      (fun w : ℂ =>
        ∫ x in Set.Ioi (0 : ℝ),
          ((x ^ (alpha - 1) : ℝ) : ℂ) *
            Complex.exp (-(w * (x : ℂ)))) z =
        (fun w : ℂ =>
          ((1 : ℂ) / w) ^ (alpha : ℂ) *
            (Real.Gamma alpha : ℂ)) z := by
  have hcast :
      Filter.Tendsto ((↑) : ℝ → ℂ)
        (nhdsWithin (1 : ℝ) ({(1 : ℝ)}ᶜ))
        (nhdsWithin (1 : ℂ) ({(1 : ℂ)}ᶜ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact tendsto_nhdsWithin_of_tendsto_nhds
        Complex.continuous_ofReal.continuousAt
    · exact eventually_nhdsWithin_iff.mpr
        (Filter.Eventually.of_forall fun r hr => by
          intro h
          exact hr (Complex.ofReal_injective h))
  have hpos :
      ∀ᶠ r in nhdsWithin (1 : ℝ) ({(1 : ℝ)}ᶜ), 0 < r :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_gt_nhds zero_lt_one)
  exact hcast.frequently
    ((hpos.mono fun r hr =>
      rightHalfPlane_gamma_kernel_integral_eq_candidate_real_rate
        halpha hr).frequently)

/-- The arbitrary-shape Gamma kernel value identity for every complex rate in
the right half-plane, obtained by analytic continuation from positive real
rates. -/
theorem rightHalfPlane_gamma_kernel_integral_eq_candidate_on_rightHalfPlane
    {alpha : ℝ} (halpha : 0 < alpha) :
    Set.EqOn
      (fun z : ℂ =>
        ∫ x in Set.Ioi (0 : ℝ),
          ((x ^ (alpha - 1) : ℝ) : ℂ) *
            Complex.exp (-(z * (x : ℂ))))
      (fun z : ℂ =>
        ((1 : ℂ) / z) ^ (alpha : ℂ) *
          (Real.Gamma alpha : ℂ))
      complexRightHalfPlane := by
  exact
    rightHalfPlane_gamma_kernel_integral_eq_candidate_on_rightHalfPlane_of_frequently_eq
      halpha (by norm_num [complexRightHalfPlane])
      (rightHalfPlane_gamma_kernel_integral_eq_candidate_frequently_real_rate
        halpha)

/-- Complex-rate Gamma kernel value on the whole right half-plane. -/
theorem rightHalfPlane_gamma_kernel_integral_eq_candidate
    {alpha : ℝ} (halpha : 0 < alpha) {z : ℂ}
    (hz : z ∈ complexRightHalfPlane) :
    ∫ x in Set.Ioi (0 : ℝ),
        ((x ^ (alpha - 1) : ℝ) : ℂ) *
          Complex.exp (-(z * (x : ℂ))) =
      ((1 : ℂ) / z) ^ (alpha : ℂ) *
        (Real.Gamma alpha : ℂ) :=
  (rightHalfPlane_gamma_kernel_integral_eq_candidate_on_rightHalfPlane
    halpha) hz

/-- The complex-rate Gamma kernel value specialized to characteristic-function
rates `r - i t`. -/
theorem complex_gamma_kernel_integral_complex_rate
    {alpha r : ℝ} (halpha : 0 < alpha) (hr : 0 < r) (t : ℝ) :
    ∫ x in Set.Ioi (0 : ℝ),
        ((x ^ (alpha - 1) : ℝ) : ℂ) *
          Complex.exp
            (-(((r : ℂ) - Complex.I * (t : ℂ)) * (x : ℂ))) =
      ((1 : ℂ) / ((r : ℂ) - Complex.I * (t : ℂ))) ^ (alpha : ℂ) *
        (Real.Gamma alpha : ℂ) :=
  rightHalfPlane_gamma_kernel_integral_eq_candidate halpha
    (complex_rate_mem_rightHalfPlane hr)
