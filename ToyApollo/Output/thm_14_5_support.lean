import ToyApollo.Output.chapter14_tightness_support

/-!
Proof support for Theorem 14.5.
-/

open Filter MeasureTheory Set Complex Real
open scoped Topology RealInnerProductSpace ENNReal

noncomputable section

/-- Characteristic function of a probability distribution on `ℝ`. -/
def thm_14_5_characteristicFunction (P : ProbabilityMeasure ℝ) (t : ℝ) : ℂ :=
  charFun (P : Measure ℝ) t

/-- The source hypothesis that the characteristic functions converge pointwise
to a limiting function `c`. -/
def thm_14_5_characteristicConvergence
    (Pseq : ℕ → ProbabilityMeasure ℝ) (c : ℝ → ℂ) : Prop :=
  ∀ t : ℝ,
    Tendsto (fun n : ℕ => thm_14_5_characteristicFunction (Pseq n) t) atTop (𝓝 (c t))

/-- Tail mass outside the symmetric interval `[-M, M]`. -/
def thm_14_5_tailMass
    (P : ProbabilityMeasure ℝ) (M : ℝ) : ℝ :=
  chapter14_tailMass P M

/-- Tail mass decreases as the cutoff grows. -/
theorem thm_14_5_tailMass_mono
    (P : ProbabilityMeasure ℝ) {M0 M : ℝ} (hM : M0 ≤ M) :
    thm_14_5_tailMass P M ≤ thm_14_5_tailMass P M0 := by
  simpa [thm_14_5_tailMass] using
    chapter14_tailMass_mono P hM

/-- A uniform tail estimate, the final quantitative output of the characteristic
function argument in the textbook proof. -/
def thm_14_5_uniformTailBound
    (Pseq : ℕ → ProbabilityMeasure ℝ) : Prop :=
  chapter14_uniformTailBound Pseq

/-- The elementary bridge from a uniform tail estimate to Definition 14.3. -/
theorem thm_14_5_of_uniformTailBound
    (Pseq : ℕ → ProbabilityMeasure ℝ)
    (htail : thm_14_5_uniformTailBound Pseq) :
    def_14_3 Pseq := by
  exact chapter14_of_uniformTailBound Pseq htail

/-- The interval form of Definition 14.3 also gives the tail formulation used
in the proof of Theorem 14.5. -/
theorem thm_14_5_uniformTailBound_of_def_14_3
    (Pseq : ℕ → ProbabilityMeasure ℝ)
    (hTight : def_14_3 Pseq) :
    thm_14_5_uniformTailBound Pseq := by
  exact chapter14_uniformTailBound_of_def_14_3 Pseq hTight

/-- The source proof first identifies the limit at zero of the characteristic
functions. -/
theorem thm_14_5_source_route_characteristic_at_zero
    (Pseq : ℕ → ProbabilityMeasure ℝ) (c : ℝ → ℂ)
    (hchar : thm_14_5_characteristicConvergence Pseq c) :
    c 0 = 1 := by
  symm
  simpa [thm_14_5_characteristicFunction] using hchar 0

/-- Mathlib's `sinc`-normalized characteristic-function interval identity.
This is used below only as analytic substrate, not as the source Fubini
obligation itself. -/
theorem thm_14_5_source_route_interval_charFun_sinc_identity
    (Pseq : ℕ → ProbabilityMeasure ℝ) (n : ℕ) {u : ℝ} (hu : 0 < u) :
    ∫ t in -u..u, thm_14_5_characteristicFunction (Pseq n) t
      =
        2 * (u : ℂ) *
          (((∫ x, Real.sinc (u * x) ∂(Pseq n : Measure ℝ)) : ℝ) : ℂ) := by
  haveI : IsProbabilityMeasure (Pseq n : Measure ℝ) := (Pseq n).property
  simpa [thm_14_5_characteristicFunction] using
    (integral_charFun_Icc (μ := (Pseq n : Measure ℝ)) hu)

set_option backward.isDefEq.respectTransparency false in
/-- The source Fubini identity (14.3): the interval integral of `1 - phi_n`
is the iterated integral of `1 - exp (i t x)`.  The exchange is justified by
the bounded integrand on the finite interval. -/
theorem thm_14_5_source_route_fubini_identity
    (Pseq : ℕ → ProbabilityMeasure ℝ) (n : ℕ) {u : ℝ} (hu : 0 < u) :
    ∫ t in -u..u, (1 - thm_14_5_characteristicFunction (Pseq n) t)
      =
        ∫ x, ∫ t in -u..u, (1 - cexp (t * x * I)) ∂volume
          ∂(Pseq n : Measure ℝ) := by
  haveI : IsProbabilityMeasure (Pseq n : Measure ℝ) := (Pseq n).property
  have h_exp_prod :
      Integrable (Function.uncurry fun (t x : ℝ) ↦ cexp (t * x * I))
        ((volume.restrict (Set.uIoc (-u) u)).prod (Pseq n : Measure ℝ)) := by
    simp only [neg_le_self_iff, hu.le, Set.uIoc_of_le]
    rw [← integrable_norm_iff (by fun_prop)]
    suffices
        (fun a =>
            ‖Function.uncurry (fun (t x : ℝ) ↦ cexp (t * x * I)) a‖)
          = fun _ ↦ 1 by
      rw [this]
      fun_prop
    ext p
    rw [← Prod.mk.eta (p := p)]
    norm_cast
    simp only [Function.uncurry_apply_pair, norm_exp_ofReal_mul_I]
  have h_int :
      Integrable
        (Function.uncurry fun (t x : ℝ) ↦ 1 - cexp (t * x * I))
        ((volume.restrict (Set.uIoc (-u) u)).prod (Pseq n : Measure ℝ)) := by
    have h_const :
        Integrable (Function.uncurry fun (_t _x : ℝ) ↦ (1 : ℂ))
          ((volume.restrict (Set.uIoc (-u) u)).prod
            (Pseq n : Measure ℝ)) := by
      simp only [neg_le_self_iff, hu.le, Set.uIoc_of_le]
      fun_prop
    exact h_const.sub h_exp_prod
  have hpoint :
      ∀ t : ℝ,
        1 - thm_14_5_characteristicFunction (Pseq n) t
          = ∫ x, (1 - cexp (t * x * I)) ∂(Pseq n : Measure ℝ) := by
    intro t
    have h_exp :
        Integrable (fun x : ℝ => cexp (t * x * I))
          (Pseq n : Measure ℝ) := by
      rw [← integrable_norm_iff (by fun_prop)]
      suffices (fun x : ℝ => ‖cexp (t * x * I)‖) = fun _ ↦ 1 by
        rw [this]
        fun_prop
      ext x
      norm_cast
      simp only [norm_exp_ofReal_mul_I]
    rw [integral_sub (integrable_const (1 : ℂ)) h_exp]
    simp [thm_14_5_characteristicFunction, charFun_apply_real]
  calc
    ∫ t in -u..u, (1 - thm_14_5_characteristicFunction (Pseq n) t)
        =
          ∫ t in -u..u,
            ∫ x, (1 - cexp (t * x * I)) ∂(Pseq n : Measure ℝ) := by
          congr with t
          exact hpoint t
    _ =
        ∫ x, ∫ t in -u..u, (1 - cexp (t * x * I)) ∂volume
          ∂(Pseq n : Measure ℝ) := by
          rw [intervalIntegral_integral_swap h_int]

set_option backward.isDefEq.respectTransparency false in
/-- The exponential part of the inner integral in (14.4), expressed through
the standard `sinc` kernel. -/
theorem thm_14_5_source_route_inner_exp_integral_identity
    {u x : ℝ} (hu : 0 < u) (hx : x ≠ 0) :
    ∫ t in -u..u, cexp (t * x * I)
      =
        2 * (u : ℂ) * (Real.sinc (u * x) : ℂ) := by
  have hchange :
      ∫ t in -u..u, cexp (t * x * I)
        =
          x⁻¹ * ∫ s in -(x * u)..x * u, cexp (s * I) ∂volume := by
    have h :=
      intervalIntegral.integral_comp_smul_deriv (E := ℂ) (a := -u) (b := u)
        (f := fun t ↦ x * t) (f' := fun _ ↦ x)
        (g := fun s ↦ cexp (s * I)) ?_ (by fun_prop) (by fun_prop)
    swap
    · intro t ht
      simp_rw [mul_comm x]
      exact hasDerivAt_mul_const _
    simp only [Function.comp_apply, ofReal_mul, real_smul,
      intervalIntegral.integral_const_mul, mul_neg] at h
    rw [← h, ← mul_assoc]
    norm_cast
    simp [mul_comm _ x, mul_inv_cancel₀ hx]
  rw [hchange, integral_exp_mul_I_eq_sinc]
  norm_cast
  field_simp [hx]

/-- The source inner integral computation (14.4): away from `x = 0`, the
integral of `1 - exp (i t x)` over `[-u,u]` is `2 * (u - sin (u*x) / x)`. -/
theorem thm_14_5_source_route_inner_integral_identity
    {u x : ℝ} (hu : 0 < u) (hx : x ≠ 0) :
    ∫ t in -u..u, (1 - cexp (t * x * I))
      =
        (((2 : ℝ) * (u - Real.sin (u * x) / x)) : ℂ) := by
  have hconst : ∫ t in -u..u, (1 : ℂ) = 2 * (u : ℂ) := by
    simp only [intervalIntegral.integral_const, sub_neg_eq_add]
    calc
      (u + u) • (1 : ℂ) = (((u + u : ℝ)) : ℂ) := by simp
      _ = 2 * (u : ℂ) := by norm_num; ring
  have hexp_int :
      IntervalIntegrable (fun t : ℝ => cexp (t * x * I)) volume (-u) u := by
    exact
      (by fun_prop : Continuous fun t : ℝ => cexp (t * x * I)).intervalIntegrable
        _ _
  rw [intervalIntegral.integral_sub intervalIntegrable_const hexp_int]
  rw [hconst, thm_14_5_source_route_inner_exp_integral_identity hu hx]
  have hsinc :
      Real.sinc (u * x) = Real.sin (u * x) / (u * x) :=
    Real.sinc_of_ne_zero (mul_ne_zero hu.ne' hx)
  rw [hsinc]
  norm_cast
  field_simp [hu.ne', hx]

/-- The inner integral in the `sinc` form used to combine (14.3) and (14.4).
At `x = 0` both sides vanish, so this removes the point-exception from the
integral statement. -/
theorem thm_14_5_source_route_inner_integral_sinc_identity
    {u x : ℝ} (hu : 0 < u) :
    ∫ t in -u..u, (1 - cexp (t * x * I))
      =
        2 * (u : ℂ) * (1 - (Real.sinc (u * x) : ℂ)) := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [thm_14_5_source_route_inner_integral_identity hu hx]
    have hsinc : Real.sinc (u * x) = Real.sin (u * x) / (u * x) :=
      Real.sinc_of_ne_zero (mul_ne_zero hu.ne' hx)
    rw [hsinc]
    norm_cast
    field_simp [hu.ne', hx]

/-- Combining the interval identity with the constant integral gives the
averaged kernel identity in the normalized form
`(2u)^{-1} ∫(1 - phi_n) = 1 - ∫ sinc`. -/
theorem thm_14_5_source_route_averaged_kernel_identity
    (Pseq : ℕ → ProbabilityMeasure ℝ) (n : ℕ) {u : ℝ} (hu : 0 < u) :
    (2 : ℂ)⁻¹ * (u : ℂ)⁻¹ *
        ∫ t in -u..u, (1 - thm_14_5_characteristicFunction (Pseq n) t)
      =
        (1 : ℂ) -
          (((∫ x, Real.sinc (u * x) ∂(Pseq n : Measure ℝ)) : ℝ) : ℂ) := by
  haveI : IsProbabilityMeasure (Pseq n : Measure ℝ) := (Pseq n).property
  let μ : Measure ℝ := (Pseq n : Measure ℝ)
  have hfubini := thm_14_5_source_route_fubini_identity Pseq n hu
  rw [hfubini]
  have hinner :
      (fun x : ℝ => ∫ t in -u..u, (1 - cexp (t * x * I)) ∂volume)
        =
          fun x : ℝ => (2 * (u : ℂ)) * (1 - (sinc (u * x) : ℂ)) := by
    funext x
    exact thm_14_5_source_route_inner_integral_sinc_identity hu
  rw [hinner]
  have hconstmul :
      ∫ x, (2 * (u : ℂ)) * (1 - (sinc (u * x) : ℂ)) ∂μ
        =
          (2 * (u : ℂ)) *
            ∫ x, (1 - (sinc (u * x) : ℂ)) ∂μ := by
    exact integral_const_mul (μ := μ) (r := (2 * (u : ℂ)))
      (f := fun x : ℝ => 1 - (sinc (u * x) : ℂ))
  change
    (2 : ℂ)⁻¹ * (u : ℂ)⁻¹ *
        (∫ x, (2 * (u : ℂ)) * (1 - (sinc (u * x) : ℂ)) ∂μ)
      =
        (1 : ℂ) - (((∫ x, sinc (u * x) ∂μ) : ℝ) : ℂ)
  rw [hconstmul]
  have h_sinc_real : Integrable (fun x : ℝ => sinc (u * x)) μ := by
    exact
      (integrable_map_measure stronglyMeasurable_sinc.aestronglyMeasurable
        (by fun_prop)).mp integrable_sinc
  have h_sinc_complex :
      Integrable (fun x : ℝ => (sinc (u * x) : ℂ)) μ :=
    h_sinc_real.ofReal
  have hsimp :
      ∫ x, (1 - (sinc (u * x) : ℂ)) ∂μ
        =
          (1 : ℂ) - (((∫ x, sinc (u * x) ∂μ) : ℝ) : ℂ) := by
    rw [integral_sub (integrable_const (1 : ℂ)) h_sinc_complex]
    have hint_ofReal :
        ∫ a, ((sinc (u * a) : ℝ) : ℂ) ∂μ
          =
            (((∫ a, sinc (u * a) ∂μ) : ℝ) : ℂ) := by
      exact integral_ofReal
    rw [hint_ofReal]
    simp [μ]
  rw [hsimp]
  field_simp [Complex.ofReal_ne_zero.mpr hu.ne']

/-- The sine-kernel lower bound on the tail.  In the normalized `sinc` form
used above, the source bound is `1 <= 2 * (1 - sinc (u*x))` whenever
`|x| >= 2/u`. -/
theorem thm_14_5_source_route_kernel_tail_lower_bound
    {u x : ℝ} (hu : 0 < u) (hx : 2 / u ≤ |x|) :
    (1 : ℝ) ≤ 2 * (1 - Real.sinc (u * x)) := by
  have hux_abs_ge : (2 : ℝ) ≤ |u * x| := by
    have hxmul : u * (2 / u) ≤ u * |x| :=
      mul_le_mul_of_nonneg_left hx hu.le
    have hleft : u * (2 / u) = 2 := by
      field_simp [hu.ne']
    have habs : |u * x| = u * |x| := by
      rw [abs_mul, abs_of_pos hu]
    linarith
  have hux_pos : 0 < |u * x| := lt_of_lt_of_le (by norm_num) hux_abs_ge
  have hux_ne : u * x ≠ 0 := by
    exact abs_pos.mp hux_pos
  have hinv : |u * x|⁻¹ ≤ (2 : ℝ)⁻¹ := by
    exact (inv_le_inv₀ hux_pos (by norm_num : (0 : ℝ) < 2)).mpr hux_abs_ge
  have hsinc : Real.sinc (u * x) ≤ (1 / 2 : ℝ) := by
    have hs := Real.sinc_le_inv_abs hux_ne
    have hhalf : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    linarith
  nlinarith

/-- The Fourier-kernel tail estimate used in the textbook proof.  This is the
named theorem-level landing for the source tail bound. -/
theorem thm_14_5_source_route_tail_bound_by_averaged_characteristic
    (Pseq : ℕ → ProbabilityMeasure ℝ) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    thm_14_5_tailMass (Pseq n) r
      ≤ 2⁻¹ * r *
        ‖∫ t in -2 * r⁻¹..2 * r⁻¹,
          1 - thm_14_5_characteristicFunction (Pseq n) t‖ := by
  let μ : Measure ℝ := (Pseq n : Measure ℝ)
  haveI : IsProbabilityMeasure μ := (Pseq n).property
  let u : ℝ := 2 * r⁻¹
  have hu : 0 < u := by positivity
  have integrable_sinc_const_mul (a : ℝ) :
      Integrable (fun x ↦ sinc (a * x)) μ :=
    (integrable_map_measure stronglyMeasurable_sinc.aestronglyMeasurable
      (by fun_prop)).mp integrable_sinc
  have h_two_div_u : 2 / u = r := by
    simp [u]
    field_simp [hr.ne']
  have h_avg := thm_14_5_source_route_averaged_kernel_identity Pseq n hu
  have h_avg_u :
      (2 : ℂ)⁻¹ * (u : ℂ)⁻¹ *
          ∫ t in -u..u, (1 - thm_14_5_characteristicFunction (Pseq n) t)
        =
          (1 : ℂ) - (((∫ x, sinc (u * x) ∂μ) : ℝ) : ℂ) := by
    simpa [μ] using h_avg
  have h_integral_one_sub_real :
      ∫ x, (1 - sinc (u * x)) ∂μ
        =
          1 - ∫ x, sinc (u * x) ∂μ := by
    rw [integral_sub (integrable_const (1 : ℝ)) (integrable_sinc_const_mul u)]
    simp [μ]
  have h_avg_real :
      (((∫ x, (1 - sinc (u * x)) ∂μ) : ℝ) : ℂ)
        =
          (2 : ℂ)⁻¹ * (u : ℂ)⁻¹ *
            ∫ t in -u..u, (1 - thm_14_5_characteristicFunction (Pseq n) t) := by
    rw [h_integral_one_sub_real]
    simpa [ofReal_inv] using h_avg_u.symm
  calc
    thm_14_5_tailMass (Pseq n) r
        = μ.real {x | r < |x|} := by
          simp [thm_14_5_tailMass, chapter14_tailMass, μ]
    _ = ∫ x in {x | r < |x|}, 1 ∂μ := by simp
    _ = 2 * ∫ x in {x | r < |x|}, 2⁻¹ ∂μ := by
          rw [← integral_const_mul]
          congr with _
          rw [mul_inv_cancel₀ (by positivity : (2 : ℝ) ≠ 0)]
    _ ≤ 2 * ∫ x in {x | r < |x|}, 1 - sinc (u * x) ∂μ := by
          gcongr (2 : ℝ) * ?_
          refine setIntegral_mono_on ?_
            ((integrable_const _).sub
              (integrable_sinc_const_mul u)).integrableOn ?_ fun x hx ↦ ?_
          · exact Integrable.integrableOn <| by fun_prop
          · exact MeasurableSet.preimage measurableSet_Ioi (by fun_prop)
          · have hkernel :=
              thm_14_5_source_route_kernel_tail_lower_bound (u := u) (x := x)
                hu ?_
            · linarith
            · rw [h_two_div_u]
              exact le_of_lt (by simpa using hx)
    _ ≤ 2 * ∫ x, 1 - sinc (u * x) ∂μ := by
          grw [setIntegral_le_integral (by fun_prop) <| ae_of_all _ fun x ↦ ?_]
          simp only [Pi.zero_apply, sub_nonneg]
          exact sinc_le_one (u * x)
    _ ≤ 2 * ‖∫ x, 1 - sinc (u * x) ∂μ‖ := by
          gcongr
          exact Real.le_norm_self _
    _ = 2⁻¹ * r *
          ‖∫ t in -2 * r⁻¹..2 * r⁻¹,
            1 - thm_14_5_characteristicFunction (Pseq n) t‖ := by
          have hnorm :
              ‖∫ x, 1 - sinc (u * x) ∂μ‖
                =
                  ‖(2 : ℂ)⁻¹ * (u : ℂ)⁻¹ *
                    ∫ t in -u..u,
                      (1 - thm_14_5_characteristicFunction (Pseq n) t)‖ := by
            rw [← h_avg_real]
            norm_cast
          rw [hnorm]
          simp only [u]
          rw [norm_mul, norm_mul]
          simp
          rw [abs_of_pos hr]
          ring

/-- Dominated convergence for the characteristic-function integrals on the
fixed interval used in the source proof. -/
theorem thm_14_5_source_route_dominated_convergence_bound
    (Pseq : ℕ → ProbabilityMeasure ℝ) (c : ℝ → ℂ)
    (hchar : thm_14_5_characteristicConvergence Pseq c)
    {r : ℝ} (hr : 0 < r) :
    Tendsto
      (fun n : ℕ =>
        ∫ t in -2 * r⁻¹..2 * r⁻¹,
          1 - thm_14_5_characteristicFunction (Pseq n) t)
      atTop
      (𝓝 (∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - c t)) := by
  have hr' : -(2 * r⁻¹) ≤ 2 * r⁻¹ := by
    rw [neg_le_self_iff]
    positivity
  simp only [neg_mul]
  simp_rw [intervalIntegral.integral_of_le hr']
  refine tendsto_integral_of_dominated_convergence (fun _ : ℝ => 2) ?_
    (by fun_prop) ?_ ?_
  · intro n
    have hmeas :
        Measurable
          (fun t : ℝ =>
            1 - charFun ((Pseq n : ProbabilityMeasure ℝ) : Measure ℝ) t) := by
      fun_prop
    simpa [thm_14_5_characteristicFunction] using hmeas.aestronglyMeasurable
  · intro n
    haveI : IsProbabilityMeasure (Pseq n : Measure ℝ) := (Pseq n).property
    exact ae_of_all _ fun _ =>
      (by
        simpa [thm_14_5_characteristicFunction] using
          (norm_one_sub_charFun_le_two (μ := (Pseq n : Measure ℝ))))
  · exact ae_of_all _ fun t =>
      tendsto_const_nhds.sub
        (by simpa [thm_14_5_characteristicFunction] using hchar t)

/-- Continuity at zero makes the source proof's small-window limiting integral
arbitrarily small. -/
theorem thm_14_5_source_route_continuity_small_u_bound
    (Pseq : ℕ → ProbabilityMeasure ℝ) (c : ℝ → ℂ)
    (hchar : thm_14_5_characteristicConvergence Pseq c)
    (hcont : ContinuousAt c 0) :
    Tendsto
      (fun r : ℝ =>
        2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - c t‖)
      atTop (𝓝 0) := by
  have hf_tendsto := hcont.tendsto
  rw [Metric.tendsto_nhds_nhds] at hf_tendsto
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hf0 : c 0 = 1 :=
    thm_14_5_source_route_characteristic_at_zero Pseq c hchar
  simp only [gt_iff_lt, dist_eq_norm_sub', zero_sub, norm_neg, hf0] at hf_tendsto
  simp only [ge_iff_le, neg_mul, dist_zero_right, norm_mul, norm_inv,
    Real.norm_ofNat, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  obtain ⟨δ, hδ, hδ_lt⟩ :
      ∃ δ, 0 < δ ∧ ∀ ⦃x : ℝ⦄, ‖x‖ < δ → ‖1 - c x‖ < ε / 4 :=
    hf_tendsto (ε / 4) (by positivity)
  refine ⟨4 * δ⁻¹, fun r hrδ => ?_⟩
  have hr : 0 < r := lt_of_lt_of_le (by positivity) hrδ
  have hr' : -(2 * r⁻¹) ≤ 2 * r⁻¹ := by
    rw [neg_le_self_iff]
    positivity
  have h_le_Ioc
      (x : ℝ) (hx : x ∈ Set.Ioc (-(2 * r⁻¹)) (2 * r⁻¹)) :
      ‖1 - c x‖ ≤ ε / 4 := by
    refine (hδ_lt ?_).le
    simp only [Real.norm_eq_abs]
    calc
      |x| ≤ 2 * r⁻¹ := by
        simp at hx
        grind
      _ < δ := by
        rw [← lt_div_iff₀' (by positivity), inv_lt_comm₀ hr (by positivity)]
        refine lt_of_lt_of_le ?_ hrδ
        field_simp
        norm_num
  rw [abs_of_nonneg hr.le]
  calc
    2⁻¹ * r * ‖∫ t in -(2 * r⁻¹)..2 * r⁻¹, 1 - c t‖
        ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, ‖1 - c t‖ := by
          grw [intervalIntegral.norm_integral_le_integral_norm hr']
    _ ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, ε / 4 := by
          gcongr
          rw [intervalIntegral.integral_of_le hr',
            intervalIntegral.integral_of_le hr']
          have hc_meas : Measurable c := by
            refine
              measurable_of_tendsto_metrizable
                (f := fun n t =>
                  charFun ((Pseq n : ProbabilityMeasure ℝ) : Measure ℝ) t)
                (by fun_prop) ?_
            rwa [tendsto_pi_nhds]
          refine integral_mono_ae ?_ (by fun_prop) ?_
          · refine Integrable.mono' (integrable_const (ε / 4)) ?_ ?_
            · exact Measurable.aestronglyMeasurable <| by fun_prop
            · simpa using ae_restrict_of_forall_mem measurableSet_Ioc h_le_Ioc
          · exact ae_restrict_of_forall_mem measurableSet_Ioc h_le_Ioc
    _ = ε / 2 := by
          simp
          field
    _ < ε := by
          simp [hε]

/-- For every single probability measure and every lower cutoff, some larger
cutoff has small tail.  This is the one-measure ingredient in the textbook
finite-prefix step. -/
theorem thm_14_5_source_route_single_tail_bound
    (P : ProbabilityMeasure ℝ) {ε M0 : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, M0 ≤ M ∧ thm_14_5_tailMass P M < ε := by
  let Pconst : ℕ → ProbabilityMeasure ℝ := fun _ => P
  have hMathlibTight : def_14_3_mathlibTight Pconst := by
    rw [def_14_3_mathlibTight]
    have hsingleton :
        IsTightMeasureSet ({((P : ProbabilityMeasure ℝ) : Measure ℝ)} :
          Set (Measure ℝ)) := by
      haveI : IsProbabilityMeasure (P : Measure ℝ) := P.property
      exact isTightMeasureSet_singleton
    simpa [Pconst, Set.range_const] using hsingleton
  have htail :
      thm_14_5_uniformTailBound Pconst :=
    thm_14_5_uniformTailBound_of_def_14_3 Pconst <|
      def_14_3_of_mathlibTight Pconst hMathlibTight
  rcases htail ε hε with ⟨R, _hR_nonneg, hRtail⟩
  refine ⟨max M0 R, le_max_left M0 R, ?_⟩
  exact lt_of_le_of_lt
    (thm_14_5_tailMass_mono P (le_max_right M0 R))
    (by simpa [Pconst] using hRtail 0)

/-- The textbook finite-prefix step: once all large indices are controlled from
some cutoff `M0`, finitely many earlier laws can be absorbed by increasing the
cutoff. -/
theorem thm_14_5_source_route_finite_prefix_tail_bound
    (Pseq : ℕ → ProbabilityMeasure ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∀ M0 : ℝ, 0 ≤ M0 →
      ∃ M : ℝ, M0 ≤ M ∧
        ∀ n : ℕ, n < N → thm_14_5_tailMass (Pseq n) M < ε := by
  intro ε hε
  intro N
  induction N with
  | zero =>
      intro M0 _hM0
      exact ⟨M0, le_rfl, by intro n hn; exact (Nat.not_lt_zero n hn).elim⟩
  | succ N ih =>
      intro M0 hM0
      rcases ih M0 hM0 with ⟨Mprev, hM0prev, hprev⟩
      rcases thm_14_5_source_route_single_tail_bound (Pseq N) hε
        (M0 := Mprev) with ⟨MN, hMprevN, hMNtail⟩
      refine ⟨MN, hM0prev.trans hMprevN, ?_⟩
      intro n hn
      have hnle : n < N ∨ n = N := Nat.lt_succ_iff_lt_or_eq.mp hn
      cases hnle with
      | inl hlt =>
          exact lt_of_le_of_lt
            (thm_14_5_tailMass_mono (Pseq n) hMprevN)
            (hprev n hlt)
      | inr heq =>
          simpa [heq] using hMNtail

/-- The analytic source estimates imply a common tail cutoff for all sufficiently
large indices. -/
theorem thm_14_5_source_route_eventual_tail_bound
    (Pseq : ℕ → ProbabilityMeasure ℝ) (c : ℝ → ℂ)
    (hchar : thm_14_5_characteristicConvergence Pseq c)
    (hcont : ContinuousAt c 0) :
    ∀ ε : ℝ, 0 < ε → ∃ M0 : ℝ, 0 ≤ M0 ∧ ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → thm_14_5_tailMass (Pseq n) M0 < ε := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  have hcont_small :=
    thm_14_5_source_route_continuity_small_u_bound Pseq c hchar hcont
  rcases (Metric.tendsto_atTop.mp hcont_small (ε / 2) hε2) with
    ⟨R, hR⟩
  let r : ℝ := max R 1
  have hRle : R ≤ r := le_max_left R 1
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  have hfirst_dist := hR r hRle
  have hfirst :
      2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - c t‖ < ε / 2 := by
    have hr_abs : |r| = r := abs_of_nonneg hr_pos.le
    simpa [Real.dist_eq, hr_abs] using hfirst_dist
  have hdct :=
    thm_14_5_source_route_dominated_convergence_bound Pseq c hchar hr_pos
  have hscaled :
      Tendsto
        (fun n : ℕ =>
          2⁻¹ * r *
            ‖(∫ t in -2 * r⁻¹..2 * r⁻¹,
                1 - thm_14_5_characteristicFunction (Pseq n) t)
              - (∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - c t)‖)
        atTop (𝓝 0) := by
    have hconst :
        Tendsto
          (fun _ : ℕ => (∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - c t))
          atTop
          (𝓝 (∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - c t)) :=
      tendsto_const_nhds
    have hsub := hdct.sub hconst
    simpa using (Tendsto.norm hsub).const_mul (2⁻¹ * r)
  rcases (Metric.tendsto_atTop.mp hscaled (ε / 2) hε2) with
    ⟨N, hN⟩
  refine ⟨r, hr_pos.le, N, ?_⟩
  intro n hn
  let A : ℂ :=
    ∫ t in -2 * r⁻¹..2 * r⁻¹,
      1 - thm_14_5_characteristicFunction (Pseq n) t
  let B : ℂ := ∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - c t
  have hdiff_dist := hN n hn
  have hdiff : 2⁻¹ * r * ‖A - B‖ < ε / 2 := by
    have hr_abs : |r| = r := abs_of_nonneg hr_pos.le
    simpa [A, B, Real.dist_eq, hr_abs] using hdiff_dist
  have hnorm : ‖A‖ ≤ ‖B‖ + ‖A - B‖ := by
    calc
      ‖A‖ = ‖B + (A - B)‖ := by
        have hBA : B + (A - B) = A := by abel
        rw [hBA]
      _ ≤ ‖B‖ + ‖A - B‖ := norm_add_le _ _
  have hcoef_nonneg : 0 ≤ 2⁻¹ * r := by positivity
  have htri :
      2⁻¹ * r * ‖A‖
        ≤ 2⁻¹ * r * ‖B‖ + 2⁻¹ * r * ‖A - B‖ := by
    have := mul_le_mul_of_nonneg_left hnorm hcoef_nonneg
    nlinarith
  have htail :=
    thm_14_5_source_route_tail_bound_by_averaged_characteristic
      Pseq n hr_pos
  exact lt_of_le_of_lt htail (by nlinarith [hfirst, hdiff, htri])

/-- The textbook characteristic-function argument, formalized at theorem level:
tail control is obtained from the Fourier-kernel estimate, dominated
convergence, and continuity of the limiting characteristic function at zero. -/
theorem thm_14_5_source_route_limsup_tight
    (Pseq : ℕ → ProbabilityMeasure ℝ) (c : ℝ → ℂ)
    (hchar : thm_14_5_characteristicConvergence Pseq c)
    (hcont : ContinuousAt c 0) :
    def_14_3_mathlibTight Pseq := by
  rw [def_14_3_mathlibTight]
  let μ : ℕ → Measure ℝ :=
    fun n : ℕ => ((Pseq n : ProbabilityMeasure ℝ) : Measure ℝ)
  change IsTightMeasureSet (Set.range μ)
  haveI : ∀ i : ℕ, IsProbabilityMeasure (μ i) :=
    fun i => (Pseq i).property
  refine
    isTightMeasureSet_range_of_tendsto_limsup_measureReal_inner_of_norm_eq_one ℝ
      (μ := μ) (fun z hz => ?_) 1 (.of_forall fun _ => by simp [μ])
  have hlim (t : ℝ) :
      Tendsto (fun n : ℕ => charFun (μ n) t) atTop (𝓝 (c t)) := by
    simpa [μ, thm_14_5_characteristicFunction] using hchar t
  have h_le_4 n r (hr : 0 < r) :
      2⁻¹ * r *
          ‖∫ t in -2 * r⁻¹..2 * r⁻¹,
            1 - charFun (μ n) (t • z)‖
        ≤ 4 := by
    have hr' : -(2 * r⁻¹) ≤ 2 * r⁻¹ := by
      rw [neg_le_self_iff]
      positivity
    calc
      2⁻¹ * r *
          ‖∫ t in -2 * r⁻¹..2 * r⁻¹,
            1 - charFun (μ n) (t • z)‖
          ≤
            2⁻¹ * r *
              ∫ t in -(2 * r⁻¹)..2 * r⁻¹,
                ‖1 - charFun (μ n) (t • z)‖ := by
            grw [neg_mul, intervalIntegral.norm_integral_le_integral_norm hr']
      _ ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, 2 := by
            gcongr
            rw [intervalIntegral.integral_of_le hr',
              intervalIntegral.integral_of_le hr']
            refine integral_mono_of_nonneg ?_ (by fun_prop) ?_
            · exact ae_of_all _ fun _ => by positivity
            · exact ae_of_all _ fun _ => norm_one_sub_charFun_le_two
      _ ≤ 4 := by
            simp only [intervalIntegral.integral_const, sub_neg_eq_add,
              smul_eq_mul]
            field_simp
            norm_num
  have h_le n r (hr : 0 < r) :
      (μ n).real {x : ℝ | r < |⟪z, x⟫|}
        ≤
          2⁻¹ * r *
            ‖∫ t in -2 * r⁻¹..2 * r⁻¹,
              1 - charFun (μ n) (t • z)‖ :=
    measureReal_abs_inner_gt_le_integral_charFun hr
  have h_limsup_le r (hr : 0 < r) :
      limsup (fun n : ℕ => (μ n).real {x : ℝ | r < |⟪z, x⟫|}) atTop
        ≤
          2⁻¹ * r *
            ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - c (t • z)‖ := by
    calc
      limsup (fun n : ℕ => (μ n).real {x : ℝ | r < |⟪z, x⟫|}) atTop
          ≤
            limsup
              (fun n : ℕ =>
                2⁻¹ * r *
                  ‖∫ t in -2 * r⁻¹..2 * r⁻¹,
                    1 - charFun (μ n) (t • z)‖)
              atTop := by
            refine limsup_le_limsup (.of_forall fun n => h_le n r hr) ?_ ?_
            · exact IsCoboundedUnder.of_frequently_ge <|
                .of_forall fun _ => ENNReal.toReal_nonneg
            · refine ⟨4, ?_⟩
              simp only [eventually_map, eventually_atTop, ge_iff_le]
              exact ⟨0, fun n _ => h_le_4 n r hr⟩
      _ = 2⁻¹ * r *
            ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - c (t • z)‖ := by
            refine ((Tendsto.norm ?_).const_mul _).limsup_eq
            simp only [neg_mul]
            have hr' : -(2 * r⁻¹) ≤ 2 * r⁻¹ := by
              rw [neg_le_self_iff]
              positivity
            simp_rw [intervalIntegral.integral_of_le hr']
            refine
              tendsto_integral_of_dominated_convergence (fun _ => 2) ?_
                (by fun_prop) ?_ ?_
            · exact fun _ => Measurable.aestronglyMeasurable <| by fun_prop
            · exact fun _ => ae_of_all _ fun _ => norm_one_sub_charFun_le_two
            · exact ae_of_all _ fun _ => tendsto_const_nhds.sub (hlim _)
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (h := fun r : ℝ =>
        2⁻¹ * r *
          ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - c (t • z)‖)
      ?_ ?_ ?_
  rotate_left
  · filter_upwards [eventually_gt_atTop 0] with r hr
    refine le_limsup_of_le ?_ fun u hu => ?_
    · refine ⟨4, ?_⟩
      simp only [eventually_map, eventually_atTop, ge_iff_le]
      exact ⟨0, fun n _ => (h_le n r hr).trans (h_le_4 n r hr)⟩
    · exact ENNReal.toReal_nonneg.trans hu.exists.choose_spec
  · filter_upwards [eventually_gt_atTop 0] with r hr using h_limsup_le r hr
  have hf_tendsto := hcont.tendsto
  rw [Metric.tendsto_nhds_nhds] at hf_tendsto
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hf0 : c 0 = 1 :=
    thm_14_5_source_route_characteristic_at_zero Pseq c hchar
  simp only [gt_iff_lt, dist_eq_norm_sub', zero_sub, norm_neg, hf0] at hf_tendsto
  simp only [ge_iff_le, neg_mul, dist_zero_right, norm_mul, norm_inv,
    Real.norm_ofNat, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  obtain ⟨δ, hδ, hδ_lt⟩ :
      ∃ δ, 0 < δ ∧ ∀ ⦃x : ℝ⦄, ‖x‖ < δ → ‖1 - c x‖ < ε / 4 :=
    hf_tendsto (ε / 4) (by positivity)
  refine ⟨4 * δ⁻¹, fun r hrδ => ?_⟩
  have hr : 0 < r := lt_of_lt_of_le (by positivity) hrδ
  have hr' : -(2 * r⁻¹) ≤ 2 * r⁻¹ := by
    rw [neg_le_self_iff]
    positivity
  have h_le_Ioc
      (x : ℝ) (hx : x ∈ Set.Ioc (-(2 * r⁻¹)) (2 * r⁻¹)) :
      ‖1 - c (x • z)‖ ≤ ε / 4 := by
    refine (hδ_lt ?_).le
    simp only [norm_smul, Real.norm_eq_abs, mul_one, hz]
    calc
      |x| ≤ 2 * r⁻¹ := by
        simp at hx
        grind
      _ < δ := by
        rw [← lt_div_iff₀' (by positivity), inv_lt_comm₀ hr (by positivity)]
        refine lt_of_lt_of_le ?_ hrδ
        field_simp
        norm_num
  rw [abs_of_nonneg hr.le]
  calc
    2⁻¹ * r *
        ‖∫ t in -(2 * r⁻¹)..2 * r⁻¹, 1 - c (t • z)‖
        ≤
          2⁻¹ * r *
            ∫ t in -(2 * r⁻¹)..2 * r⁻¹, ‖1 - c (t • z)‖ := by
          grw [intervalIntegral.norm_integral_le_integral_norm hr']
    _ ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, ε / 4 := by
          gcongr
          rw [intervalIntegral.integral_of_le hr',
            intervalIntegral.integral_of_le hr']
          have hc_meas : Measurable c := by
            refine
              measurable_of_tendsto_metrizable
                (f := fun n t => charFun (μ n) t) (by fun_prop) ?_
            rwa [tendsto_pi_nhds]
          refine integral_mono_ae ?_ (by fun_prop) ?_
          · refine Integrable.mono' (integrable_const (ε / 4)) ?_ ?_
            · exact Measurable.aestronglyMeasurable <| by fun_prop
            · simpa using ae_restrict_of_forall_mem measurableSet_Ioc h_le_Ioc
          · exact ae_restrict_of_forall_mem measurableSet_Ioc h_le_Ioc
    _ = ε / 2 := by
          simp
          field
    _ < ε := by
          simp [hε]

/-- The theorem-level source route produces the uniform tail estimate used by
the final textbook-tightness bridge. -/
theorem thm_14_5_source_route_uniform_tail_bound
    (Pseq : ℕ → ProbabilityMeasure ℝ) (c : ℝ → ℂ)
    (hchar : thm_14_5_characteristicConvergence Pseq c)
    (hcont : ContinuousAt c 0) :
    thm_14_5_uniformTailBound Pseq := by
  intro ε hε
  rcases
    thm_14_5_source_route_eventual_tail_bound Pseq c hchar hcont ε hε with
    ⟨M0, hM0_nonneg, N, hlarge⟩
  rcases
    thm_14_5_source_route_finite_prefix_tail_bound Pseq ε hε N M0 hM0_nonneg with
    ⟨M, hM0M, hprefix⟩
  refine ⟨M, hM0_nonneg.trans hM0M, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · exact lt_of_le_of_lt
      (thm_14_5_tailMass_mono (Pseq n) hM0M)
      (hlarge n hn)
  · exact hprefix n (Nat.lt_of_not_ge hn)

/-- A named record of the proof obligations in the textbook proof of Theorem
14.5.  The final field is the uniform tail estimate obtained by combining
Fubini, the inner integral calculation, the kernel lower bound, continuity at
zero, dominated convergence, and the finite-prefix argument. -/
structure thm_14_5_SourceProofSpine
    (Pseq : ℕ → ProbabilityMeasure ℝ) (c : ℝ → ℂ)
    (hchar : thm_14_5_characteristicConvergence Pseq c)
    (hcont : ContinuousAt c 0) : Prop where
  characteristic_at_zero :
    c 0 = 1
  fubini_identity :
    ∀ n : ℕ, ∀ u : ℝ, 0 < u →
      (∫ t in Icc (-u) u,
          (1 - thm_14_5_characteristicFunction (Pseq n) t) ∂volume)
        =
      ∫ x,
        (∫ t in Icc (-u) u,
          (1 - Complex.exp (Complex.I * ((t * x : ℝ) : ℂ))) ∂volume)
        ∂(Pseq n : Measure ℝ)
  inner_integral_identity :
    ∀ u x : ℝ, 0 < u → x ≠ 0 →
      (∫ t in Icc (-u) u,
          (1 - Complex.exp (Complex.I * ((t * x : ℝ) : ℂ))) ∂volume)
        =
      ((2 : ℝ) * (u - Real.sin (u * x) / x) : ℂ)
  averaged_kernel_identity :
    ∀ n : ℕ, ∀ u : ℝ, 0 < u →
      ((u : ℂ)⁻¹ *
          ∫ t in Icc (-u) u,
            (1 - thm_14_5_characteristicFunction (Pseq n) t) ∂volume)
        =
      ∫ x,
        ((1 : ℂ) - ((Real.sin (u * x) / (u * x) : ℝ) : ℂ))
        ∂(Pseq n : Measure ℝ)
  kernel_tail_lower_bound :
    ∀ u x : ℝ, 0 < u → (2 / u) ≤ |x| →
      (1 : ℝ) ≤ 1 - Real.sin (u * x) / (u * x)
  tail_bound_by_averaged_characteristic :
    ∀ n : ℕ, ∀ u : ℝ, 0 < u →
      thm_14_5_tailMass (Pseq n) (2 / u)
        ≤ ‖
          ((u : ℂ)⁻¹ *
            ∫ t in Icc (-u) u,
              (1 - thm_14_5_characteristicFunction (Pseq n) t) ∂volume)‖
  continuity_small_u_bound :
    ∀ ε : ℝ, 0 < ε → ∃ u0 : ℝ, 0 < u0 ∧
      (u0)⁻¹ * ∫ t in Icc (-u0) u0, ‖1 - c t‖ ∂volume ≤ ε / 2
  dominated_convergence_bound :
    ∀ ε : ℝ, 0 < ε → ∀ u0 : ℝ, 0 < u0 → ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n →
        (u0)⁻¹ *
          ∫ t in Icc (-u0) u0,
            ‖c t - thm_14_5_characteristicFunction (Pseq n) t‖ ∂volume
          ≤ ε / 2
  finite_prefix_tail_bound :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∀ M0 : ℝ, 0 ≤ M0 →
      ∃ M : ℝ, M0 ≤ M ∧
        ∀ n : ℕ, n < N → thm_14_5_tailMass (Pseq n) M < ε
  uniform_tail_bound :
    thm_14_5_uniformTailBound Pseq

