import Mathlib
import ToyApollo.Output.def_9_1
import ToyApollo.Output.def_9_3
import ToyApollo.Output.thm_7_7
import ToyApollo.Output.thm_9_4

/-
TASK ID: thm_9_7
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter9-characteristic-functions
TASK CONTENT:
\begin{thmbox}{9.7}
\textbf{Derivatives of Characteristic Function.}
Suppose $\mathbb{E}[\lvert X\rvert^n]<\infty$. Then the $n$-th derivative of $\phi_X(t)$ exists and
\[
\phi_X^{(n)}(t)=\mathbb{E}[(iX)^n e^{iXt}].
\]
In particular,
\[
\mathbb{E}[X^n]=\frac{1}{i^n}\phi_X^{(n)}(0).
\]
\end{thmbox}

\textit{Sketch of Proof}
We prove the theorem for $n=1$ and $n=2$ only. Suppose $\mathbb{E}[\lvert X\rvert]<\infty$. We want to evaluate
\[
\lim_{h\to 0}\frac{\phi_X(t+h)-\phi_X(t)}{h}
=\lim_{h\to 0}\int \frac{1}{h}
\left(e^{iX(\omega)(t+h)}-e^{iX(\omega)t}\right)\,dP(\omega).
\]
By Theorem 9.4,
\[
\frac{1}{\lvert h\rvert}
\lvert e^{iX(\omega)(t+h)}-e^{iX(\omega)t}\rvert
\leq
\frac{1}{\lvert h\rvert}\lvert e^{iX(\omega)h}-1\rvert
\leq \lvert X(\omega)\rvert.
\]
Hence, by the limit version of the dominated convergence theorem (Theorem 7.7),
\[
\phi'_X(t)
=\int \lim_{h\to 0}\frac{1}{h}
\left(e^{iX(\omega)(t+h)}-e^{iX(\omega)t}\right)\,dP(\omega)
=\int iX(\omega)e^{iX(\omega)t}\,dP(\omega)
=\mathbb{E}[iXe^{iXt}].
\]

For $n=2$, we compute the second derivative:
\[
\lim_{h\to 0}\frac{\phi'_X(t+h)-\phi'_X(t)}{h}
=\lim_{h\to 0}\int \frac{i}{h}
\left(X(\omega)e^{iX(\omega)(t+h)}-X(\omega)e^{iX(\omega)t}\right)\,dP(\omega).
\]
For each $\omega$, the absolute value of the integrand is bounded by
\[
\left\lvert
iX(\omega)e^{iX(\omega)t}\frac{e^{iX(\omega)h}-1}{h}
\right\rvert
\leq \lvert X(\omega)\rvert^2.
\]
If $\mathbb{E}[\lvert X\rvert^2]$ is finite, dominated convergence gives
\[
\lim_{h\to 0}\frac{\phi'_X(t+h)-\phi'_X(t)}{h}
=\mathbb{E}[(iX)^2e^{iXt}].
\]
This proves the formula for $n=2$.
\hfill $\square$
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory Complex Filter
open scoped Topology Nat RealInnerProductSpace

/-- The textbook integrand `(i x)^n e^{i x t}` for the `n`-th derivative of a
characteristic function. -/
noncomputable def characteristicFunctionDerivativeIntegrand (n : ℕ) (t x : ℝ) : ℂ :=
  (Complex.I * (x : ℂ)) ^ n * Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))

private lemma real_inv_smul_eq_complex_div (h : ℝ) (z : ℂ) :
    h⁻¹ • z = z / (h : ℂ) := by
  change (((h⁻¹ : ℝ) : ℂ) * z) = z / (h : ℂ)
  rw [div_eq_mul_inv, Complex.ofReal_inv]
  exact mul_comm _ _

theorem first_difference_quotient_pointwise_limit
    (x t : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (Complex.exp (Complex.I * (x : ℂ) * (((t + h : ℝ) : ℂ))) -
            Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))) /
          (h : ℂ))
      (nhdsWithin 0 ({h : ℝ | h ≠ 0}))
      (nhds (Complex.I * (x : ℂ) *
        Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)))) := by
  have hlinear :
      HasDerivAt (fun s : ℝ => Complex.I * (x : ℂ) * (s : ℂ))
        (Complex.I * (x : ℂ)) t := by
    simpa using
      (((Complex.ofRealCLM).hasDerivAt (x := t)).const_mul
        (Complex.I * (x : ℂ)))
  have hderiv :
      HasDerivAt (fun s : ℝ =>
        Complex.exp (Complex.I * (x : ℂ) * (s : ℂ)))
        (Complex.I * (x : ℂ) *
          Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))) t := by
    have h := hlinear.cexp
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have htend := hderiv.tendsto_slope_zero
  refine Filter.Tendsto.congr' ?_ htend
  filter_upwards with h
  exact real_inv_smul_eq_complex_div h _

theorem first_difference_quotient_domination
    (x h : ℝ) (hh : h ≠ 0) :
    ‖(Complex.exp (Complex.I * (x : ℂ) * (h : ℂ)) - 1) / (h : ℂ)‖ ≤ ‖x‖ := by
  have h94 :
      ‖Complex.exp (Complex.I * (x : ℂ) * (h : ℂ)) - 1‖ ≤ |x * h| := by
    simpa [Complex.ofReal_mul, mul_assoc] using thm_9_4 (x * h)
  calc
    ‖(Complex.exp (Complex.I * (x : ℂ) * (h : ℂ)) - 1) / (h : ℂ)‖
        = ‖Complex.exp (Complex.I * (x : ℂ) * (h : ℂ)) - 1‖ / ‖(h : ℂ)‖ := by
          rw [norm_div]
    _ ≤ |x * h| / ‖(h : ℂ)‖ := by
          exact div_le_div_of_nonneg_right h94 (norm_nonneg _)
    _ = ‖x‖ := by
          rw [abs_mul]
          simp [Real.norm_eq_abs]
          field_simp [abs_ne_zero.mpr hh]

theorem second_difference_quotient_domination
    (x h t : ℝ) (hh : h ≠ 0) :
    ‖Complex.I * (x : ℂ) * Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) *
        ((Complex.exp (Complex.I * (x : ℂ) * (h : ℂ)) - 1) / (h : ℂ))‖ ≤
      ‖x ^ 2‖ := by
  have hfirst := first_difference_quotient_domination x h hh
  have hexp : ‖Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))‖ = 1 := by
    simpa [Complex.ofReal_mul, mul_assoc] using Complex.norm_exp_I_mul_ofReal (x * t)
  have hexp' : ‖Complex.exp (Complex.I * ((x : ℂ) * (t : ℂ)))‖ = 1 := by
    simpa [mul_assoc] using hexp
  have hfactor :
      ‖Complex.I * (x : ℂ) * Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))‖ = ‖x‖ := by
    rw [norm_mul, norm_mul]
    simp [hexp', Real.norm_eq_abs, mul_assoc]
  calc
    ‖Complex.I * (x : ℂ) * Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) *
        ((Complex.exp (Complex.I * (x : ℂ) * (h : ℂ)) - 1) / (h : ℂ))‖
        = ‖Complex.I * (x : ℂ) * Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))‖ *
            ‖(Complex.exp (Complex.I * (x : ℂ) * (h : ℂ)) - 1) / (h : ℂ)‖ := by
          rw [norm_mul]
    _ ≤ ‖x‖ * ‖x‖ := by
          rw [hfactor]
          exact mul_le_mul_of_nonneg_left hfirst (norm_nonneg _)
    _ = ‖x ^ 2‖ := by
          simp [pow_two, norm_mul]

theorem characteristicFunction_first_derivative_dct_bridge_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : AEMeasurable X P) (hMoment1 : Integrable X P) (t : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ∫ ω : Ω,
          Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ)) *
            ((Complex.exp (Complex.I * (X ω : ℂ) * (h : ℂ)) - 1) / (h : ℂ)) ∂P)
      (nhdsWithin 0 ({h : ℝ | h ≠ 0}))
      (nhds (∫ ω : Ω,
        Complex.I * (X ω : ℂ) *
          Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ)) ∂P)) := by
  let Xh : ℝ → Ω → ℂ := fun h ω =>
    Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ)) *
      ((Complex.exp (Complex.I * (X ω : ℂ) * (h : ℂ)) - 1) / (h : ℂ))
  let Xlim : Ω → ℂ := fun ω =>
    Complex.I * (X ω : ℂ) * Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ))
  let Y : Ω → ℝ := fun ω => ‖X ω‖
  have hXm :
      ∀ᶠ h in nhdsWithin (0 : ℝ) ({h : ℝ | h ≠ 0}),
        AEStronglyMeasurable (Xh h) P := by
    refine Eventually.of_forall ?_
    intro h
    dsimp [Xh]
    fun_prop
  have hYint : Integrable Y P := by
    dsimp [Y]
    exact hMoment1.norm
  have hbound :
      ∀ᶠ h in nhdsWithin (0 : ℝ) ({h : ℝ | h ≠ 0}),
        ∀ᵐ ω ∂P, ‖Xh h ω‖ ≤ Y ω := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    filter_upwards with ω
    dsimp [Xh, Y]
    have hfirst := first_difference_quotient_domination (X ω) h hh
    have hexp : ‖Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ))‖ = 1 := by
      simpa [Complex.ofReal_mul, mul_assoc] using Complex.norm_exp_I_mul_ofReal ((X ω) * t)
    calc
      ‖Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ)) *
          ((Complex.exp (Complex.I * (X ω : ℂ) * (h : ℂ)) - 1) / (h : ℂ))‖
          = ‖Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ))‖ *
              ‖(Complex.exp (Complex.I * (X ω : ℂ) * (h : ℂ)) - 1) / (h : ℂ)‖ := by
            rw [norm_mul]
      _ = ‖(Complex.exp (Complex.I * (X ω : ℂ) * (h : ℂ)) - 1) / (h : ℂ)‖ := by
            simp [hexp]
      _ ≤ ‖X ω‖ := hfirst
  have hlim :
      ∀ᵐ ω ∂P, Tendsto (fun h : ℝ => Xh h ω)
        (nhdsWithin (0 : ℝ) ({h : ℝ | h ≠ 0})) (nhds (Xlim ω)) := by
    filter_upwards with ω
    dsimp [Xh, Xlim]
    have hq := first_difference_quotient_pointwise_limit (X ω) 0
    have hq0 :
        Tendsto
          (fun h : ℝ =>
            (Complex.exp (Complex.I * (X ω : ℂ) * (h : ℂ)) - 1) / (h : ℂ))
          (nhdsWithin (0 : ℝ) ({h : ℝ | h ≠ 0}))
          (nhds (Complex.I * (X ω : ℂ))) := by
      simpa using hq
    have hc :
        Tendsto (fun _ : ℝ => Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ)))
          (nhdsWithin (0 : ℝ) ({h : ℝ | h ≠ 0}))
          (nhds (Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ)))) :=
      tendsto_const_nhds
    have hm := hc.mul hq0
    simpa [mul_comm, mul_left_comm, mul_assoc] using hm
  exact thm_7_DCT_filter P Xh Xlim Y (nhdsWithin (0 : ℝ) ({h : ℝ | h ≠ 0}))
    hXm hYint hbound hlim

private lemma characteristicFunction_first_slope_eq_integral_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) (t h : ℝ) :
    h⁻¹ • (characteristicFunction P X (t + h) - characteristicFunction P X t) =
      ∫ ω : Ω,
        Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ)) *
          ((Complex.exp (Complex.I * (X ω : ℂ) * (h : ℂ)) - 1) / (h : ℂ)) ∂P := by
  have hint_t :
      Integrable
        (fun ω : Ω => Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ))) P := by
    exact (integrable_const (1 : ℂ)).mono (by fun_prop)
      (by simp [Complex.norm_exp])
  have hint_th :
      Integrable
        (fun ω : Ω =>
          Complex.exp (Complex.I * (X ω : ℂ) * (((t + h : ℝ) : ℂ)))) P := by
    exact (integrable_const (1 : ℂ)).mono (by fun_prop)
      (by simp [Complex.norm_exp])
  have hsub :
      characteristicFunction P X (t + h) - characteristicFunction P X t =
        ∫ ω : Ω,
          (Complex.exp (Complex.I * (X ω : ℂ) * (((t + h : ℝ) : ℂ))) -
            Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ))) ∂P := by
    rw [characteristicFunction, characteristicFunction, ← integral_sub hint_th hint_t]
  calc
    h⁻¹ • (characteristicFunction P X (t + h) - characteristicFunction P X t)
        = (characteristicFunction P X (t + h) - characteristicFunction P X t) /
            (h : ℂ) := by
          exact real_inv_smul_eq_complex_div h _
    _ = (∫ ω : Ω,
          (Complex.exp (Complex.I * (X ω : ℂ) * (((t + h : ℝ) : ℂ))) -
            Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ))) ∂P) / (h : ℂ) := by
          rw [hsub]
    _ = ∫ ω : Ω,
          (Complex.exp (Complex.I * (X ω : ℂ) * (((t + h : ℝ) : ℂ))) -
            Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ))) / (h : ℂ) ∂P := by
          exact (integral_div (μ := P) (r := (h : ℂ))
            (f := fun ω : Ω =>
              Complex.exp (Complex.I * (X ω : ℂ) * (((t + h : ℝ) : ℂ))) -
                Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ)))).symm
    _ = ∫ ω : Ω,
          Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ)) *
            ((Complex.exp (Complex.I * (X ω : ℂ) * (h : ℂ)) - 1) / (h : ℂ)) ∂P := by
          congr with ω
          have hsplit :
              Complex.I * (X ω : ℂ) * (((t + h : ℝ) : ℂ)) =
                Complex.I * (X ω : ℂ) * (t : ℂ) +
                  Complex.I * (X ω : ℂ) * (h : ℂ) := by
            norm_num [Complex.ofReal_add]
            ring
          rw [hsplit, Complex.exp_add]
          ring

theorem characteristicFunction_hasDerivAt_one_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) (hMoment1 : Integrable X P) (t : ℝ) :
    HasDerivAt (characteristicFunction P X)
      (∫ ω : Ω,
        Complex.I * (X ω : ℂ) *
          Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ)) ∂P) t := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hdct := characteristicFunction_first_derivative_dct_bridge_source hX hMoment1 t
  refine Filter.Tendsto.congr' ?_ hdct
  filter_upwards with h
  exact (characteristicFunction_first_slope_eq_integral_source (P := P) hX t h).symm

private lemma integrable_of_integrable_sq_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P)
    (hMoment2 : Integrable (fun ω : Ω => X ω ^ 2) P) :
    Integrable X P := by
  have hsquareNorm : Integrable (fun ω : Ω => ‖X ω‖ ^ 2) P := by
    simpa [pow_two, norm_mul] using hMoment2.norm
  have hnorm : Integrable (fun ω : Ω => ‖X ω‖) P := by
    simpa using
      (integrable_norm_pow_of_le (μ := P) hX.aestronglyMeasurable
        (p := 1) (q := 2) (by norm_num) hsquareNorm)
  exact (integrable_norm_iff hX.aestronglyMeasurable).mp hnorm

private lemma characteristicFunction_derivative_integrand_integrable_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P)
    (hMoment2 : Integrable (fun ω : Ω => X ω ^ 2) P) (s : ℝ) :
    Integrable
      (fun ω : Ω =>
        Complex.I * (X ω : ℂ) *
          Complex.exp (Complex.I * (X ω : ℂ) * (s : ℂ))) P := by
  have hXint := integrable_of_integrable_sq_source (P := P) hX hMoment2
  exact hXint.mono (by fun_prop) (by
    filter_upwards with ω
    have hexp : ‖Complex.exp (Complex.I * (X ω : ℂ) * (s : ℂ))‖ = 1 := by
      simpa [Complex.ofReal_mul, mul_assoc] using
        Complex.norm_exp_I_mul_ofReal ((X ω) * s)
    have hexp' : ‖Complex.exp (Complex.I * ((X ω : ℂ) * (s : ℂ)))‖ = 1 := by
      simpa [mul_assoc] using hexp
    calc
      ‖Complex.I * (X ω : ℂ) *
          Complex.exp (Complex.I * (X ω : ℂ) * (s : ℂ))‖
          = ‖X ω‖ := by
            rw [norm_mul, norm_mul]
            simp [hexp', Real.norm_eq_abs, mul_assoc]
      _ ≤ ‖X ω‖ := le_rfl)

theorem characteristicFunction_second_derivative_dct_bridge_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : AEMeasurable X P)
    (hMoment2 : Integrable (fun ω : Ω => X ω ^ 2) P) (t : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ∫ ω : Ω,
          Complex.I * (X ω : ℂ) *
            Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ)) *
            ((Complex.exp (Complex.I * (X ω : ℂ) * (h : ℂ)) - 1) / (h : ℂ)) ∂P)
      (nhdsWithin 0 ({h : ℝ | h ≠ 0}))
      (nhds (∫ ω : Ω,
        (Complex.I * (X ω : ℂ)) ^ 2 *
          Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ)) ∂P)) := by
  let Xh : ℝ → Ω → ℂ := fun h ω =>
    Complex.I * (X ω : ℂ) *
      Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ)) *
      ((Complex.exp (Complex.I * (X ω : ℂ) * (h : ℂ)) - 1) / (h : ℂ))
  let Xlim : Ω → ℂ := fun ω =>
    (Complex.I * (X ω : ℂ)) ^ 2 *
      Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ))
  let Y : Ω → ℝ := fun ω => ‖X ω ^ 2‖
  have hXm :
      ∀ᶠ h in nhdsWithin (0 : ℝ) ({h : ℝ | h ≠ 0}),
        AEStronglyMeasurable (Xh h) P := by
    refine Eventually.of_forall ?_
    intro h
    dsimp [Xh]
    fun_prop
  have hYint : Integrable Y P := by
    dsimp [Y]
    exact hMoment2.norm
  have hbound :
      ∀ᶠ h in nhdsWithin (0 : ℝ) ({h : ℝ | h ≠ 0}),
        ∀ᵐ ω ∂P, ‖Xh h ω‖ ≤ Y ω := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    filter_upwards with ω
    dsimp [Xh, Y]
    exact second_difference_quotient_domination (X ω) h t hh
  have hlim :
      ∀ᵐ ω ∂P, Tendsto (fun h : ℝ => Xh h ω)
        (nhdsWithin (0 : ℝ) ({h : ℝ | h ≠ 0})) (nhds (Xlim ω)) := by
    filter_upwards with ω
    dsimp [Xh, Xlim]
    have hq := first_difference_quotient_pointwise_limit (X ω) 0
    have hq0 :
        Tendsto
          (fun h : ℝ =>
            (Complex.exp (Complex.I * (X ω : ℂ) * (h : ℂ)) - 1) / (h : ℂ))
          (nhdsWithin (0 : ℝ) ({h : ℝ | h ≠ 0}))
          (nhds (Complex.I * (X ω : ℂ))) := by
      simpa using hq
    have hc :
        Tendsto
          (fun _ : ℝ =>
            Complex.I * (X ω : ℂ) *
              Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ)))
          (nhdsWithin (0 : ℝ) ({h : ℝ | h ≠ 0}))
          (nhds
            (Complex.I * (X ω : ℂ) *
              Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ)))) :=
      tendsto_const_nhds
    have hm := hc.mul hq0
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hm
  exact thm_7_DCT_filter P Xh Xlim Y (nhdsWithin (0 : ℝ) ({h : ℝ | h ≠ 0}))
    hXm hYint hbound hlim

private lemma characteristicFunction_second_slope_eq_integral_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P)
    (hMoment2 : Integrable (fun ω : Ω => X ω ^ 2) P) (t h : ℝ) :
    h⁻¹ •
        ((∫ ω : Ω,
            Complex.I * (X ω : ℂ) *
              Complex.exp (Complex.I * (X ω : ℂ) * (((t + h : ℝ) : ℂ))) ∂P) -
          (∫ ω : Ω,
            Complex.I * (X ω : ℂ) *
              Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ)) ∂P)) =
      ∫ ω : Ω,
        Complex.I * (X ω : ℂ) *
          Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ)) *
          ((Complex.exp (Complex.I * (X ω : ℂ) * (h : ℂ)) - 1) / (h : ℂ)) ∂P := by
  have hint_t :=
    characteristicFunction_derivative_integrand_integrable_source
      (P := P) hX hMoment2 t
  have hint_th :=
    characteristicFunction_derivative_integrand_integrable_source
      (P := P) hX hMoment2 (t + h)
  have hsub :
      (∫ ω : Ω,
            Complex.I * (X ω : ℂ) *
              Complex.exp (Complex.I * (X ω : ℂ) * (((t + h : ℝ) : ℂ))) ∂P) -
          (∫ ω : Ω,
            Complex.I * (X ω : ℂ) *
              Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ)) ∂P) =
        ∫ ω : Ω,
          (Complex.I * (X ω : ℂ) *
              Complex.exp (Complex.I * (X ω : ℂ) * (((t + h : ℝ) : ℂ))) -
            Complex.I * (X ω : ℂ) *
              Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ))) ∂P := by
    rw [← integral_sub hint_th hint_t]
  calc
    h⁻¹ •
        ((∫ ω : Ω,
            Complex.I * (X ω : ℂ) *
              Complex.exp (Complex.I * (X ω : ℂ) * (((t + h : ℝ) : ℂ))) ∂P) -
          (∫ ω : Ω,
            Complex.I * (X ω : ℂ) *
              Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ)) ∂P))
        = (((∫ ω : Ω,
            Complex.I * (X ω : ℂ) *
              Complex.exp (Complex.I * (X ω : ℂ) * (((t + h : ℝ) : ℂ))) ∂P) -
          (∫ ω : Ω,
            Complex.I * (X ω : ℂ) *
              Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ)) ∂P)) / (h : ℂ)) := by
          exact real_inv_smul_eq_complex_div h _
    _ = (∫ ω : Ω,
          (Complex.I * (X ω : ℂ) *
              Complex.exp (Complex.I * (X ω : ℂ) * (((t + h : ℝ) : ℂ))) -
            Complex.I * (X ω : ℂ) *
              Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ))) ∂P) / (h : ℂ) := by
          rw [hsub]
    _ = ∫ ω : Ω,
          (Complex.I * (X ω : ℂ) *
              Complex.exp (Complex.I * (X ω : ℂ) * (((t + h : ℝ) : ℂ))) -
            Complex.I * (X ω : ℂ) *
              Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ))) / (h : ℂ) ∂P := by
          exact (integral_div (μ := P) (r := (h : ℂ))
            (f := fun ω : Ω =>
              Complex.I * (X ω : ℂ) *
                  Complex.exp (Complex.I * (X ω : ℂ) * (((t + h : ℝ) : ℂ))) -
                Complex.I * (X ω : ℂ) *
                  Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ)))).symm
    _ = ∫ ω : Ω,
          Complex.I * (X ω : ℂ) *
            Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ)) *
            ((Complex.exp (Complex.I * (X ω : ℂ) * (h : ℂ)) - 1) / (h : ℂ)) ∂P := by
          congr with ω
          have hsplit :
              Complex.I * (X ω : ℂ) * (((t + h : ℝ) : ℂ)) =
                Complex.I * (X ω : ℂ) * (t : ℂ) +
                  Complex.I * (X ω : ℂ) * (h : ℂ) := by
            norm_num [Complex.ofReal_add]
            ring
          rw [hsplit, Complex.exp_add]
          ring

theorem characteristicFunction_hasDerivAt_two_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P)
    (hMoment2 : Integrable (fun ω : Ω => X ω ^ 2) P) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ =>
        ∫ ω : Ω,
          Complex.I * (X ω : ℂ) *
            Complex.exp (Complex.I * (X ω : ℂ) * (s : ℂ)) ∂P)
      (∫ ω : Ω,
        (Complex.I * (X ω : ℂ)) ^ 2 *
          Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ)) ∂P) t := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hdct := characteristicFunction_second_derivative_dct_bridge_source hX hMoment2 t
  refine Filter.Tendsto.congr' ?_ hdct
  filter_upwards with h
  exact (characteristicFunction_second_slope_eq_integral_source
    (P := P) hX hMoment2 t h).symm

theorem characteristicFunction_iteratedDeriv_one_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) (hMoment1 : Integrable X P) (t : ℝ) :
    iteratedDeriv 1 (characteristicFunction P X) t =
      ∫ ω : Ω, characteristicFunctionDerivativeIntegrand 1 t (X ω) ∂P := by
  rw [iteratedDeriv_one]
  rw [(characteristicFunction_hasDerivAt_one_source hX hMoment1 t).deriv]
  congr with ω
  simp [characteristicFunctionDerivativeIntegrand]

theorem characteristicFunction_iteratedDeriv_two_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P)
    (hMoment2 : Integrable (fun ω : Ω => X ω ^ 2) P) (t : ℝ) :
    iteratedDeriv 2 (characteristicFunction P X) t =
      ∫ ω : Ω, characteristicFunctionDerivativeIntegrand 2 t (X ω) ∂P := by
  have hMoment1 := integrable_of_integrable_sq_source (P := P) hX hMoment2
  have hderiv_eq :
      deriv (characteristicFunction P X) =
        fun s : ℝ =>
          ∫ ω : Ω,
            Complex.I * (X ω : ℂ) *
              Complex.exp (Complex.I * (X ω : ℂ) * (s : ℂ)) ∂P := by
    funext s
    exact (characteristicFunction_hasDerivAt_one_source hX hMoment1 s).deriv
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one,
    hderiv_eq]
  rw [(characteristicFunction_hasDerivAt_two_source hX hMoment2 t).deriv]
  congr with ω

theorem moment_from_derivative_zero_source
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {n : ℕ} {D : ℂ}
    (hD : D = ∫ ω : Ω, (Complex.I * (X ω : ℂ)) ^ n ∂μ) :
    ((∫ ω : Ω, X ω ^ n ∂μ : ℝ) : ℂ) =
      (Complex.I ^ n)⁻¹ * D := by
  rw [hD]
  have hInt :
      (∫ ω : Ω, (Complex.I * (X ω : ℂ)) ^ n ∂μ) =
        Complex.I ^ n * ∫ ω : Ω, ((X ω ^ n : ℝ) : ℂ) ∂μ := by
    calc
      (∫ ω : Ω, (Complex.I * (X ω : ℂ)) ^ n ∂μ)
          = ∫ ω : Ω, Complex.I ^ n * ((X ω ^ n : ℝ) : ℂ) ∂μ := by
            congr with ω
            simp [mul_pow]
      _ = Complex.I ^ n * ∫ ω : Ω, ((X ω ^ n : ℝ) : ℂ) ∂μ := by
            exact MeasureTheory.integral_const_mul (Complex.I ^ n)
              (fun ω : Ω => ((X ω ^ n : ℝ) : ℂ))
  rw [hInt]
  rw [integral_complex_ofReal]
  field_simp [pow_ne_zero n Complex.I_ne_zero]

theorem characteristicFunction_moment_from_derivative_zero_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {n : ℕ}
    (hDeriv0 :
      iteratedDeriv n (characteristicFunction P X) 0 =
        ∫ ω : Ω, (Complex.I * (X ω : ℂ)) ^ n ∂P) :
    ((∫ ω : Ω, X ω ^ n ∂P : ℝ) : ℂ) =
      (Complex.I ^ n)⁻¹ * iteratedDeriv n (characteristicFunction P X) 0 :=
  moment_from_derivative_zero_source (μ := P) (X := X) hDeriv0

theorem characteristicFunction_moment_from_derivative_one_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) (hMoment1 : Integrable X P) :
    ((∫ ω : Ω, X ω ^ 1 ∂P : ℝ) : ℂ) =
      (Complex.I ^ 1)⁻¹ * iteratedDeriv 1 (characteristicFunction P X) 0 := by
  have hDeriv0 :
      iteratedDeriv 1 (characteristicFunction P X) 0 =
        ∫ ω : Ω, (Complex.I * (X ω : ℂ)) ^ 1 ∂P := by
    have h := characteristicFunction_iteratedDeriv_one_source hX hMoment1 0
    simpa [characteristicFunctionDerivativeIntegrand] using h
  exact characteristicFunction_moment_from_derivative_zero_source hDeriv0

theorem characteristicFunction_moment_from_derivative_two_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P)
    (hMoment2 : Integrable (fun ω : Ω => X ω ^ 2) P) :
    ((∫ ω : Ω, X ω ^ 2 ∂P : ℝ) : ℂ) =
      (Complex.I ^ 2)⁻¹ * iteratedDeriv 2 (characteristicFunction P X) 0 := by
  have hDeriv0 :
      iteratedDeriv 2 (characteristicFunction P X) 0 =
        ∫ ω : Ω, (Complex.I * (X ω : ℂ)) ^ 2 ∂P := by
    have h := characteristicFunction_iteratedDeriv_two_source hX hMoment2 0
    simpa [characteristicFunctionDerivativeIntegrand] using h
  exact characteristicFunction_moment_from_derivative_zero_source hDeriv0

private lemma characteristicFunctionDerivativeIntegrand_norm
    (k : ℕ) (t x : ℝ) :
    ‖characteristicFunctionDerivativeIntegrand k t x‖ = ‖x‖ ^ k := by
  have hexp : ‖Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))‖ = 1 := by
    simpa [Complex.ofReal_mul, mul_assoc] using Complex.norm_exp_I_mul_ofReal (x * t)
  have hxnorm : ‖Complex.I * (x : ℂ)‖ = ‖x‖ := by
    simp [Real.norm_eq_abs]
  calc
    ‖characteristicFunctionDerivativeIntegrand k t x‖
        = ‖(Complex.I * (x : ℂ)) ^ k‖ *
            ‖Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))‖ := by
          rw [characteristicFunctionDerivativeIntegrand, norm_mul]
    _ = ‖Complex.I * (x : ℂ)‖ ^ k := by
          simp [norm_pow, hexp]
    _ = ‖x‖ ^ k := by
          rw [hxnorm]

private lemma derivative_integrand_step_domination_source
    (k : ℕ) (x h t : ℝ) (hh : h ≠ 0) :
    ‖characteristicFunctionDerivativeIntegrand k t x *
        ((Complex.exp (Complex.I * (x : ℂ) * (h : ℂ)) - 1) / (h : ℂ))‖ ≤
      ‖x‖ ^ (k + 1) := by
  have hfirst := first_difference_quotient_domination x h hh
  calc
    ‖characteristicFunctionDerivativeIntegrand k t x *
        ((Complex.exp (Complex.I * (x : ℂ) * (h : ℂ)) - 1) / (h : ℂ))‖
        = ‖x‖ ^ k *
            ‖(Complex.exp (Complex.I * (x : ℂ) * (h : ℂ)) - 1) / (h : ℂ)‖ := by
          rw [norm_mul, characteristicFunctionDerivativeIntegrand_norm]
    _ ≤ ‖x‖ ^ k * ‖x‖ := by
          exact mul_le_mul_of_nonneg_left hfirst (pow_nonneg (norm_nonneg _) k)
    _ = ‖x‖ ^ (k + 1) := by
          rw [pow_succ]

private lemma derivative_integrand_step_pointwise_limit_source
    (k : ℕ) (x t : ℝ) :
    Tendsto
      (fun h : ℝ =>
        characteristicFunctionDerivativeIntegrand k t x *
          ((Complex.exp (Complex.I * (x : ℂ) * (h : ℂ)) - 1) / (h : ℂ)))
      (nhdsWithin 0 ({h : ℝ | h ≠ 0}))
      (nhds (characteristicFunctionDerivativeIntegrand (k + 1) t x)) := by
  have hq := first_difference_quotient_pointwise_limit x 0
  have hq0 :
      Tendsto
        (fun h : ℝ =>
          (Complex.exp (Complex.I * (x : ℂ) * (h : ℂ)) - 1) / (h : ℂ))
        (nhdsWithin (0 : ℝ) ({h : ℝ | h ≠ 0}))
        (nhds (Complex.I * (x : ℂ))) := by
    simpa using hq
  have hc :
      Tendsto (fun _ : ℝ => characteristicFunctionDerivativeIntegrand k t x)
        (nhdsWithin (0 : ℝ) ({h : ℝ | h ≠ 0}))
        (nhds (characteristicFunctionDerivativeIntegrand k t x)) :=
    tendsto_const_nhds
  have hm := hc.mul hq0
  simpa [characteristicFunctionDerivativeIntegrand, pow_succ, mul_comm, mul_left_comm,
    mul_assoc] using hm

private lemma integrable_norm_pow_of_memLp_map_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P)
    {k : ℕ} (hMoment : MemLp id k (P.map X)) :
    Integrable (fun ω : Ω => ‖X ω‖ ^ k) P := by
  have hMap : Integrable (fun x : ℝ => ‖x‖ ^ k) (P.map X) := by
    simpa using hMoment.integrable_norm_pow'
  simpa [Function.comp_def] using
    (integrable_map_measure (μ := P) (f := X) (g := fun x : ℝ => ‖x‖ ^ k)
      (by fun_prop) hX).mp hMap

private lemma characteristicFunction_derivative_integrand_integrable_high_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : AEMeasurable X P) (k : ℕ)
    (hMomentK : Integrable (fun ω : Ω => ‖X ω‖ ^ k) P) (s : ℝ) :
    Integrable
      (fun ω : Ω => characteristicFunctionDerivativeIntegrand k s (X ω)) P := by
  refine hMomentK.mono ?_ ?_
  · unfold characteristicFunctionDerivativeIntegrand
    fun_prop
  · filter_upwards with ω
    rw [characteristicFunctionDerivativeIntegrand_norm]
    simp [Real.norm_eq_abs]

theorem characteristicFunction_derivative_dct_bridge_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : AEMeasurable X P) (k : ℕ)
    (hMomentSucc : Integrable (fun ω : Ω => ‖X ω‖ ^ (k + 1)) P) (t : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ∫ ω : Ω,
          characteristicFunctionDerivativeIntegrand k t (X ω) *
            ((Complex.exp (Complex.I * (X ω : ℂ) * (h : ℂ)) - 1) / (h : ℂ)) ∂P)
      (nhdsWithin 0 ({h : ℝ | h ≠ 0}))
      (nhds (∫ ω : Ω,
        characteristicFunctionDerivativeIntegrand (k + 1) t (X ω) ∂P)) := by
  let Xh : ℝ → Ω → ℂ := fun h ω =>
    characteristicFunctionDerivativeIntegrand k t (X ω) *
      ((Complex.exp (Complex.I * (X ω : ℂ) * (h : ℂ)) - 1) / (h : ℂ))
  let Xlim : Ω → ℂ := fun ω =>
    characteristicFunctionDerivativeIntegrand (k + 1) t (X ω)
  let Y : Ω → ℝ := fun ω => ‖X ω‖ ^ (k + 1)
  have hXm :
      ∀ᶠ h in nhdsWithin (0 : ℝ) ({h : ℝ | h ≠ 0}),
        AEStronglyMeasurable (Xh h) P := by
    refine Eventually.of_forall ?_
    intro h
    dsimp [Xh]
    unfold characteristicFunctionDerivativeIntegrand
    fun_prop
  have hYint : Integrable Y P := by
    dsimp [Y]
    exact hMomentSucc
  have hbound :
      ∀ᶠ h in nhdsWithin (0 : ℝ) ({h : ℝ | h ≠ 0}),
        ∀ᵐ ω ∂P, ‖Xh h ω‖ ≤ Y ω := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    filter_upwards with ω
    dsimp [Xh, Y]
    exact derivative_integrand_step_domination_source k (X ω) h t hh
  have hlim :
      ∀ᵐ ω ∂P, Tendsto (fun h : ℝ => Xh h ω)
        (nhdsWithin (0 : ℝ) ({h : ℝ | h ≠ 0})) (nhds (Xlim ω)) := by
    filter_upwards with ω
    dsimp [Xh, Xlim]
    exact derivative_integrand_step_pointwise_limit_source k (X ω) t
  exact thm_7_DCT_filter P Xh Xlim Y (nhdsWithin (0 : ℝ) ({h : ℝ | h ≠ 0}))
    hXm hYint hbound hlim

private lemma characteristicFunction_integral_slope_eq_integral_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) (k : ℕ)
    (hMomentK : Integrable (fun ω : Ω => ‖X ω‖ ^ k) P) (t h : ℝ) :
    h⁻¹ •
        ((∫ ω : Ω,
            characteristicFunctionDerivativeIntegrand k (t + h) (X ω) ∂P) -
          (∫ ω : Ω,
            characteristicFunctionDerivativeIntegrand k t (X ω) ∂P)) =
      ∫ ω : Ω,
        characteristicFunctionDerivativeIntegrand k t (X ω) *
          ((Complex.exp (Complex.I * (X ω : ℂ) * (h : ℂ)) - 1) / (h : ℂ)) ∂P := by
  have hint_t :=
    characteristicFunction_derivative_integrand_integrable_high_source
      (P := P) hX k hMomentK t
  have hint_th :=
    characteristicFunction_derivative_integrand_integrable_high_source
      (P := P) hX k hMomentK (t + h)
  have hsub :
      (∫ ω : Ω,
            characteristicFunctionDerivativeIntegrand k (t + h) (X ω) ∂P) -
          (∫ ω : Ω,
            characteristicFunctionDerivativeIntegrand k t (X ω) ∂P) =
        ∫ ω : Ω,
          (characteristicFunctionDerivativeIntegrand k (t + h) (X ω) -
            characteristicFunctionDerivativeIntegrand k t (X ω)) ∂P := by
    rw [← integral_sub hint_th hint_t]
  calc
    h⁻¹ •
        ((∫ ω : Ω,
            characteristicFunctionDerivativeIntegrand k (t + h) (X ω) ∂P) -
          (∫ ω : Ω,
            characteristicFunctionDerivativeIntegrand k t (X ω) ∂P))
        = (((∫ ω : Ω,
            characteristicFunctionDerivativeIntegrand k (t + h) (X ω) ∂P) -
          (∫ ω : Ω,
            characteristicFunctionDerivativeIntegrand k t (X ω) ∂P)) / (h : ℂ)) := by
          exact real_inv_smul_eq_complex_div h _
    _ = (∫ ω : Ω,
          (characteristicFunctionDerivativeIntegrand k (t + h) (X ω) -
            characteristicFunctionDerivativeIntegrand k t (X ω)) ∂P) / (h : ℂ) := by
          rw [hsub]
    _ = ∫ ω : Ω,
          (characteristicFunctionDerivativeIntegrand k (t + h) (X ω) -
            characteristicFunctionDerivativeIntegrand k t (X ω)) / (h : ℂ) ∂P := by
          exact (integral_div (μ := P) (r := (h : ℂ))
            (f := fun ω : Ω =>
              characteristicFunctionDerivativeIntegrand k (t + h) (X ω) -
                characteristicFunctionDerivativeIntegrand k t (X ω))).symm
    _ = ∫ ω : Ω,
          characteristicFunctionDerivativeIntegrand k t (X ω) *
            ((Complex.exp (Complex.I * (X ω : ℂ) * (h : ℂ)) - 1) / (h : ℂ)) ∂P := by
          congr with ω
          unfold characteristicFunctionDerivativeIntegrand
          have hsplit :
              Complex.I * (X ω : ℂ) * (((t + h : ℝ) : ℂ)) =
                Complex.I * (X ω : ℂ) * (t : ℂ) +
                  Complex.I * (X ω : ℂ) * (h : ℂ) := by
            norm_num [Complex.ofReal_add]
            ring
          rw [hsplit, Complex.exp_add]
          ring

theorem characteristicFunction_integral_hasDerivAt_succ_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) (k : ℕ)
    (hMomentK : Integrable (fun ω : Ω => ‖X ω‖ ^ k) P)
    (hMomentSucc : Integrable (fun ω : Ω => ‖X ω‖ ^ (k + 1)) P) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ =>
        ∫ ω : Ω, characteristicFunctionDerivativeIntegrand k s (X ω) ∂P)
      (∫ ω : Ω, characteristicFunctionDerivativeIntegrand (k + 1) t (X ω) ∂P) t := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hdct := characteristicFunction_derivative_dct_bridge_source hX k hMomentSucc t
  refine Filter.Tendsto.congr' ?_ hdct
  filter_upwards with h
  exact (characteristicFunction_integral_slope_eq_integral_source
    (P := P) hX k hMomentK t h).symm

theorem characteristicFunction_iteratedDeriv_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P)
    {n : ℕ} (hMoment : MemLp id n (P.map X)) :
    ∀ t : ℝ,
      iteratedDeriv n (characteristicFunction P X) t =
        ∫ ω : Ω, characteristicFunctionDerivativeIntegrand n t (X ω) ∂P := by
  induction n with
  | zero =>
      intro t
      simp [iteratedDeriv_zero, characteristicFunction, characteristicFunctionDerivativeIntegrand]
  | succ k ih =>
      have hMomentK : MemLp id k (P.map X) := hMoment.mono_exponent (by simp)
      have hPowK := integrable_norm_pow_of_memLp_map_source hX hMomentK
      have hPowSucc := integrable_norm_pow_of_memLp_map_source hX hMoment
      have hEqFun :
          iteratedDeriv k (characteristicFunction P X) =
            fun s : ℝ =>
              ∫ ω : Ω, characteristicFunctionDerivativeIntegrand k s (X ω) ∂P := by
        funext s
        exact ih hMomentK s
      intro t
      rw [iteratedDeriv_succ, hEqFun]
      exact (characteristicFunction_integral_hasDerivAt_succ_source
        hX k hPowK hPowSucc t).deriv

theorem characteristicFunction_moment_from_derivative_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P)
    {n : ℕ} (hMoment : MemLp id n (P.map X)) :
    ((∫ ω : Ω, X ω ^ n ∂P : ℝ) : ℂ) =
      (Complex.I ^ n)⁻¹ * iteratedDeriv n (characteristicFunction P X) 0 := by
  have hDeriv0 :
      iteratedDeriv n (characteristicFunction P X) 0 =
        ∫ ω : Ω, (Complex.I * (X ω : ℂ)) ^ n ∂P := by
    have h := characteristicFunction_iteratedDeriv_source hX hMoment 0
    simpa [characteristicFunctionDerivativeIntegrand] using h
  exact characteristicFunction_moment_from_derivative_zero_source hDeriv0

theorem characteristicFunction_eq_charFun_map
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (hX : AEMeasurable X μ) (t : ℝ) :
    characteristicFunction μ X t = charFun (μ.map X) t := by
  rw [charFun_apply_real]
  rw [integral_map hX.aestronglyMeasurable.aemeasurable (by fun_prop)]
  simp [characteristicFunction, mul_comm, mul_left_comm]

/-- Compatibility export used by downstream law-level characteristic-function
tasks. The final random-variable theorem below does not depend on this bridge. -/
theorem characteristicFunction_iteratedDeriv_law
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {n : ℕ} (hμ : MemLp id n μ) (t : ℝ) :
    iteratedDeriv n (charFun μ) t =
      ∫ x : ℝ, characteristicFunctionDerivativeIntegrand n t x ∂μ := by
  rw [iteratedDeriv_charFun (μ := μ) (n := n) (t := t) hμ]
  calc
    I ^ n * ∫ x : ℝ, (x : ℂ) ^ n * Complex.exp ((t : ℂ) * (x : ℂ) * I) ∂μ
        = ∫ x : ℝ,
            I ^ n * ((x : ℂ) ^ n * Complex.exp ((t : ℂ) * (x : ℂ) * I)) ∂μ := by
          exact (integral_const_mul (μ := μ) (I ^ n)
            (fun x : ℝ => (x : ℂ) ^ n * Complex.exp ((t : ℂ) * (x : ℂ) * I))).symm
    _ = ∫ x : ℝ, characteristicFunctionDerivativeIntegrand n t x ∂μ := by
          congr with x
          simp [characteristicFunctionDerivativeIntegrand]
          ring_nf

theorem characteristicFunction_iteratedDeriv_randomVariable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P)
    {n : ℕ} (hMoment : MemLp id n (P.map X)) (t : ℝ) :
    iteratedDeriv n (characteristicFunction P X) t =
      ∫ ω : Ω, characteristicFunctionDerivativeIntegrand n t (X ω) ∂P :=
  characteristicFunction_iteratedDeriv_source hX hMoment t

/-- Compatibility export for law-level moment recovery. -/
theorem characteristicFunction_moment_from_derivative_law
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {n : ℕ} (hμ : MemLp id n μ) :
    ((∫ x : ℝ, x ^ n ∂μ : ℝ) : ℂ) =
      (Complex.I ^ n)⁻¹ * iteratedDeriv n (charFun μ) 0 := by
  have hDeriv0 :
      iteratedDeriv n (charFun μ) 0 =
        ∫ x : ℝ, (Complex.I * (x : ℂ)) ^ n ∂μ := by
    have h := characteristicFunction_iteratedDeriv_law (μ := μ) hμ 0
    simpa [characteristicFunctionDerivativeIntegrand] using h
  simpa using
    (moment_from_derivative_zero_source (μ := μ) (X := fun x : ℝ => x) hDeriv0)

theorem characteristicFunction_moment_from_derivative_randomVariable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P)
    {n : ℕ} (hMoment : MemLp id n (P.map X)) :
    ((∫ ω : Ω, X ω ^ n ∂P : ℝ) : ℂ) =
      (Complex.I ^ n)⁻¹ * iteratedDeriv n (characteristicFunction P X) 0 :=
  characteristicFunction_moment_from_derivative_source hX hMoment

theorem thm_9_7
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P)
    {n : ℕ} (hMoment : MemLp id n (P.map X)) :
    (∀ t : ℝ,
        iteratedDeriv n (characteristicFunction P X) t =
          ∫ ω : Ω, characteristicFunctionDerivativeIntegrand n t (X ω) ∂P) ∧
      ((∫ ω : Ω, X ω ^ n ∂P : ℝ) : ℂ) =
        (Complex.I ^ n)⁻¹ * iteratedDeriv n (characteristicFunction P X) 0 := by
  exact ⟨characteristicFunction_iteratedDeriv_source hX hMoment,
    characteristicFunction_moment_from_derivative_source hX hMoment⟩
