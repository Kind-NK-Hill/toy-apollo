import Mathlib
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import ToyApollo.Output.def_9_3
import ToyApollo.Output.thm_8_5
import ToyApollo.Output.thm_9_4

open Filter MeasureTheory Set
open scoped Topology Interval

noncomputable section

/-- The removable-singularity multiplier
`(e^{-ita} - e^{-itb}) / (i t)` appearing in the inversion formula. -/
noncomputable def characteristicInversionMultiplier (a b t : ℝ) : ℂ :=
  if t = 0 then (b - a : ℂ)
  else
    (Complex.exp (-(Complex.I * (t : ℂ) * (a : ℂ))) -
        Complex.exp (-(Complex.I * (t : ℂ) * (b : ℂ)))) /
      (Complex.I * (t : ℂ))

/-- Away from the removable singularity, multiplying by `e^{itx}` turns the
source multiplier into the expected translated exponential difference. This is
the first local algebraic step of the kernel change-of-variables obligation. -/
theorem characteristicInversionMultiplier_mul_exp_eq_of_ne
    (a b x t : ℝ) (ht : t ≠ 0) :
    characteristicInversionMultiplier a b t *
        Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) =
      (Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (a : ℂ))) -
          Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (b : ℂ)))) /
        (Complex.I * (t : ℂ)) := by
  have hden : Complex.I * (t : ℂ) ≠ 0 := by
    exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast ht)
  simp [characteristicInversionMultiplier, ht]
  let E := Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))
  let A := Complex.exp (-(Complex.I * (t : ℂ) * (a : ℂ)))
  let B := Complex.exp (-(Complex.I * (t : ℂ) * (b : ℂ)))
  have hA : A * E = Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (a : ℂ))) := by
    dsimp [A, E]
    rw [← Complex.exp_add]
    congr 1
    ring
  have hB : B * E = Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (b : ℂ))) := by
    dsimp [B, E]
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    ((A - B) / (Complex.I * (t : ℂ))) * E
        = (A * E - B * E) / (Complex.I * (t : ℂ)) := by
            field_simp [hden]
    _ = (Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (a : ℂ))) -
          Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (b : ℂ)))) /
        (Complex.I * (t : ℂ)) := by
            simpa [hA, hB]

/-- Euler expansion of the translated exponential factor used in the local
kernel algebra. -/
theorem characteristicInversionTranslatedExp_eq_cos_add_sin_I
    (a x t : ℝ) :
    Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (a : ℂ))) =
      (Real.cos (t * (x - a)) : ℂ) +
        (Real.sin (t * (x - a)) : ℂ) * Complex.I := by
  have harg :
      Complex.I * (t : ℂ) * ((x : ℂ) - (a : ℂ)) =
        ((t * (x - a) : ℝ) : ℂ) * Complex.I := by
    norm_num [Complex.ofReal_sub, Complex.ofReal_mul]
    ring
  rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- Away from `t = 0`, the translated exponential quotient separates into the
real sine contribution and a pure-imaginary cosine difference. The latter is
the odd term that must disappear after integration over `[-T,T]`. -/
theorem characteristicInversionTranslatedExpDifference_div_I_mul
    (a b x t : ℝ) (ht : t ≠ 0) :
    (Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (a : ℂ))) -
        Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (b : ℂ)))) /
      (Complex.I * (t : ℂ)) =
    (((Real.sin (t * (x - a)) - Real.sin (t * (x - b))) / t : ℝ) : ℂ) -
      Complex.I *
        (((Real.cos (t * (x - a)) - Real.cos (t * (x - b))) / t : ℝ) : ℂ) := by
  have htC : (t : ℂ) ≠ 0 := by
    exact_mod_cast ht
  have hden : Complex.I * (t : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero htC
  rw [characteristicInversionTranslatedExp_eq_cos_add_sin_I,
    characteristicInversionTranslatedExp_eq_cos_add_sin_I]
  apply Complex.ext
  · simp [div_eq_mul_inv, ht, mul_comm, mul_left_comm]
    field_simp [ht]
    ring
  · simp [div_eq_mul_inv, ht, mul_comm, mul_left_comm]
    field_simp [ht]
    ring

/-- A reusable symmetric-interval fact: a complex-valued odd function has zero
oriented interval integral over `[-T,T]`. -/
theorem intervalIntegral_odd_eq_zero_complex
    (f : ℝ → ℂ) (T : ℝ) (hodd : ∀ t : ℝ, f (-t) = -f t) :
    (∫ t in (-T)..T, f t) = 0 := by
  let I : ℂ := ∫ t in (-T)..T, f t
  have hcomp : (∫ t in (-T)..T, f (-t)) = I := by
    simpa [I] using
      (intervalIntegral.integral_comp_neg (f := f) (a := (-T)) (b := T))
  have hneg : (∫ t in (-T)..T, f (-t)) = -I := by
    calc
      (∫ t in (-T)..T, f (-t)) = ∫ t in (-T)..T, (-f t) := by
          refine intervalIntegral.integral_congr_ae ?_
          filter_upwards with t
          exact fun _ => hodd t
      _ = -I := by
          simp [I]
  have hI : I = -I := hcomp.symm.trans hneg
  have hsum : I + I = 0 := by
    nth_rewrite 2 [hI]
    simp
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hmul : (2 : ℂ) * I = 0 := by
    simpa [two_mul] using hsum
  exact (mul_eq_zero.mp hmul).resolve_left htwo

/-- The pure-imaginary cosine term left by the nonzero pointwise algebra. It is
kept separate because the source proof removes it by oddness over `[-T,T]`. -/
noncomputable def characteristicInversionCosineOddTerm
    (a b x t : ℝ) : ℂ :=
  -Complex.I *
    (((Real.cos (t * (x - a)) - Real.cos (t * (x - b))) / t : ℝ) : ℂ)

theorem characteristicInversionCosineOddTerm_odd
    (a b x : ℝ) :
    ∀ t : ℝ,
      characteristicInversionCosineOddTerm a b x (-t) =
        -characteristicInversionCosineOddTerm a b x t := by
  intro t
  by_cases ht : t = 0
  · subst t
    simp [characteristicInversionCosineOddTerm]
  · have hneg : -t ≠ 0 := neg_ne_zero.mpr ht
    simp [characteristicInversionCosineOddTerm, Real.cos_neg, mul_comm]
    ring

/-- The odd cosine term contributes zero to the symmetric inner kernel
integral. This discharges the parity half of the source change-of-variables
step; the remaining work is the real sine-term affine substitution. -/
theorem characteristicInversionCosineOddTerm_integral_eq_zero
    (a b x T : ℝ) :
    (∫ t in (-T)..T, characteristicInversionCosineOddTerm a b x t) = 0 :=
  intervalIntegral_odd_eq_zero_complex
    (fun t : ℝ => characteristicInversionCosineOddTerm a b x t)
    T
    (characteristicInversionCosineOddTerm_odd a b x)

/-- The finite-`T` Cauchy principal-value truncation from the source proof. -/
noncomputable def characteristicInversionTruncation
    (μ : Measure ℝ) (a b T : ℝ) : ℂ :=
  ∫ t in (-T)..T, characteristicInversionMultiplier a b t * charFun μ t

/-- The endpoint-corrected mass on the left side of Theorem 9.5. -/
noncomputable def characteristicInversionMass
    (μ : Measure ℝ) (a b : ℝ) : ℂ :=
  (μ.real (Ioo a b) : ℂ) + (μ.real ({a} : Set ℝ) : ℂ) / 2 +
    (μ.real ({b} : Set ℝ) : ℂ) / 2

/-- The inner kernel obtained after applying the Fubini step in the source proof. -/
noncomputable def characteristicInversionInnerKernel
    (a b x T : ℝ) : ℂ :=
  ∫ t in (-T)..T,
    characteristicInversionMultiplier a b t *
      Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))

/-- The pointwise limit of the inner sine kernel, including endpoint half masses. -/
noncomputable def characteristicInversionKernelLimitValue
    (a b x : ℝ) : ℂ :=
  if a < x ∧ x < b then (2 * Real.pi : ℂ)
  else if x = a ∨ x = b then (Real.pi : ℂ)
  else 0

/-- The finite-`T` Fubini swap required by equation (9.1) of the source proof. -/
def characteristicInversionFubiniSwap
    (μ : Measure ℝ) (a b T : ℝ) : Prop :=
  characteristicInversionTruncation μ a b T =
    ∫ x, characteristicInversionInnerKernel a b x T ∂μ

/-- Product-space integrand used by the finite-`T` Fubini step. -/
noncomputable def characteristicInversionFubiniIntegrand
    (a b : ℝ) (p : ℝ × ℝ) : ℂ :=
  characteristicInversionMultiplier a b p.1 *
    Complex.exp (Complex.I * (p.1 : ℂ) * (p.2 : ℂ))

/-- The translated quotient is uniformly bounded by the interval length. This
is the Theorem 9.4 estimate used in the textbook before Fubini. -/
theorem characteristicInversionTranslatedQuotient_norm_le
    (a b x t : ℝ) (hab : a ≤ b) :
    ‖(Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (a : ℂ))) -
          Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (b : ℂ)))) /
        (Complex.I * (t : ℂ))‖ ≤ b - a := by
  by_cases ht : t = 0
  · subst t
    simp [hab]
  · have hnum_factor :
        Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (a : ℂ))) -
            Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (b : ℂ))) =
          Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (b : ℂ))) *
            (Complex.exp (Complex.I * ((t * (b - a) : ℝ) : ℂ)) - 1) := by
      have harg :
          Complex.I * (t : ℂ) * ((x : ℂ) - (a : ℂ)) =
            Complex.I * (t : ℂ) * ((x : ℂ) - (b : ℂ)) +
              Complex.I * ((t * (b - a) : ℝ) : ℂ) := by
        norm_num [Complex.ofReal_sub, Complex.ofReal_mul]
        ring
      rw [harg, Complex.exp_add]
      ring
    have h_exp_norm :
        ‖Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (b : ℂ)))‖ = 1 := by
      have harg :
          Complex.I * (t : ℂ) * ((x : ℂ) - (b : ℂ)) =
            ((t * (x - b) : ℝ) : ℂ) * Complex.I := by
        norm_num [Complex.ofReal_sub, Complex.ofReal_mul]
        ring
      rw [harg]
      exact Complex.norm_exp_ofReal_mul_I (t * (x - b))
    have hden_norm : ‖Complex.I * (t : ℂ)‖ = |t| := by
      simp
    have hnum_bound :
        ‖Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (a : ℂ))) -
            Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (b : ℂ)))‖ ≤
          |t * (b - a)| := by
      rw [hnum_factor, norm_mul, h_exp_norm, one_mul]
      exact thm_9_4 (t * (b - a))
    calc
      ‖(Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (a : ℂ))) -
          Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (b : ℂ)))) /
        (Complex.I * (t : ℂ))‖
          = ‖Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (a : ℂ))) -
              Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (b : ℂ)))‖ /
              |t| := by
              rw [norm_div, hden_norm]
      _ ≤ |t * (b - a)| / |t| := by
              exact div_le_div_of_nonneg_right hnum_bound (abs_nonneg t)
      _ = b - a := by
              rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hab)]
              field_simp [abs_ne_zero.mpr ht]

theorem characteristicInversionFubiniIntegrand_norm_le
    (a b : ℝ) (hab : a ≤ b) (p : ℝ × ℝ) :
    ‖characteristicInversionFubiniIntegrand a b p‖ ≤ b - a := by
  by_cases ht : p.1 = 0
  · have hnorm : ‖((b : ℂ) - (a : ℂ))‖ ≤ b - a := by
      have h : ((b : ℂ) - (a : ℂ)) = ((b - a : ℝ) : ℂ) := by
        norm_num
      calc
        ‖((b : ℂ) - (a : ℂ))‖ = ‖((b - a : ℝ) : ℂ)‖ := by
          rw [h]
        _ = |b - a| := by
          simpa using (RCLike.norm_ofReal (K := ℂ) (b - a))
        _ ≤ b - a := by
          rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    simpa [characteristicInversionFubiniIntegrand,
      characteristicInversionMultiplier, ht] using hnorm
  · rw [characteristicInversionFubiniIntegrand,
      characteristicInversionMultiplier_mul_exp_eq_of_ne a b p.2 p.1 ht]
    exact characteristicInversionTranslatedQuotient_norm_le
      a b p.2 p.1 hab

theorem characteristicInversionMultiplier_measurable (a b : ℝ) :
    Measurable (fun t : ℝ => characteristicInversionMultiplier a b t) := by
  unfold characteristicInversionMultiplier
  refine Measurable.ite ?_ measurable_const ?_
  · simpa using (MeasurableSet.singleton (0 : ℝ))
  · have htC : Continuous (fun t : ℝ => (t : ℂ)) :=
      Complex.continuous_ofReal.comp continuous_id
    have hA :
        Continuous (fun t : ℝ => -(Complex.I * (t : ℂ) * (a : ℂ))) := by
      exact ((continuous_const.mul htC).mul continuous_const).neg
    have hB :
        Continuous (fun t : ℝ => -(Complex.I * (t : ℂ) * (b : ℂ))) := by
      exact ((continuous_const.mul htC).mul continuous_const).neg
    have hden : Continuous (fun t : ℝ => Complex.I * (t : ℂ)) := by
      exact continuous_const.mul htC
    exact ((Complex.continuous_exp.comp hA).measurable.sub
      (Complex.continuous_exp.comp hB).measurable).div hden.measurable

theorem characteristicInversionFubiniIntegrand_measurable (a b : ℝ) :
    Measurable
      (fun p : ℝ × ℝ => characteristicInversionFubiniIntegrand a b p) := by
  unfold characteristicInversionFubiniIntegrand
  have hmult :
      Measurable
        (fun p : ℝ × ℝ => characteristicInversionMultiplier a b p.1) :=
    (characteristicInversionMultiplier_measurable a b).comp measurable_fst
  have hfstC : Measurable (fun p : ℝ × ℝ => (p.1 : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp measurable_fst
  have hsndC : Measurable (fun p : ℝ × ℝ => (p.2 : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp measurable_snd
  have hexp :
      Measurable
        (fun p : ℝ × ℝ =>
          Complex.exp (Complex.I * (p.1 : ℂ) * (p.2 : ℂ))) :=
    ((measurable_const.mul hfstC).mul hsndC).cexp
  exact hmult.mul hexp

/-- Integrability condition needed to instantiate Chapter 8 Fubini on `[-T,T] × ℝ`. -/
def characteristicInversionFubiniIntegrable
    (μ : Measure ℝ) (a b T : ℝ) : Prop :=
  Integrable
    (fun p : ℝ × ℝ => characteristicInversionFubiniIntegrand a b p)
    ((volume.restrict (Icc (-T) T)).prod μ)

theorem characteristicInversionFubiniIntegrable_of_finite
    (μ : Measure ℝ) [IsFiniteMeasure μ] (a b T : ℝ) (hab : a ≤ b) :
    characteristicInversionFubiniIntegrable μ a b T := by
  unfold characteristicInversionFubiniIntegrable
  let M : Measure (ℝ × ℝ) := (volume.restrict (Icc (-T) T)).prod μ
  haveI : IsFiniteMeasure M := by
    dsimp [M]
    infer_instance
  have hmeas :
      AEStronglyMeasurable
        (fun p : ℝ × ℝ => characteristicInversionFubiniIntegrand a b p)
        M :=
    (characteristicInversionFubiniIntegrand_measurable a b).aestronglyMeasurable
  have hbound :
      ∀ᵐ p ∂M, ‖characteristicInversionFubiniIntegrand a b p‖ ≤ b - a :=
    ae_of_all M fun p => characteristicInversionFubiniIntegrand_norm_le
      a b hab p
  exact Integrable.of_bound hmeas (b - a) hbound

/-- Applying Chapter 8 Fubini once the product-space integrability bridge is available. -/
def characteristicInversionFubiniFromIntegrable
    (μ : Measure ℝ) (a b T : ℝ) : Prop :=
  characteristicInversionFubiniIntegrable μ a b T →
    characteristicInversionFubiniSwap μ a b T

/-- Product-measure Fubini swap in the exact form supplied by Chapter 8. This
does not yet identify either side with the oriented interval integral in
`characteristicInversionTruncation`; that interval/product bridge remains a
separate obligation. -/
def characteristicInversionProductFubiniSwap
    (μ : Measure ℝ) (a b T : ℝ) : Prop :=
  (∫ p : ℝ × ℝ, characteristicInversionFubiniIntegrand a b p ∂
      ((volume.restrict (Icc (-T) T)).prod μ)) =
    ∫ x, ∫ t,
      characteristicInversionFubiniIntegrand a b (t, x) ∂
        (volume.restrict (Icc (-T) T)) ∂μ

/-- Direct use of the exported Chapter 8 Fubini theorem on the product measure. -/
theorem characteristicInversionProductFubiniSwap_of_integrable
    (μ : Measure ℝ) [SigmaFinite μ] (a b T : ℝ)
    (hf : characteristicInversionFubiniIntegrable μ a b T) :
    characteristicInversionProductFubiniSwap μ a b T := by
  let P : Measure ℝ := volume.restrict (Icc (-T) T)
  let f : ℝ × ℝ → ℂ := characteristicInversionFubiniIntegrand a b
  have hf' : Integrable f (P.prod μ) := by
    simpa [characteristicInversionFubiniIntegrable, P, f] using hf
  have h := thm_8_5 P μ (f := f) hf'.1 (Or.inr (Or.inr hf'.2))
  have hswap :
      (∫ t, ∫ x, f (t, x) ∂μ ∂P) =
        ∫ x, ∫ t, f (t, x) ∂P ∂μ := h.2.2.2.1
  have hprod :
      (∫ t, ∫ x, f (t, x) ∂μ ∂P) =
        ∫ z, f z ∂(P.prod μ) := h.2.2.2.2
  exact by
    simpa [characteristicInversionProductFubiniSwap, P, f] using hprod.symm.trans hswap

/-- For fixed `t`, the inner integral against `μ` is the characteristic
function times the multiplier. -/
theorem characteristicInversionFubiniIntegrand_integral_eq_charFun
    (μ : Measure ℝ) (a b t : ℝ) :
    (∫ x, characteristicInversionFubiniIntegrand a b (t, x) ∂μ) =
      characteristicInversionMultiplier a b t * charFun μ t := by
  have hconst :
      (∫ x, characteristicInversionMultiplier a b t *
            Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) ∂μ) =
        characteristicInversionMultiplier a b t *
          ∫ x, Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) ∂μ := by
    simpa using
      (integral_const_mul (μ := μ)
        (r := characteristicInversionMultiplier a b t)
        (f := fun x : ℝ =>
          Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))))
  calc
    (∫ x, characteristicInversionFubiniIntegrand a b (t, x) ∂μ)
        = ∫ x, characteristicInversionMultiplier a b t *
            Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) ∂μ := by
            simp [characteristicInversionFubiniIntegrand]
    _ = characteristicInversionMultiplier a b t *
          ∫ x, Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) ∂μ := hconst
    _ = characteristicInversionMultiplier a b t * charFun μ t := by
            congr 1
            refine integral_congr_ae ?_
            filter_upwards with x
            congr 1
            dsimp [charFun, inner]
            simp
            ring

theorem characteristicInversionTruncation_eq_fubiniLeft
    (μ : Measure ℝ) (a b T : ℝ) (hT : 0 ≤ T) :
    characteristicInversionTruncation μ a b T =
      ∫ t, ∫ x, characteristicInversionFubiniIntegrand a b (t, x) ∂μ ∂
        (volume.restrict (Icc (-T) T)) := by
  have hle : -T ≤ T := by
    linarith
  rw [characteristicInversionTruncation]
  rw [intervalIntegral.integral_of_le hle]
  have hmeasure :
      volume.restrict (Ioc (-T) T) =
        volume.restrict (Icc (-T) T) := by
    exact Measure.restrict_congr_set Ioc_ae_eq_Icc
  rw [hmeasure]
  refine integral_congr_ae ?_
  filter_upwards with t
  rw [characteristicInversionFubiniIntegrand_integral_eq_charFun]

theorem characteristicInversionInnerKernel_eq_restrictIntegral
    (a b x T : ℝ) (hT : 0 ≤ T) :
    characteristicInversionInnerKernel a b x T =
      ∫ t, characteristicInversionFubiniIntegrand a b (t, x) ∂
        (volume.restrict (Icc (-T) T)) := by
  have hle : -T ≤ T := by
    linarith
  rw [characteristicInversionInnerKernel]
  rw [intervalIntegral.integral_of_le hle]
  have hmeasure :
      volume.restrict (Ioc (-T) T) =
        volume.restrict (Icc (-T) T) := by
    exact Measure.restrict_congr_set Ioc_ae_eq_Icc
  rw [hmeasure]
  refine integral_congr_ae ?_
  filter_upwards with t
  simp [characteristicInversionFubiniIntegrand]

theorem characteristicInversionInnerIntegral_eq_fubiniRight
    (μ : Measure ℝ) (a b T : ℝ) (hT : 0 ≤ T) :
    (∫ x, characteristicInversionInnerKernel a b x T ∂μ) =
      ∫ x, ∫ t, characteristicInversionFubiniIntegrand a b (t, x) ∂
        (volume.restrict (Icc (-T) T)) ∂μ := by
  refine integral_congr_ae ?_
  filter_upwards with x
  exact characteristicInversionInnerKernel_eq_restrictIntegral a b x T hT

theorem characteristicInversionFubiniSwap_of_integrable_nonneg
    (μ : Measure ℝ) [SigmaFinite μ] (a b T : ℝ) (hT : 0 ≤ T)
    (hf : characteristicInversionFubiniIntegrable μ a b T) :
    characteristicInversionFubiniSwap μ a b T := by
  let P : Measure ℝ := volume.restrict (Icc (-T) T)
  let f : ℝ × ℝ → ℂ := characteristicInversionFubiniIntegrand a b
  have hf' : Integrable f (P.prod μ) := by
    simpa [characteristicInversionFubiniIntegrable, P, f] using hf
  have hswap := (thm_8_5 P μ (f := f) hf'.1 (Or.inr (Or.inr hf'.2))).2.2.2.1
  rw [characteristicInversionFubiniSwap]
  rw [characteristicInversionTruncation_eq_fubiniLeft μ a b T hT]
  rw [characteristicInversionInnerIntegral_eq_fubiniRight μ a b T hT]
  simpa [P, f] using hswap

