/-
TASK ID: prob_9_5
TYPE: Problem
SOURCE PLAN: chapter9-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_9_3
import ToyApollo.Output.thm_9_7
import ToyApollo.Output.def_9_1

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory Complex
open scoped Nat

noncomputable def standardGaussianCharFun (t : ℝ) : ℂ :=
  charFun (ProbabilityTheory.gaussianReal 0 (1 : NNReal)) t

noncomputable def standardGaussianPsiReal (t : ℝ) : ℝ :=
  (standardGaussianCharFun t).re

noncomputable def standardGaussianEvenMoment (k : ℕ) : ℝ :=
  2 * (Real.sqrt (2 * Real.pi))⁻¹ *
    ∫ x in Set.Ioi (0 : ℝ),
      x ^ (2 * k : ℝ) * Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℝ))

theorem standardGaussian_derivative_formula_via_thm_9_7 (t : ℝ) :
    iteratedDeriv 1 standardGaussianCharFun t =
      ∫ x : ℝ,
        characteristicFunctionDerivativeIntegrand 1 t x
          ∂ProbabilityTheory.gaussianReal 0 (1 : NNReal) := by
  unfold standardGaussianCharFun
  have hmem :
      MemLp id ((1 : ℕ) : ENNReal) (ProbabilityTheory.gaussianReal 0 (1 : NNReal)) := by
    simpa using
      (ProbabilityTheory.memLp_id_gaussianReal' (μ := 0) (v := (1 : NNReal))
        (((1 : ℕ) : ENNReal)) (by norm_num))
  exact characteristicFunction_iteratedDeriv_law
    (μ := ProbabilityTheory.gaussianReal 0 (1 : NNReal))
    (n := 1)
    (hμ := hmem)
    t

noncomputable def standardGaussianExpKernel (t x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (x : ℂ) * (t : ℂ))

theorem standardGaussianCharFun_density (t : ℝ) :
    standardGaussianCharFun t =
      ∫ x : ℝ,
        (ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℂ) *
          standardGaussianExpKernel t x := by
  unfold standardGaussianCharFun
  rw [charFun_apply_real]
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul
    (μ := 0) (v := (1 : NNReal)) (hv := by norm_num)
    (f := fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))]
  congr with x
  change (ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℂ) *
      Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) =
    (ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℂ) *
      standardGaussianExpKernel t x
  unfold standardGaussianExpKernel
  congr 1
  ring_nf

theorem standardGaussianPDF_hasDerivAt (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => (ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) y : ℂ))
      ((-x * ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℝ) : ℂ) x := by
  have hreal :
      HasDerivAt
        (fun y : ℝ => ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) y)
        (-x * ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x) x := by
    rw [ProbabilityTheory.gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    have h_inner : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-x) x := by
      have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
        simpa using ((hasDerivAt_id x).pow 2)
      convert hsq.neg.div_const 2 using 1
      ring
    have h_exp := h_inner.exp
    have h_const := h_exp.const_mul ((Real.sqrt (2 * Real.pi))⁻¹)
    convert h_const using 1
    ring_nf
  have hclm :=
    (ContinuousLinearMap.hasFDerivAt Complex.ofRealCLM).comp_hasDerivAt x hreal
  simpa using hclm

theorem standardGaussianExpKernel_hasDerivAt (t x : ℝ) :
    HasDerivAt (fun y : ℝ => standardGaussianExpKernel t y)
      (Complex.I * (t : ℂ) * standardGaussianExpKernel t x) x := by
  unfold standardGaussianExpKernel
  have h_ofReal : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x))
  have h_inner : HasDerivAt
      (fun y : ℝ => Complex.I * (y : ℂ) * (t : ℂ))
      (Complex.I * (t : ℂ)) x := by
    convert h_ofReal.const_mul (Complex.I * (t : ℂ)) using 1
    · funext y
      ring
    · ring
  convert h_inner.cexp using 1
  ring

theorem standardGaussianDensityKernel_integrable (t : ℝ) :
    Integrable (fun x : ℝ =>
      (ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℂ) *
        standardGaussianExpKernel t x) := by
  have hquad : Integrable (fun x : ℝ =>
      Complex.exp (-(1 / 2 : ℂ) * (x : ℂ) ^ 2 + (Complex.I * (t : ℂ)) * (x : ℂ) + 0)) := by
    exact integrable_cexp_quadratic (b := (1 / 2 : ℂ)) (c := Complex.I * (t : ℂ)) (d := 0)
      (by norm_num)
  have hconst := hquad.const_mul (((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) : ℂ)
  convert hconst using 1
  ext x
  unfold standardGaussianExpKernel ProbabilityTheory.gaussianPDFReal
  push_cast
  norm_num
  rw [mul_assoc, ← Complex.exp_add]
  congr 1
  ring_nf

theorem standardGaussianCharFun_density_integrable (t : ℝ) :
    Integrable (fun x : ℝ =>
      (ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℂ) *
        standardGaussianExpKernel t x) :=
  standardGaussianDensityKernel_integrable t

theorem standardGaussianXDensityKernel_integrable (t : ℝ) :
    Integrable (fun x : ℝ =>
      ((x : ℂ) * (ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℂ)) *
        standardGaussianExpKernel t x) := by
  have hbase : Integrable
      (fun x : ℝ => (x : ℂ) * Complex.exp (-(1 / 2 : ℂ) * (x : ℂ) ^ 2)) := by
    exact integrable_mul_cexp_neg_mul_sq (b := (1 / 2 : ℂ)) (by norm_num)
  have hg : Integrable
      (fun x : ℝ => (x : ℂ) *
        (ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℂ)) := by
    have hconst := hbase.const_mul (((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) : ℂ)
    convert hconst using 1
    ext x
    rw [ProbabilityTheory.gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    push_cast
    ring_nf
  refine Integrable.mono hg (by unfold standardGaussianExpKernel; fun_prop) ?_
  filter_upwards with x
  have hnormexp : ‖standardGaussianExpKernel t x‖ = 1 := by
    unfold standardGaussianExpKernel
    have harg :
        Complex.I * (x : ℂ) * (t : ℂ) = ((x * t : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  rw [norm_mul, hnormexp, mul_one]

theorem standardGaussianDensityKernel_deriv_integral_by_parts (t : ℝ) :
    (∫ x : ℝ,
      (ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℂ) *
        (Complex.I * (t : ℂ) * standardGaussianExpKernel t x)) =
      - ∫ x : ℝ,
        (((-x * ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℝ) : ℂ) *
          standardGaussianExpKernel t x) := by
  have huv' : Integrable (fun x : ℝ =>
      (ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℂ) *
        (Complex.I * (t : ℂ) * standardGaussianExpKernel t x)) := by
    have h := (standardGaussianDensityKernel_integrable t).mul_const (Complex.I * (t : ℂ))
    convert h using 1
    ext x
    ring
  have hu'v : Integrable (fun x : ℝ =>
      (((-x * ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℝ) : ℂ) *
        standardGaussianExpKernel t x)) := by
    have h := (standardGaussianXDensityKernel_integrable t).const_mul (-1 : ℂ)
    convert h using 1
    ext x
    push_cast
    ring
  exact MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => (ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℂ))
    (v := fun x : ℝ => standardGaussianExpKernel t x)
    (u' := fun x : ℝ =>
      ((-x * ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℝ) : ℂ))
    (v' := fun x : ℝ => Complex.I * (t : ℂ) * standardGaussianExpKernel t x)
    (fun x _ => standardGaussianPDF_hasDerivAt x)
    (fun x _ => standardGaussianExpKernel_hasDerivAt t x)
    huv' hu'v (standardGaussianDensityKernel_integrable t)

theorem standardGaussianDerivativeDensityIntegral_eq_neg_t (t : ℝ) :
    (∫ x : ℝ,
      (ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℂ) *
        (Complex.I * (x : ℂ) * standardGaussianExpKernel t x)) =
      -(t : ℂ) *
        ∫ x : ℝ,
          (ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℂ) *
            standardGaussianExpKernel t x := by
  have hibp := standardGaussianDensityKernel_deriv_integral_by_parts t
  have hnegfun : (fun x : ℝ =>
      (((-x * ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℝ) : ℂ) *
        standardGaussianExpKernel t x)) =
      fun x : ℝ =>
        -(((x : ℂ) * (ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℂ)) *
          standardGaussianExpKernel t x) := by
    funext x
    push_cast
    ring
  rw [hnegfun, integral_neg, neg_neg] at hibp
  calc
    (∫ x : ℝ,
      (ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℂ) *
        (Complex.I * (x : ℂ) * standardGaussianExpKernel t x))
        = ∫ x : ℝ, Complex.I *
          (((x : ℂ) * (ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℂ)) *
            standardGaussianExpKernel t x) := by
            congr with x
            ring
    _ = Complex.I * ∫ x : ℝ,
          ((x : ℂ) * (ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℂ)) *
            standardGaussianExpKernel t x := by
            simpa using integral_const_mul (μ := volume) (r := Complex.I)
              (f := fun x : ℝ =>
                ((x : ℂ) * (ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℂ)) *
                  standardGaussianExpKernel t x)
    _ = Complex.I * ∫ x : ℝ,
          (ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℂ) *
            (Complex.I * (t : ℂ) * standardGaussianExpKernel t x) := by
            rw [← hibp]
    _ = Complex.I * (∫ x : ℝ, (Complex.I * (t : ℂ)) *
          ((ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℂ) *
            standardGaussianExpKernel t x)) := by
            congr 1
            congr with x
            ring
    _ = Complex.I * ((Complex.I * (t : ℂ)) * ∫ x : ℝ,
          (ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℂ) *
            standardGaussianExpKernel t x) := by
            congr 1
            simpa using integral_const_mul (μ := volume) (r := Complex.I * (t : ℂ))
              (f := fun x : ℝ =>
                (ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℂ) *
                  standardGaussianExpKernel t x)
    _ = -(t : ℂ) * ∫ x : ℝ,
          (ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℂ) *
            standardGaussianExpKernel t x := by
            let A : ℂ := ∫ x : ℝ,
              (ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℂ) *
                standardGaussianExpKernel t x
            have hII : Complex.I * (Complex.I * (t : ℂ)) = -(t : ℂ) := by
              rw [← mul_assoc, Complex.I_mul_I]
              ring
            change Complex.I * ((Complex.I * (t : ℂ)) * A) = -(t : ℂ) * A
            calc
              Complex.I * ((Complex.I * (t : ℂ)) * A) =
                  (Complex.I * (Complex.I * (t : ℂ))) * A := by ring
              _ = -(t : ℂ) * A := by rw [hII]

theorem standardGaussianCharFun_deriv_source (t : ℝ) :
    deriv standardGaussianCharFun t = -(t : ℂ) * standardGaussianCharFun t := by
  have hD := standardGaussian_derivative_formula_via_thm_9_7 t
  rw [iteratedDeriv_one] at hD
  rw [hD]
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul
    (μ := 0) (v := (1 : NNReal)) (hv := by norm_num)
    (f := fun x : ℝ => characteristicFunctionDerivativeIntegrand 1 t x)]
  rw [standardGaussianCharFun_density t]
  simpa [characteristicFunctionDerivativeIntegrand, standardGaussianExpKernel, smul_eq_mul]
    using standardGaussianDerivativeDensityIntegral_eq_neg_t t

theorem standardGaussianCharFun_differentiable :
    Differentiable ℝ standardGaussianCharFun := by
  unfold standardGaussianCharFun
  have hmem : MemLp id (1 : ℕ)
      (ProbabilityTheory.gaussianReal 0 (1 : NNReal)) := by
    simpa using
      (ProbabilityTheory.memLp_id_gaussianReal' (μ := 0) (v := (1 : NNReal))
        ((1 : ℕ) : ENNReal) (by norm_num))
  exact (MeasureTheory.contDiff_charFun
    (μ := ProbabilityTheory.gaussianReal 0 (1 : NNReal)) hmem).differentiable_one

theorem standardGaussianCharFun_zero : standardGaussianCharFun 0 = 1 := by
  unfold standardGaussianCharFun
  rw [MeasureTheory.charFun_zero]
  simp

theorem standardGaussianPsiReal_deriv_source (t : ℝ) :
    deriv standardGaussianPsiReal t = -t * standardGaussianPsiReal t := by
  have hchar0 : HasDerivAt standardGaussianCharFun (deriv standardGaussianCharFun t) t :=
    (standardGaussianCharFun_differentiable t).hasDerivAt
  have hchar : HasDerivAt standardGaussianCharFun
      (-(t : ℂ) * standardGaussianCharFun t) t := by
    simpa [standardGaussianCharFun_deriv_source t] using hchar0
  have hre :=
    (ContinuousLinearMap.hasFDerivAt Complex.reCLM).comp_hasDerivAt t hchar
  have hderiv : HasDerivAt standardGaussianPsiReal
      ((-(t : ℂ) * standardGaussianCharFun t).re) t := by
    simpa [standardGaussianPsiReal] using hre
  rw [hderiv.deriv]
  unfold standardGaussianPsiReal
  simp

theorem standardGaussianPsiReal_deriv :
    deriv standardGaussianPsiReal = fun t : ℝ => -t * standardGaussianPsiReal t := by
  funext t
  exact standardGaussianPsiReal_deriv_source t

theorem standardGaussianPositiveExp_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (((s ^ 2 : ℝ) / 2 : ℝ) : ℂ))
      (Complex.exp (((t ^ 2 : ℝ) / 2 : ℝ) : ℂ) * (t : ℂ)) t := by
  have hreal : HasDerivAt (fun s : ℝ => (s ^ 2 : ℝ) / 2) t t := by
    have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      simpa using ((hasDerivAt_id t).pow 2)
    convert hsq.div_const 2 using 1
    ring
  have hcomplex :=
    (ContinuousLinearMap.hasFDerivAt Complex.ofRealCLM).comp_hasDerivAt t hreal
  exact hcomplex.cexp

theorem standardGaussianPositiveExp_differentiable :
    Differentiable ℝ
      (fun s : ℝ => Complex.exp (((s ^ 2 : ℝ) / 2 : ℝ) : ℂ)) := by
  intro t
  exact (standardGaussianPositiveExp_hasDerivAt t).differentiableAt

theorem standardGaussianCorrectedProduct_deriv_zero (t : ℝ) :
    deriv (fun s : ℝ => standardGaussianCharFun s *
      Complex.exp (((s ^ 2 : ℝ) / 2 : ℝ) : ℂ)) t = 0 := by
  have hchar0 : HasDerivAt standardGaussianCharFun (deriv standardGaussianCharFun t) t :=
    (standardGaussianCharFun_differentiable t).hasDerivAt
  have hchar : HasDerivAt standardGaussianCharFun
      (-(t : ℂ) * standardGaussianCharFun t) t := by
    simpa [standardGaussianCharFun_deriv_source t] using hchar0
  have hexp := standardGaussianPositiveExp_hasDerivAt t
  have hprod := hchar.mul hexp
  change deriv (standardGaussianCharFun *
    (fun s : ℝ => Complex.exp (((s ^ 2 : ℝ) / 2 : ℝ) : ℂ))) t = 0
  rw [hprod.deriv]
  ring

theorem standardGaussianCorrectedProduct_differentiable :
    Differentiable ℝ (fun s : ℝ => standardGaussianCharFun s *
      Complex.exp (((s ^ 2 : ℝ) / 2 : ℝ) : ℂ)) := by
  exact standardGaussianCharFun_differentiable.mul
    standardGaussianPositiveExp_differentiable

theorem standardGaussianCharFun_eq_exp (t : ℝ) :
    standardGaussianCharFun t = Complex.exp (-(t ^ 2 : ℝ) / 2 : ℂ) := by
  let F : ℝ → ℂ := fun s => standardGaussianCharFun s *
    Complex.exp (((s ^ 2 : ℝ) / 2 : ℝ) : ℂ)
  have hFdiff : Differentiable ℝ F := by
    exact standardGaussianCorrectedProduct_differentiable
  have hFderiv : ∀ s, deriv F s = 0 := by
    intro s
    exact standardGaussianCorrectedProduct_deriv_zero s
  have hconst := is_const_of_deriv_eq_zero hFdiff hFderiv t 0
  have hF0 : F 0 = 1 := by
    simp [F, standardGaussianCharFun_zero]
  have hprod0 :
      standardGaussianCharFun t *
        Complex.exp (((t ^ 2 : ℝ) / 2 : ℝ) : ℂ) = F 0 := by
    simpa [F] using hconst
  have hprod :
      standardGaussianCharFun t *
        Complex.exp (((t ^ 2 : ℝ) / 2 : ℝ) : ℂ) = 1 := by
    rw [hprod0, hF0]
  have hnonzero : Complex.exp (((t ^ 2 : ℝ) / 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.exp_ne_zero _
  calc
    standardGaussianCharFun t =
        1 * (Complex.exp (((t ^ 2 : ℝ) / 2 : ℝ) : ℂ))⁻¹ := by
      calc
        standardGaussianCharFun t =
            (standardGaussianCharFun t *
              Complex.exp (((t ^ 2 : ℝ) / 2 : ℝ) : ℂ)) *
              (Complex.exp (((t ^ 2 : ℝ) / 2 : ℝ) : ℂ))⁻¹ := by
              field_simp [hnonzero]
        _ = 1 * (Complex.exp (((t ^ 2 : ℝ) / 2 : ℝ) : ℂ))⁻¹ := by
              rw [hprod]
    _ = Complex.exp (-(t ^ 2 : ℝ) / 2 : ℂ) := by
      rw [one_mul]
      rw [← Complex.exp_neg]
      congr 1
      push_cast
      ring

theorem standardGaussianCharFun_im_zero (t : ℝ) :
    (standardGaussianCharFun t).im = 0 := by
  rw [standardGaussianCharFun_eq_exp t]
  convert Complex.exp_ofReal_im (-(t ^ 2) / 2) using 2
  norm_num

theorem standardGaussianPsiReal_eq_exp (t : ℝ) :
    standardGaussianPsiReal t = Real.exp (-(t ^ 2) / 2) := by
  unfold standardGaussianPsiReal
  rw [standardGaussianCharFun_eq_exp t]
  convert Complex.exp_ofReal_re (-(t ^ 2) / 2) using 2
  norm_num

theorem standardGaussianCharFun_re_density (t : ℝ) :
    (standardGaussianCharFun t).re =
      ∫ x : ℝ,
        ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x * Real.cos (t * x) := by
  rw [standardGaussianCharFun_density t]
  calc
    (∫ x : ℝ,
        (ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℂ) *
          standardGaussianExpKernel t x).re
        = ∫ x : ℝ,
            (((ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x : ℂ) *
              standardGaussianExpKernel t x).re) := by
          exact (integral_re (standardGaussianCharFun_density_integrable t)).symm
    _ = ∫ x : ℝ,
        ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x * Real.cos (t * x) := by
          congr with x
          rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
          unfold standardGaussianExpKernel
          have harg : Complex.I * (x : ℂ) * (t : ℂ) = ((x * t : ℝ) : ℂ) * Complex.I := by
            push_cast
            ring
          rw [harg, Complex.exp_ofReal_mul_I_re]
          ring_nf

theorem standardGaussianPsiReal_cosineIntegral (t : ℝ) :
    standardGaussianPsiReal t =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        ∫ x : ℝ, Real.cos (t * x) * Real.exp (-(x ^ 2) / 2) := by
  calc
    standardGaussianPsiReal t = (standardGaussianCharFun t).re := rfl
    _ = ∫ x : ℝ,
        ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) x * Real.cos (t * x) :=
          standardGaussianCharFun_re_density t
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
        ∫ x : ℝ, Real.cos (t * x) * Real.exp (-(x ^ 2) / 2) := by
          rw [← integral_const_mul]
          congr with x
          unfold ProbabilityTheory.gaussianPDFReal
          norm_num
          ring_nf

theorem standardGaussianEvenMoment_gamma (k : ℕ) :
    standardGaussianEvenMoment k =
      2 * (Real.sqrt (2 * Real.pi))⁻¹ *
        ((1 / 2 : ℝ) ^ (-((2 * k : ℝ) + 1) / 2) * (1 / 2) *
          Real.Gamma (((2 * k : ℝ) + 1) / 2)) := by
  unfold standardGaussianEvenMoment
  rw [_root_.integral_rpow_mul_exp_neg_mul_rpow (p := (2 : ℝ)) (q := (2 * k : ℝ))
      (b := (1 / 2 : ℝ)) (by norm_num)
      (by
        have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        nlinarith)
      (by norm_num)]

theorem standardGaussianEvenMoment_fullIntegral_abs (k : ℕ) :
    standardGaussianEvenMoment k =
      ∫ x : ℝ,
        (Real.sqrt (2 * Real.pi))⁻¹ * |x| ^ (2 * k : ℝ) *
          Real.exp (-(1 / 2 : ℝ) * |x| ^ (2 : ℝ)) := by
  symm
  calc
    (∫ x : ℝ,
        (Real.sqrt (2 * Real.pi))⁻¹ * |x| ^ (2 * k : ℝ) *
          Real.exp (-(1 / 2 : ℝ) * |x| ^ (2 : ℝ)))
        = 2 * ∫ x in Set.Ioi (0 : ℝ),
            (Real.sqrt (2 * Real.pi))⁻¹ * x ^ (2 * k : ℝ) *
              Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℝ)) := by
          exact integral_comp_abs
            (f := fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * x ^ (2 * k : ℝ) *
              Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℝ)))
    _ = standardGaussianEvenMoment k := by
          unfold standardGaussianEvenMoment
          rw [show (∫ x in Set.Ioi (0 : ℝ),
              (Real.sqrt (2 * Real.pi))⁻¹ * x ^ (2 * k : ℝ) *
                Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℝ))) =
              (Real.sqrt (2 * Real.pi))⁻¹ *
                ∫ x in Set.Ioi (0 : ℝ),
                  x ^ (2 * k : ℝ) * Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℝ)) by
            rw [show (fun x : ℝ =>
                (Real.sqrt (2 * Real.pi))⁻¹ * x ^ (2 * k : ℝ) *
                  Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℝ))) =
                (fun x : ℝ =>
                  (Real.sqrt (2 * Real.pi))⁻¹ *
                    (x ^ (2 * k : ℝ) * Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℝ)))) by
              funext x
              ring]
            rw [integral_const_mul]]
          ring

theorem standardGaussianEvenMoment_eq_rthMoment (k : ℕ) :
    rthMoment (ProbabilityTheory.gaussianReal 0 (1 : NNReal)) id (2 * k) =
      standardGaussianEvenMoment k := by
  rw [standardGaussianEvenMoment_fullIntegral_abs k]
  unfold rthMoment ProbabilityTheory.moment
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul
    (μ := 0) (v := (1 : NNReal)) (hv := by norm_num)
    (f := (id : ℝ → ℝ) ^ (2 * k))]
  congr with x
  simp only [Pi.pow_apply, id_eq, smul_eq_mul]
  unfold ProbabilityTheory.gaussianPDFReal
  norm_num
  have hxpow : |x| ^ (2 * k) = x ^ (2 * k) :=
    (even_two.mul_right k).pow_abs x
  rw [← hxpow]
  have hrpow_nat : |x| ^ (2 * k : ℝ) = |x| ^ (2 * k) :=
    by
      have hcast : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by norm_num
      simpa [hcast] using Real.rpow_natCast |x| (2 * k)
  rw [hrpow_nat]
  ring_nf

theorem standardGaussianGamma_half_rewrite (k : ℕ) :
    Real.Gamma (((2 * k : ℝ) + 1) / 2) =
      ((2 * k - 1 : ℕ)‼ : ℝ) * Real.sqrt Real.pi / (2 ^ k) := by
  rw [show ((2 * k : ℝ) + 1) / 2 = (k : ℝ) + 1 / 2 by ring]
  exact Real.Gamma_nat_add_half k

theorem standardGaussianPower_factor (k : ℕ) :
    (1 / 2 : ℝ) ^ (-1 / 2 - (k : ℝ)) * 2⁻¹ ^ k = Real.sqrt 2 := by
  rw [show (-1 / 2 - (k : ℝ)) = (-1 / 2 : ℝ) + (-(k : ℝ)) by ring]
  rw [Real.rpow_add (by norm_num : 0 < (1 / 2 : ℝ))]
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring]
  rw [Real.rpow_neg (by norm_num : 0 ≤ (1 / 2 : ℝ)) (1 / 2)]
  rw [← Real.sqrt_eq_rpow]
  rw [← Real.sqrt_inv]
  rw [Real.rpow_neg (by norm_num : 0 ≤ (1 / 2 : ℝ)) (k : ℝ)]
  rw [Real.rpow_natCast]
  norm_num

theorem standardGaussianEvenMoment_doubleFactorial (k : ℕ) :
    standardGaussianEvenMoment k = ((2 * k - 1 : ℕ)‼ : ℝ) := by
  rw [standardGaussianEvenMoment_gamma k, standardGaussianGamma_half_rewrite k]
  ring_nf
  rw [show (√(Real.pi * 2))⁻¹ * (1 / 2 : ℝ) ^ (-1 / 2 - (k : ℝ)) *
      ↑(k * 2 - 1)‼ * √Real.pi * 2⁻¹ ^ k =
      ((1 / 2 : ℝ) ^ (-1 / 2 - (k : ℝ)) * 2⁻¹ ^ k) *
        ((√(Real.pi * 2))⁻¹ * √Real.pi) * ↑(k * 2 - 1)‼ by ring]
  rw [standardGaussianPower_factor k]
  have hsqrt : √(Real.pi * 2) = √Real.pi * √(2 : ℝ) := by
    rw [Real.sqrt_mul Real.pi_pos.le]
  rw [hsqrt]
  field_simp [(Real.sqrt_pos_of_pos Real.pi_pos).ne',
    (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 2)).ne']

theorem prob_9_5 :
    (∀ t : ℝ,
      (standardGaussianCharFun t).im = 0 ∧
      standardGaussianPsiReal t =
        (Real.sqrt (2 * Real.pi))⁻¹ *
          ∫ x : ℝ, Real.cos (t * x) * Real.exp (-(x ^ 2) / 2) ∧
      iteratedDeriv 1 standardGaussianCharFun t =
        ∫ x : ℝ,
          characteristicFunctionDerivativeIntegrand 1 t x
            ∂ProbabilityTheory.gaussianReal 0 (1 : NNReal) ∧
      deriv standardGaussianPsiReal t = -t * standardGaussianPsiReal t ∧
      standardGaussianPsiReal t = Real.exp (-(t ^ 2) / 2) ∧
      standardGaussianCharFun t = Complex.exp (-(t ^ 2 : ℝ) / 2 : ℂ)) ∧
    (∀ k : ℕ,
      rthMoment (ProbabilityTheory.gaussianReal 0 (1 : NNReal)) id (2 * k) =
        standardGaussianEvenMoment k ∧
      rthMoment (ProbabilityTheory.gaussianReal 0 (1 : NNReal)) id (2 * k) =
        ((2 * k - 1 : ℕ)‼ : ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro t
    exact ⟨standardGaussianCharFun_im_zero t,
      standardGaussianPsiReal_cosineIntegral t,
      standardGaussian_derivative_formula_via_thm_9_7 t,
      by rw [standardGaussianPsiReal_deriv],
      standardGaussianPsiReal_eq_exp t,
      standardGaussianCharFun_eq_exp t⟩
  · intro k
    exact ⟨standardGaussianEvenMoment_eq_rthMoment k,
      (standardGaussianEvenMoment_eq_rthMoment k).trans
        (standardGaussianEvenMoment_doubleFactorial k)⟩
