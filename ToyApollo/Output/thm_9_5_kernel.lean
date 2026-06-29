/-
TASK ID: thm_9_5_kernel
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_9_5_fubini
import ToyApollo.Output.thm_9_5_dirichlet

open Filter MeasureTheory Set
open scoped Topology Interval

noncomputable section

theorem characteristicInversionSinMulDiv_intervalIntegrable_complex
    (c r s : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => ((Real.sin (t * c) / t : ℝ) : ℂ)) volume r s := by
  by_cases hc : c = 0
  · subst c
    simpa using
      (continuous_const.intervalIntegrable r s :
        IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume r s)
  · have hhelper_cont :
        Continuous (fun t : ℝ => ((c * Real.sinc (c * t) : ℝ) : ℂ)) := by
      exact Complex.continuous_ofReal.comp
        ((Real.continuous_sinc.comp
          (continuous_const.mul continuous_id)).const_mul c)
    have hhelper :
        IntervalIntegrable
          (fun t : ℝ => ((c * Real.sinc (c * t) : ℝ) : ℂ))
          volume r s :=
      hhelper_cont.intervalIntegrable r s
    refine hhelper.congr_ae ?_
    have hne0 : ∀ᵐ t : ℝ, t ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simpa using
        (MeasureTheory.NoAtoms.measure_singleton (μ := volume) (0 : ℝ))
    filter_upwards
      [MeasureTheory.ae_restrict_of_ae (s := Set.uIoc r s) hne0]
      with t ht0
    have hct : c * t ≠ 0 := mul_ne_zero hc ht0
    rw [mul_comm c t] at hct ⊢
    rw [Real.sinc_of_ne_zero hct]
    norm_num
    field_simp [hc, ht0]

theorem characteristicInversionCosineQuotient_intervalIntegrable_complex
    (a b x r s : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        (((Real.cos (t * (x - a)) - Real.cos (t * (x - b))) / t : ℝ) : ℂ))
      volume r s := by
  let c : ℝ := ((x - a) - (x - b)) / 2
  let g : ℝ → ℂ := fun t =>
    ((-2 * Real.sin ((t * (x - a) + t * (x - b)) / 2) : ℝ) : ℂ)
  have hf :
      IntervalIntegrable
        (fun t : ℝ => ((Real.sin (t * c) / t : ℝ) : ℂ)) volume r s :=
    characteristicInversionSinMulDiv_intervalIntegrable_complex c r s
  have hg : ContinuousOn g (Set.uIcc r s) := by
    have hcont : Continuous g := by
      dsimp [g]
      exact Complex.continuous_ofReal.comp
        (continuous_const.mul
          (Real.continuous_sin.comp
            (((continuous_id.mul continuous_const).add
              (continuous_id.mul continuous_const)).div_const 2)))
    exact hcont.continuousOn
  have hprod :
      IntervalIntegrable
        (fun t : ℝ => ((Real.sin (t * c) / t : ℝ) : ℂ) * g t)
        volume r s :=
    hf.mul_continuousOn hg
  refine hprod.congr_ae ?_
  have hne0 : ∀ᵐ t : ℝ, t ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using
      (MeasureTheory.NoAtoms.measure_singleton (μ := volume) (0 : ℝ))
  filter_upwards
    [MeasureTheory.ae_restrict_of_ae (s := Set.uIoc r s) hne0]
    with t ht0
  dsimp [g, c]
  rw [Real.cos_sub_cos]
  have harg :
      t * (((x - a) - (x - b)) / 2) =
        (t * (x - a) - t * (x - b)) / 2 := by
    ring
  rw [harg]
  norm_num
  field_simp [ht0]

theorem characteristicInversionCosineOddTerm_intervalIntegrable
    (a b x r s : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => characteristicInversionCosineOddTerm a b x t)
      volume r s := by
  have hcos :=
    characteristicInversionCosineQuotient_intervalIntegrable_complex
      a b x r s
  simpa [characteristicInversionCosineOddTerm] using
    hcos.const_mul (-Complex.I)

theorem characteristicInversionTranslatedExpDifference_integral_eq_sineKernel
    (a b x T : ℝ) :
    (∫ t in (-T)..T,
      (Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (a : ℂ))) -
          Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (b : ℂ)))) /
        (Complex.I * (t : ℂ))) =
      characteristicInversionSineKernel a b x T := by
  let sineTerm : ℝ → ℂ := fun t =>
    ((Real.sin (t * (x - a)) / t : ℝ) : ℂ) -
      ((Real.sin (t * (x - b)) / t : ℝ) : ℂ)
  have hsinA :
      IntervalIntegrable
        (fun t : ℝ => ((Real.sin (t * (x - a)) / t : ℝ) : ℂ))
        volume (-T) T :=
    characteristicInversionSinMulDiv_intervalIntegrable_complex
      (x - a) (-T) T
  have hsinB :
      IntervalIntegrable
        (fun t : ℝ => ((Real.sin (t * (x - b)) / t : ℝ) : ℂ))
        volume (-T) T :=
    characteristicInversionSinMulDiv_intervalIntegrable_complex
      (x - b) (-T) T
  have hsine : IntervalIntegrable sineTerm volume (-T) T := by
    dsimp [sineTerm]
    exact hsinA.sub hsinB
  have hodd :
      IntervalIntegrable
        (fun t : ℝ => characteristicInversionCosineOddTerm a b x t)
        volume (-T) T :=
    characteristicInversionCosineOddTerm_intervalIntegrable
      a b x (-T) T
  have hne0 : ∀ᵐ t : ℝ, t ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using
      (MeasureTheory.NoAtoms.measure_singleton (μ := volume) (0 : ℝ))
  calc
    (∫ t in (-T)..T,
      (Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (a : ℂ))) -
          Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (b : ℂ)))) /
        (Complex.I * (t : ℂ)))
        = ∫ t in (-T)..T,
            sineTerm t + characteristicInversionCosineOddTerm a b x t := by
            refine intervalIntegral.integral_congr_ae ?_
            filter_upwards [hne0] with t ht0 htI
            rw [
              characteristicInversionTranslatedExpDifference_div_I_mul
                a b x t ht0]
            dsimp [sineTerm, characteristicInversionCosineOddTerm]
            norm_num
            field_simp [ht0]
            ring
    _ = (∫ t in (-T)..T, sineTerm t) +
          ∫ t in (-T)..T, characteristicInversionCosineOddTerm a b x t := by
            rw [intervalIntegral.integral_add hsine hodd]
    _ = ∫ t in (-T)..T, sineTerm t := by
            rw [characteristicInversionCosineOddTerm_integral_eq_zero]
            simp
    _ = (∫ t in (-T)..T,
            ((Real.sin (t * (x - a)) / t : ℝ) : ℂ)) -
          ∫ t in (-T)..T,
            ((Real.sin (t * (x - b)) / t : ℝ) : ℂ) := by
            dsimp [sineTerm]
            rw [intervalIntegral.integral_sub hsinA hsinB]
    _ = ((∫ t in (-T)..T,
            Real.sin (t * (x - a)) / t : ℝ) : ℂ) -
          ((∫ t in (-T)..T,
            Real.sin (t * (x - b)) / t : ℝ) : ℂ) := by
            rw [intervalIntegral.integral_ofReal,
              intervalIntegral.integral_ofReal]
    _ = ((2 * characteristicInversionSinePrimitive ((x - a) * T) : ℝ) : ℂ) -
          ((2 * characteristicInversionSinePrimitive ((x - b) * T) : ℝ) : ℂ) := by
            rw [
              characteristicInversionSinMulDiv_integral_symm_eq_primitive,
              characteristicInversionSinMulDiv_integral_symm_eq_primitive]
    _ = characteristicInversionSineKernel a b x T := by
            rw [characteristicInversionSineKernel_eq_primitive]
            rw [show (x - a) * T = -((a - x) * T) by ring,
              show (x - b) * T = -((b - x) * T) by ring]
            rw [characteristicInversionSinePrimitive_neg,
              characteristicInversionSinePrimitive_neg]
            norm_num
            ring

theorem characteristicInversionSineKernel_continuous
    (a b T : ℝ) :
    Continuous (fun x : ℝ => characteristicInversionSineKernel a b x T) := by
  have hB :
      Continuous
        (fun x : ℝ => characteristicInversionSinePrimitive ((b - x) * T)) := by
    exact characteristicInversionSinePrimitive_continuous.comp
      ((continuous_const.sub continuous_id).mul continuous_const)
  have hA :
      Continuous
        (fun x : ℝ => characteristicInversionSinePrimitive ((a - x) * T)) := by
    exact characteristicInversionSinePrimitive_continuous.comp
      ((continuous_const.sub continuous_id).mul continuous_const)
  have hfun :
      (fun x : ℝ => characteristicInversionSineKernel a b x T) =
        fun x : ℝ =>
          (2 : ℂ) *
            ((characteristicInversionSinePrimitive ((b - x) * T) -
              characteristicInversionSinePrimitive ((a - x) * T) : ℝ) : ℂ) := by
    funext x
    rw [characteristicInversionSineKernel_eq_primitive]
  rw [hfun]
  exact continuous_const.mul (Complex.continuous_ofReal.comp (hB.sub hA))

theorem characteristicInversionSineKernel_aestronglyMeasurable
    (μ : Measure ℝ) (a b T : ℝ) :
    AEStronglyMeasurable
      (fun x : ℝ => characteristicInversionSineKernel a b x T) μ :=
  (characteristicInversionSineKernel_continuous a b T).aestronglyMeasurable

theorem characteristicInversionSineKernelLimit_interior_of_dirichlet
    (hlim : characteristicInversionDirichletIntegralLimit)
    {a b x : ℝ} (ha : a < x) (hb : x < b) :
    Tendsto
      (fun T : ℝ => characteristicInversionSineKernel a b x T)
      atTop
      (nhds ((2 * Real.pi : ℂ))) := by
  have hBscale :
      Tendsto (fun T : ℝ => (b - x) * T) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (sub_pos.mpr hb) tendsto_id
  have hAscale :
      Tendsto (fun T : ℝ => (a - x) * T) atTop atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg (sub_neg.mpr ha) tendsto_id
  have hB :
      Tendsto
        (fun T : ℝ =>
          characteristicInversionSinePrimitive ((b - x) * T))
        atTop
        (nhds (Real.pi / 2)) :=
    hlim.comp hBscale
  have hA :
      Tendsto
        (fun T : ℝ =>
          characteristicInversionSinePrimitive ((a - x) * T))
        atTop
        (nhds (-(Real.pi / 2))) :=
    (characteristicInversionSinePrimitive_tendsto_atBot hlim).comp hAscale
  have hdiff :
      Tendsto
        (fun T : ℝ =>
          characteristicInversionSinePrimitive ((b - x) * T) -
            characteristicInversionSinePrimitive ((a - x) * T))
        atTop
        (nhds Real.pi) := by
    have h := hB.sub hA
    convert h using 1
    ring_nf
  have hcomplex :
      Tendsto
        (fun T : ℝ =>
          (2 : ℂ) *
            ((characteristicInversionSinePrimitive ((b - x) * T) -
              characteristicInversionSinePrimitive ((a - x) * T) : ℝ) : ℂ))
        atTop
        (nhds ((2 * Real.pi : ℂ))) := by
    have h := (Filter.Tendsto.ofReal hdiff).const_mul (2 : ℂ)
    simpa using h
  exact hcomplex.congr' (Eventually.of_forall fun T =>
    (characteristicInversionSineKernel_eq_primitive a b x T).symm)

theorem characteristicInversionSineKernelLimit_leftEndpoint_of_dirichlet
    (hlim : characteristicInversionDirichletIntegralLimit)
    {a b : ℝ} (hab : a < b) :
    Tendsto
      (fun T : ℝ => characteristicInversionSineKernel a b a T)
      atTop
      (nhds (Real.pi : ℂ)) := by
  have hBscale :
      Tendsto (fun T : ℝ => (b - a) * T) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (sub_pos.mpr hab) tendsto_id
  have hB :
      Tendsto
        (fun T : ℝ =>
          characteristicInversionSinePrimitive ((b - a) * T))
        atTop
        (nhds (Real.pi / 2)) :=
    hlim.comp hBscale
  have hzero : characteristicInversionSinePrimitive 0 = 0 := by
    simp [characteristicInversionSinePrimitive]
  have hA :
      Tendsto
        (fun T : ℝ =>
          characteristicInversionSinePrimitive ((a - a) * T))
        atTop
        (nhds 0) := by
    simp [hzero]
  have hdiff :
      Tendsto
        (fun T : ℝ =>
          characteristicInversionSinePrimitive ((b - a) * T) -
            characteristicInversionSinePrimitive ((a - a) * T))
        atTop
        (nhds (Real.pi / 2)) := by
    have h := hB.sub hA
    convert h using 1
    ring_nf
  have hcomplex :
      Tendsto
        (fun T : ℝ =>
          (2 : ℂ) *
            ((characteristicInversionSinePrimitive ((b - a) * T) -
              characteristicInversionSinePrimitive ((a - a) * T) : ℝ) : ℂ))
        atTop
        (nhds (Real.pi : ℂ)) := by
    have h := (Filter.Tendsto.ofReal hdiff).const_mul (2 : ℂ)
    convert h using 1
    norm_num
    ring
  exact hcomplex.congr' (Eventually.of_forall fun T =>
    (characteristicInversionSineKernel_eq_primitive a b a T).symm)

theorem characteristicInversionSineKernelLimit_rightEndpoint_of_dirichlet
    (hlim : characteristicInversionDirichletIntegralLimit)
    {a b : ℝ} (hab : a < b) :
    Tendsto
      (fun T : ℝ => characteristicInversionSineKernel a b b T)
      atTop
      (nhds (Real.pi : ℂ)) := by
  have hAscale :
      Tendsto (fun T : ℝ => (a - b) * T) atTop atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg (sub_neg.mpr hab) tendsto_id
  have hA :
      Tendsto
        (fun T : ℝ =>
          characteristicInversionSinePrimitive ((a - b) * T))
        atTop
        (nhds (-(Real.pi / 2))) :=
    (characteristicInversionSinePrimitive_tendsto_atBot hlim).comp hAscale
  have hzero : characteristicInversionSinePrimitive 0 = 0 := by
    simp [characteristicInversionSinePrimitive]
  have hB :
      Tendsto
        (fun T : ℝ =>
          characteristicInversionSinePrimitive ((b - b) * T))
        atTop
        (nhds 0) := by
    simp [hzero]
  have hdiff :
      Tendsto
        (fun T : ℝ =>
          characteristicInversionSinePrimitive ((b - b) * T) -
            characteristicInversionSinePrimitive ((a - b) * T))
        atTop
        (nhds (Real.pi / 2)) := by
    have h := hB.sub hA
    convert h using 1
    ring_nf
  have hcomplex :
      Tendsto
        (fun T : ℝ =>
          (2 : ℂ) *
            ((characteristicInversionSinePrimitive ((b - b) * T) -
              characteristicInversionSinePrimitive ((a - b) * T) : ℝ) : ℂ))
        atTop
        (nhds (Real.pi : ℂ)) := by
    have h := (Filter.Tendsto.ofReal hdiff).const_mul (2 : ℂ)
    convert h using 1
    norm_num
    ring
  exact hcomplex.congr' (Eventually.of_forall fun T =>
    (characteristicInversionSineKernel_eq_primitive a b b T).symm)

theorem characteristicInversionSineKernelLimit_leftExterior_of_dirichlet
    (hlim : characteristicInversionDirichletIntegralLimit)
    {a b x : ℝ} (hab : a < b) (hx : x < a) :
    Tendsto
      (fun T : ℝ => characteristicInversionSineKernel a b x T)
      atTop
      (nhds (0 : ℂ)) := by
  have hxb : x < b := hx.trans hab
  have hBscale :
      Tendsto (fun T : ℝ => (b - x) * T) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (sub_pos.mpr hxb) tendsto_id
  have hAscale :
      Tendsto (fun T : ℝ => (a - x) * T) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (sub_pos.mpr hx) tendsto_id
  have hB :
      Tendsto
        (fun T : ℝ =>
          characteristicInversionSinePrimitive ((b - x) * T))
        atTop
        (nhds (Real.pi / 2)) :=
    hlim.comp hBscale
  have hA :
      Tendsto
        (fun T : ℝ =>
          characteristicInversionSinePrimitive ((a - x) * T))
        atTop
        (nhds (Real.pi / 2)) :=
    hlim.comp hAscale
  have hdiff :
      Tendsto
        (fun T : ℝ =>
          characteristicInversionSinePrimitive ((b - x) * T) -
            characteristicInversionSinePrimitive ((a - x) * T))
        atTop
        (nhds 0) := by
    have h := hB.sub hA
    convert h using 1
    ring_nf
  have hcomplex :
      Tendsto
        (fun T : ℝ =>
          (2 : ℂ) *
            ((characteristicInversionSinePrimitive ((b - x) * T) -
              characteristicInversionSinePrimitive ((a - x) * T) : ℝ) : ℂ))
        atTop
        (nhds (0 : ℂ)) := by
    have h := (Filter.Tendsto.ofReal hdiff).const_mul (2 : ℂ)
    simpa using h
  exact hcomplex.congr' (Eventually.of_forall fun T =>
    (characteristicInversionSineKernel_eq_primitive a b x T).symm)

theorem characteristicInversionSineKernelLimit_rightExterior_of_dirichlet
    (hlim : characteristicInversionDirichletIntegralLimit)
    {a b x : ℝ} (hab : a < b) (hx : b < x) :
    Tendsto
      (fun T : ℝ => characteristicInversionSineKernel a b x T)
      atTop
      (nhds (0 : ℂ)) := by
  have hax : a < x := hab.trans hx
  have hBscale :
      Tendsto (fun T : ℝ => (b - x) * T) atTop atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg (sub_neg.mpr hx) tendsto_id
  have hAscale :
      Tendsto (fun T : ℝ => (a - x) * T) atTop atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg (sub_neg.mpr hax) tendsto_id
  have hB :
      Tendsto
        (fun T : ℝ =>
          characteristicInversionSinePrimitive ((b - x) * T))
        atTop
        (nhds (-(Real.pi / 2))) :=
    (characteristicInversionSinePrimitive_tendsto_atBot hlim).comp hBscale
  have hA :
      Tendsto
        (fun T : ℝ =>
          characteristicInversionSinePrimitive ((a - x) * T))
        atTop
        (nhds (-(Real.pi / 2))) :=
    (characteristicInversionSinePrimitive_tendsto_atBot hlim).comp hAscale
  have hdiff :
      Tendsto
        (fun T : ℝ =>
          characteristicInversionSinePrimitive ((b - x) * T) -
            characteristicInversionSinePrimitive ((a - x) * T))
        atTop
        (nhds 0) := by
    have h := hB.sub hA
    convert h using 1
    ring_nf
  have hcomplex :
      Tendsto
        (fun T : ℝ =>
          (2 : ℂ) *
            ((characteristicInversionSinePrimitive ((b - x) * T) -
              characteristicInversionSinePrimitive ((a - x) * T) : ℝ) : ℂ))
        atTop
        (nhds (0 : ℂ)) := by
    have h := (Filter.Tendsto.ofReal hdiff).const_mul (2 : ℂ)
    simpa using h
  exact hcomplex.congr' (Eventually.of_forall fun T =>
    (characteristicInversionSineKernel_eq_primitive a b x T).symm)

def characteristicInversionSinePrimitiveBounded : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ v : ℝ, |characteristicInversionSinePrimitive v| ≤ C

theorem characteristicInversionSinePrimitiveBounded_of_dirichlet
    (hlim : characteristicInversionDirichletIntegralLimit) :
    characteristicInversionSinePrimitiveBounded := by
  let G : ℝ → ℝ := fun v => |characteristicInversionSinePrimitive v|
  have hpi_nonneg : 0 ≤ Real.pi / 2 := by positivity
  have htop : Tendsto G atTop (nhds (Real.pi / 2)) := by
    have h := Filter.Tendsto.abs hlim
    simpa [G, characteristicInversionDirichletIntegralLimit,
      abs_of_nonneg hpi_nonneg] using h
  have hbot : Tendsto G atBot (nhds (Real.pi / 2)) := by
    have h := Filter.Tendsto.abs
      (characteristicInversionSinePrimitive_tendsto_atBot hlim)
    have htarget : |-(Real.pi / 2)| = Real.pi / 2 := by
      rw [abs_neg, abs_of_nonneg hpi_nonneg]
    simpa [G, htarget] using h
  have hcocompact : Tendsto G (cocompact ℝ) (nhds (Real.pi / 2)) := by
    rw [cocompact_eq_atBot_atTop]
    exact hbot.sup htop
  have hGcont : Continuous G := characteristicInversionSinePrimitive_continuous.abs
  have hcompact : IsCompact (insert (Real.pi / 2) (Set.range G)) :=
    Filter.Tendsto.isCompact_insert_range_of_cocompact hcocompact hGcont
  have hbounded : Bornology.IsBounded (insert (Real.pi / 2) (Set.range G)) :=
    hcompact.isBounded
  rw [isBounded_iff_forall_norm_le] at hbounded
  rcases hbounded with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro v
  have hv_range : G v ∈ insert (Real.pi / 2) (Set.range G) := by
    exact Or.inr ⟨v, rfl⟩
  have hnorm : ‖G v‖ ≤ C := hC (G v) hv_range
  have hG_nonneg : 0 ≤ G v := abs_nonneg _
  have hG_le_C : G v ≤ C := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hG_nonneg] using hnorm
  exact hG_le_C.trans (le_max_left C 0)

def characteristicInversionDirichletKernelPackage : Prop :=
  characteristicInversionDirichletIntegralLimit ∧
    characteristicInversionSinePrimitiveBounded

theorem characteristicInversionDirichletKernelPackage_of_limit
    (hlim : characteristicInversionDirichletIntegralLimit) :
    characteristicInversionDirichletKernelPackage :=
  ⟨hlim, characteristicInversionSinePrimitiveBounded_of_dirichlet hlim⟩

theorem characteristicInversionSinc_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable Real.sinc volume a b :=
  Real.continuous_sinc.intervalIntegrable a b

def characteristicInversionKernelChangeOfVariables
    (a b x : ℝ) : Prop :=
  ∀ T : ℝ,
    characteristicInversionInnerKernel a b x T =
      characteristicInversionSineKernel a b x T

theorem characteristicInversionKernelChangeOfVariables_of_translated
    (a b x : ℝ) :
    characteristicInversionKernelChangeOfVariables a b x := by
  intro T
  unfold characteristicInversionInnerKernel
  calc
    (∫ t in (-T)..T,
      characteristicInversionMultiplier a b t *
        Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)))
        = ∫ t in (-T)..T,
          (Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (a : ℂ))) -
              Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) - (b : ℂ)))) /
            (Complex.I * (t : ℂ)) := by
            refine intervalIntegral.integral_congr_ae ?_
            have hne0 : ∀ᵐ t : ℝ, t ≠ 0 := by
              rw [MeasureTheory.ae_iff]
              simpa using
                (MeasureTheory.NoAtoms.measure_singleton
                  (μ := volume) (0 : ℝ))
            filter_upwards [hne0] with t ht0 htI
            exact
              characteristicInversionMultiplier_mul_exp_eq_of_ne
                a b x t ht0
    _ = characteristicInversionSineKernel a b x T := by
            rw [
              characteristicInversionTranslatedExpDifference_integral_eq_sineKernel]

def characteristicInversionSineKernelLimit
    (a b x : ℝ) : Prop :=
  Tendsto
    (fun T : ℝ => characteristicInversionSineKernel a b x T)
    atTop
    (nhds (characteristicInversionKernelLimitValue a b x))

theorem characteristicInversionSineKernelLimit_of_dirichlet
    (hlim : characteristicInversionDirichletIntegralLimit)
    {a b x : ℝ} (hab : a < b) :
    characteristicInversionSineKernelLimit a b x := by
  unfold characteristicInversionSineKernelLimit
  by_cases hinside : a < x ∧ x < b
  · simpa [characteristicInversionKernelLimitValue, hinside] using
      characteristicInversionSineKernelLimit_interior_of_dirichlet
        hlim hinside.1 hinside.2
  · by_cases hendpoint : x = a ∨ x = b
    · rcases hendpoint with hxa | hxb
      · subst x
        simpa [characteristicInversionKernelLimitValue, hab, hab.ne'] using
          characteristicInversionSineKernelLimit_leftEndpoint_of_dirichlet
            hlim hab
      · subst x
        simpa [characteristicInversionKernelLimitValue, hab, hab.ne] using
          characteristicInversionSineKernelLimit_rightEndpoint_of_dirichlet
            hlim hab
    · by_cases hxleft : x < a
      · simpa [characteristicInversionKernelLimitValue, hinside, hendpoint] using
          characteristicInversionSineKernelLimit_leftExterior_of_dirichlet
            hlim hab hxleft
      · have hax : a < x := by
          have hle : a ≤ x := le_of_not_gt hxleft
          have hne : a ≠ x := fun h => hendpoint (Or.inl h.symm)
          exact lt_of_le_of_ne hle hne
        have hbx : b < x := by
          by_contra hnot
          have hxb_le : x ≤ b := le_of_not_gt hnot
          have hne : x ≠ b := fun h => hendpoint (Or.inr h)
          have hxb : x < b := lt_of_le_of_ne hxb_le hne
          exact hinside ⟨hax, hxb⟩
        simpa [characteristicInversionKernelLimitValue, hinside, hendpoint] using
          characteristicInversionSineKernelLimit_rightExterior_of_dirichlet
            hlim hab hbx

def characteristicInversionKernelPointwiseLimit
    (a b x : ℝ) : Prop :=
  Tendsto
    (fun T : ℝ => characteristicInversionInnerKernel a b x T)
    atTop
    (nhds (characteristicInversionKernelLimitValue a b x))

def characteristicInversionKernelFromSine
    (a b x : ℝ) : Prop :=
  characteristicInversionKernelChangeOfVariables a b x →
    characteristicInversionSineKernelLimit a b x →
      characteristicInversionKernelPointwiseLimit a b x

theorem characteristicInversionKernelFromSine_of_change
    (a b x : ℝ) :
    characteristicInversionKernelFromSine a b x := by
  intro hchange hsine
  exact hsine.congr' (Filter.Eventually.of_forall fun T => (hchange T).symm)

theorem characteristicInversionInnerKernel_aestronglyMeasurable_of_change
    (μ : Measure ℝ) (a b : ℝ)
    (hchange : ∀ x : ℝ, characteristicInversionKernelChangeOfVariables a b x) :
    ∀ T : ℝ,
      AEStronglyMeasurable
        (fun x : ℝ => characteristicInversionInnerKernel a b x T) μ := by
  intro T
  exact (characteristicInversionSineKernel_aestronglyMeasurable μ a b T).congr
    (Filter.Eventually.of_forall fun x => (hchange x T).symm)

def characteristicInversionKernelDominated
    (a b : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ x T : ℝ, ‖characteristicInversionInnerKernel a b x T‖ ≤ C

theorem characteristicInversionKernelDominated_of_dirichlet
    {a b : ℝ}
    (hlim : characteristicInversionDirichletIntegralLimit)
    (hchange : ∀ x : ℝ, characteristicInversionKernelChangeOfVariables a b x) :
    characteristicInversionKernelDominated a b := by
  rcases characteristicInversionSinePrimitiveBounded_of_dirichlet hlim with
    ⟨C, hC_nonneg, hC⟩
  refine ⟨4 * C, by nlinarith, ?_⟩
  intro x T
  have hB :
      |characteristicInversionSinePrimitive ((b - x) * T)| ≤ C :=
    hC ((b - x) * T)
  have hA :
      |characteristicInversionSinePrimitive ((a - x) * T)| ≤ C :=
    hC ((a - x) * T)
  have hdiff :
      |characteristicInversionSinePrimitive ((b - x) * T) -
          characteristicInversionSinePrimitive ((a - x) * T)| ≤ C + C := by
    calc
      |characteristicInversionSinePrimitive ((b - x) * T) -
          characteristicInversionSinePrimitive ((a - x) * T)|
          ≤ |characteristicInversionSinePrimitive ((b - x) * T)| +
              |characteristicInversionSinePrimitive ((a - x) * T)| :=
            abs_sub _ _
      _ ≤ C + C := add_le_add hB hA
  rw [hchange x T, characteristicInversionSineKernel_eq_primitive]
  have hnormDiff :
      ‖((characteristicInversionSinePrimitive ((b - x) * T) -
          characteristicInversionSinePrimitive ((a - x) * T) : ℝ) : ℂ)‖ =
        |characteristicInversionSinePrimitive ((b - x) * T) -
          characteristicInversionSinePrimitive ((a - x) * T)| := by
    exact RCLike.norm_ofReal
      (characteristicInversionSinePrimitive ((b - x) * T) -
        characteristicInversionSinePrimitive ((a - x) * T))
  calc
    ‖(2 : ℂ) *
        ((characteristicInversionSinePrimitive ((b - x) * T) -
          characteristicInversionSinePrimitive ((a - x) * T) : ℝ) : ℂ)‖
        = ‖(2 : ℂ)‖ *
          ‖((characteristicInversionSinePrimitive ((b - x) * T) -
            characteristicInversionSinePrimitive ((a - x) * T) : ℝ) : ℂ)‖ := by
          rw [norm_mul]
    _ = 2 *
          |characteristicInversionSinePrimitive ((b - x) * T) -
            characteristicInversionSinePrimitive ((a - x) * T)| := by
          rw [hnormDiff]
          norm_num
    _ ≤ 2 * (C + C) := mul_le_mul_of_nonneg_left hdiff (by norm_num)
    _ = 4 * C := by ring
