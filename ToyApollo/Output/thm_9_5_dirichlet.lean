/-
TASK ID: thm_9_5_dirichlet
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

open Filter MeasureTheory Set
open scoped Topology Interval

noncomputable section

theorem characteristicInversionSinMulDiv_integral_eq_sinc
    (c T : ℝ) :
    (∫ t in (0 : ℝ)..T, Real.sin (t * c) / t) =
      ∫ u in (0 : ℝ)..(c * T), Real.sinc u := by
  by_cases hc : c = 0
  · subst c
    simp
  · have hne0 : ∀ᵐ t : ℝ, t ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simpa using
        (MeasureTheory.NoAtoms.measure_singleton (μ := volume) (0 : ℝ))
    calc
      (∫ t in (0 : ℝ)..T, Real.sin (t * c) / t)
          = ∫ t in (0 : ℝ)..T, c * Real.sinc (c * t) := by
              refine intervalIntegral.integral_congr_ae ?_
              filter_upwards [hne0] with t ht0 htI
              have hct : c * t ≠ 0 := mul_ne_zero hc ht0
              rw [Real.sinc_of_ne_zero hct]
              field_simp [hc, ht0]
      _ = c * ∫ t in (0 : ℝ)..T, Real.sinc (c * t) := by
              rw [intervalIntegral.integral_const_mul]
      _ = ∫ u in (0 : ℝ)..(c * T), Real.sinc u := by
              simpa using
                (intervalIntegral.smul_integral_comp_mul_left
                  (fun u : ℝ => Real.sinc u) c (a := (0 : ℝ)) (b := T))

theorem characteristicInversionSinMulDiv_intervalIntegrable
    (c r s : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.sin (t * c) / t) volume r s := by
  by_cases hc : c = 0
  · subst c
    simpa using
      (continuous_const.intervalIntegrable r s :
        IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume r s)
  · have hhelper_cont :
        Continuous (fun t : ℝ => c * Real.sinc (c * t)) := by
      exact
        (Real.continuous_sinc.comp
          (continuous_const.mul continuous_id)).const_mul c
    have hhelper :
        IntervalIntegrable (fun t : ℝ => c * Real.sinc (c * t))
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
    field_simp [hc, ht0]

noncomputable def characteristicInversionSineKernel
    (a b x T : ℝ) : ℂ :=
  (2 : ℂ) *
    ((∫ u in ((a - x) * T)..((b - x) * T), Real.sin u / u : ℝ) : ℂ)

theorem characteristicInversionSinDiv_integral_eq_sinc_integral (r s : ℝ) :
    (∫ u in r..s, Real.sin u / u) =
      (∫ u in r..s, Real.sinc u) := by
  refine intervalIntegral.integral_congr_ae ?_
  have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 0 := by
    rw [ae_iff]
    simp
  exact hne.mono fun u hu _hu_interval => by
    rw [Real.sinc_of_ne_zero hu]

noncomputable def characteristicInversionSinePrimitive (v : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..v, Real.sinc u

theorem characteristicInversionSinePrimitive_continuous :
    Continuous characteristicInversionSinePrimitive := by
  change Continuous (fun v : ℝ => ∫ u in (0 : ℝ)..v, Real.sinc u)
  exact
    (intervalIntegral.differentiable_integral_of_continuous
      (a := (0 : ℝ)) Real.continuous_sinc).continuous

theorem characteristicInversionSinePrimitive_neg (v : ℝ) :
    characteristicInversionSinePrimitive (-v) =
      -characteristicInversionSinePrimitive v := by
  change (∫ u in (0 : ℝ)..(-v), Real.sinc u) =
    -(∫ u in (0 : ℝ)..v, Real.sinc u)
  have hcomp :
      (∫ u in (0 : ℝ)..(-v), Real.sinc (-u)) =
        ∫ u in v..(0 : ℝ), Real.sinc u := by
    simpa using
      (intervalIntegral.integral_comp_neg
        (f := Real.sinc) (a := (0 : ℝ)) (b := -v))
  have hsame :
      (∫ u in (0 : ℝ)..(-v), Real.sinc u) =
        ∫ u in v..(0 : ℝ), Real.sinc u := by
    simpa [Real.sinc_neg] using hcomp
  rw [hsame, intervalIntegral.integral_symm]

def characteristicInversionDirichletIntegralLimit : Prop :=
  Tendsto characteristicInversionSinePrimitive atTop (nhds (Real.pi / 2))

namespace CharacteristicInversionDirichletAux

theorem scratch_inner_dirichlet_laplace_integral (T y : ℝ) :
    (∫ u in (0 : ℝ)..T, Real.exp (-(u * y)) * Real.sin u) =
      (1 - Real.exp (-(T * y)) * (y * Real.sin T + Real.cos T)) /
        (1 + y ^ 2) := by
  let F : ℝ → ℝ := fun u =>
    -Real.exp (-(u * y)) * (y * Real.sin u + Real.cos u) / (1 + y ^ 2)
  have hden : 1 + y ^ 2 ≠ 0 := by positivity
  have hderiv :
      ∀ u : ℝ, HasDerivAt F (Real.exp (-(u * y)) * Real.sin u) u := by
    intro u
    dsimp [F]
    convert
      (((Real.hasDerivAt_exp (-(u * y))).comp u
          (((hasDerivAt_id u).mul_const y).neg)).neg.mul
        (((hasDerivAt_const u y).mul (Real.hasDerivAt_sin u)).add
          (Real.hasDerivAt_cos u))).div_const (1 + y ^ 2)
      using 1
    field_simp [hden]
    simp [Function.comp_apply, mul_comm, mul_assoc]
    ring_nf
  have hint :
      IntervalIntegrable (fun u : ℝ => Real.exp (-(u * y)) * Real.sin u)
        volume (0 : ℝ) T := by
    exact
      (((Real.continuous_exp.comp
        ((continuous_id.mul continuous_const).neg)).mul Real.continuous_sin).intervalIntegrable
          (0 : ℝ) T)
  calc
    (∫ u in (0 : ℝ)..T, Real.exp (-(u * y)) * Real.sin u)
        = F T - F 0 := by
          exact intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun u hu => hderiv u) hint
    _ = (1 - Real.exp (-(T * y)) * (y * Real.sin T + Real.cos T)) /
          (1 + y ^ 2) := by
        simp [F]
        field_simp [hden]
        ring

theorem scratch_integral_exp_neg_mul_Ioi (T : ℝ) (hT : 0 < T) :
    (∫ y : ℝ in Ioi (0 : ℝ), Real.exp (-(T * y))) = T⁻¹ := by
  have hneg : -T < 0 := by linarith
  calc
    (∫ y : ℝ in Ioi (0 : ℝ), Real.exp (-(T * y))) =
        ∫ y : ℝ in Ioi (0 : ℝ), Real.exp ((-T) * y) := by
      congr 1 with y
      ring_nf
    _ = T⁻¹ := by
      have h := integral_exp_mul_Ioi (a := -T) hneg (c := (0 : ℝ))
      simpa [hT.ne', div_eq_mul_inv] using h

theorem scratch_laplace_sinc (u : ℝ) (hu : 0 < u) :
    (∫ y : ℝ in Ioi (0 : ℝ), Real.exp (-(u * y)) * Real.sin u) =
      Real.sinc u := by
  calc
    (∫ y : ℝ in Ioi (0 : ℝ), Real.exp (-(u * y)) * Real.sin u)
        = (∫ y : ℝ in Ioi (0 : ℝ), Real.exp (-(u * y))) * Real.sin u := by
          rw [MeasureTheory.integral_mul_const]
    _ = u⁻¹ * Real.sin u := by
          rw [scratch_integral_exp_neg_mul_Ioi u hu]
    _ = Real.sinc u := by
          rw [Real.sinc_of_ne_zero hu.ne']
          ring

theorem scratch_sinc_as_laplace_interval (T : ℝ) (hT : 0 < T) :
    (∫ u in (0 : ℝ)..T, Real.sinc u) =
      ∫ u : ℝ in Ioc (0 : ℝ) T,
        ∫ y : ℝ in Ioi (0 : ℝ), Real.exp (-(u * y)) * Real.sin u := by
  rw [intervalIntegral.integral_of_le hT.le]
  refine (setIntegral_congr_fun measurableSet_Ioc ?_).symm
  intro u hu
  exact scratch_laplace_sinc u (Set.mem_Ioc.mp hu).1

theorem scratch_laplace_kernel_integrableOn (T : ℝ) (_hT : 0 < T) :
    IntegrableOn
      (fun p : ℝ × ℝ => Real.exp (-(p.1 * p.2)) * Real.sin p.1)
      (Ioc (0 : ℝ) T ×ˢ Ioi (0 : ℝ)) (volume.prod volume) := by
  let f : ℝ × ℝ → ℝ := fun p => Real.exp (-(p.1 * p.2)) * Real.sin p.1
  rw [IntegrableOn, ← Measure.prod_restrict]
  have hsm : StronglyMeasurable f := by
    have hcont : Continuous f := by
      dsimp [f]
      fun_prop
    exact hcont.stronglyMeasurable
  refine ⟨hsm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_prod_iff hsm]
  constructor
  · filter_upwards [self_mem_ae_restrict (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) T))]
      with u hu
    have hu_pos : 0 < u := (Set.mem_Ioc.mp hu).1
    have hneg : -u < 0 := by linarith
    have hbase :
        IntegrableOn (fun y : ℝ => Real.exp (-(u * y))) (Ioi (0 : ℝ)) volume := by
      have h := integrableOn_exp_mul_Ioi (a := -u) hneg (c := (0 : ℝ))
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    rw [IntegrableOn] at hbase
    have hmul := hbase.mul_const (Real.sin u)
    simpa [f, mul_comm, mul_left_comm, mul_assoc] using hmul.hasFiniteIntegral
  · have hnorm_sm : StronglyMeasurable (fun p : ℝ × ℝ => ‖f p‖) := hsm.norm
    have hinner_sm :
        StronglyMeasurable
          (fun u : ℝ => ∫ y : ℝ, ‖f (u, y)‖ ∂(volume.restrict (Ioi (0 : ℝ)))) :=
      hnorm_sm.integral_prod_right'
    have hconst :
        Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc (0 : ℝ) T)) := by
      simpa [IntegrableOn] using
        (integrableOn_const
          (s := Ioc (0 : ℝ) T) (μ := volume) (C := (1 : ℝ))
          (measure_Ioc_lt_top.ne))
    have hinner_int :
        Integrable
          (fun u : ℝ => ∫ y : ℝ, ‖f (u, y)‖ ∂(volume.restrict (Ioi (0 : ℝ))))
          (volume.restrict (Ioc (0 : ℝ) T)) := by
      refine hconst.mono hinner_sm.aestronglyMeasurable ?_
      rw [ae_restrict_iff' (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) T))]
      refine Eventually.of_forall ?_
      intro u hu
      have hu_pos : 0 < u := (Set.mem_Ioc.mp hu).1
      have hnorm_eq :
          (fun y : ℝ => ‖f (u, y)‖) =
            fun y : ℝ => |Real.sin u| * Real.exp (-(u * y)) := by
        funext y
        dsimp [f]
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        ring
      have hinner_eq :
          (∫ y : ℝ, ‖f (u, y)‖ ∂(volume.restrict (Ioi (0 : ℝ)))) =
            |Real.sin u| * u⁻¹ := by
        calc
          (∫ y : ℝ, ‖f (u, y)‖ ∂(volume.restrict (Ioi (0 : ℝ))))
              = ∫ y : ℝ in Ioi (0 : ℝ), |Real.sin u| * Real.exp (-(u * y)) := by
                rw [hnorm_eq]
          _ = |Real.sin u| *
                (∫ y : ℝ in Ioi (0 : ℝ), Real.exp (-(u * y))) := by
                rw [MeasureTheory.integral_const_mul]
          _ = |Real.sin u| * u⁻¹ := by
                rw [scratch_integral_exp_neg_mul_Ioi u hu_pos]
      have hsin : |Real.sin u| ≤ u := by
        simpa [abs_of_pos hu_pos] using (Real.abs_sin_le_abs (x := u))
      have hle : |Real.sin u| * u⁻¹ ≤ 1 := by
        rw [mul_inv_le_iff₀ hu_pos]
        simpa using hsin
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      rw [hinner_eq]
      have hprod_nonneg : 0 ≤ |Real.sin u| * u⁻¹ := by positivity
      simpa [abs_of_nonneg hprod_nonneg] using hle
    simpa using hinner_int.hasFiniteIntegral

theorem scratch_sinc_laplace_fubini (T : ℝ) (hT : 0 < T) :
    (∫ u in (0 : ℝ)..T, Real.sinc u) =
      ∫ y : ℝ in Ioi (0 : ℝ),
        ∫ u in (0 : ℝ)..T, Real.exp (-(u * y)) * Real.sin u := by
  let f : ℝ → ℝ → ℝ := fun u y => Real.exp (-(u * y)) * Real.sin u
  have hstart := scratch_sinc_as_laplace_interval T hT
  have hf_on := scratch_laplace_kernel_integrableOn T hT
  have hf :
      Integrable (fun p : ℝ × ℝ => f p.1 p.2)
        ((volume.restrict (Ioc (0 : ℝ) T)).prod
          (volume.restrict (Ioi (0 : ℝ)))) := by
    have hf_restrict :
        Integrable (fun p : ℝ × ℝ => Real.exp (-(p.1 * p.2)) * Real.sin p.1)
          ((volume.prod volume).restrict (Ioc (0 : ℝ) T ×ˢ Ioi (0 : ℝ))) := by
      simpa [IntegrableOn] using hf_on
    rw [← Measure.prod_restrict] at hf_restrict
    simpa [f] using hf_restrict
  have hswap :
      (∫ u : ℝ in Ioc (0 : ℝ) T,
          ∫ y : ℝ in Ioi (0 : ℝ), f u y) =
        ∫ y : ℝ in Ioi (0 : ℝ),
          ∫ u : ℝ in Ioc (0 : ℝ) T, f u y := by
    simpa [f] using
      (integral_integral_swap
        (μ := volume.restrict (Ioc (0 : ℝ) T))
        (ν := volume.restrict (Ioi (0 : ℝ)))
        (f := f) hf)
  have hright :
      (∫ y : ℝ in Ioi (0 : ℝ),
          ∫ u : ℝ in Ioc (0 : ℝ) T, f u y) =
        ∫ y : ℝ in Ioi (0 : ℝ),
          ∫ u in (0 : ℝ)..T, f u y := by
    exact setIntegral_congr_fun measurableSet_Ioi fun y _hy => by
      rw [intervalIntegral.integral_of_le hT.le]
  calc
    (∫ u in (0 : ℝ)..T, Real.sinc u)
        = ∫ u : ℝ in Ioc (0 : ℝ) T,
            ∫ y : ℝ in Ioi (0 : ℝ), f u y := by
          simpa [f] using hstart
    _ = ∫ y : ℝ in Ioi (0 : ℝ),
          ∫ u : ℝ in Ioc (0 : ℝ) T, f u y := hswap
    _ = ∫ y : ℝ in Ioi (0 : ℝ),
          ∫ u in (0 : ℝ)..T, f u y := hright

theorem scratch_sinc_laplace_integral_formula (T : ℝ) (hT : 0 < T) :
    (∫ u in (0 : ℝ)..T, Real.sinc u) =
      ∫ y : ℝ in Ioi (0 : ℝ),
        (1 - Real.exp (-(T * y)) * (y * Real.sin T + Real.cos T)) /
          (1 + y ^ 2) := by
  rw [scratch_sinc_laplace_fubini T hT]
  exact setIntegral_congr_fun measurableSet_Ioi fun y _hy =>
    scratch_inner_dirichlet_laplace_integral T y

theorem scratch_dirichlet_remainder_integrand_bound
    (T y : ℝ) (_hT : 0 < T) (hy : y ∈ Ioi (0 : ℝ)) :
    |Real.exp (-(T * y)) * (y * Real.sin T + Real.cos T) / (1 + y ^ 2)|
      ≤ 2 * Real.exp (-(T * y)) := by
  have hy_pos : 0 < y := hy
  have hy_nonneg : 0 ≤ y := le_of_lt hy_pos
  have hexp_nonneg : 0 ≤ Real.exp (-(T * y)) := (Real.exp_pos _).le
  have hden_pos : 0 < 1 + y ^ 2 := by positivity
  have htrig :
      |y * Real.sin T + Real.cos T| ≤ y + 1 := by
    calc
      |y * Real.sin T + Real.cos T|
          ≤ |y * Real.sin T| + |Real.cos T| := abs_add_le _ _
      _ = y * |Real.sin T| + |Real.cos T| := by
        rw [abs_mul, abs_of_nonneg hy_nonneg]
      _ ≤ y * 1 + 1 := by
        gcongr
        exact Real.abs_sin_le_one T
        exact Real.abs_cos_le_one T
      _ = y + 1 := by ring
  have hpoly : y + 1 ≤ 2 * (1 + y ^ 2) := by
    nlinarith [sq_nonneg (y - 1)]
  have hratio :
      |y * Real.sin T + Real.cos T| / (1 + y ^ 2) ≤ 2 := by
    rw [div_le_iff₀ hden_pos]
    exact htrig.trans hpoly
  calc
    |Real.exp (-(T * y)) * (y * Real.sin T + Real.cos T) / (1 + y ^ 2)|
        = Real.exp (-(T * y)) *
            (|y * Real.sin T + Real.cos T| / (1 + y ^ 2)) := by
          rw [abs_div, abs_mul, abs_of_nonneg hexp_nonneg, abs_of_pos hden_pos]
          ring
    _ ≤ Real.exp (-(T * y)) * 2 := by
      exact mul_le_mul_of_nonneg_left hratio hexp_nonneg
    _ = 2 * Real.exp (-(T * y)) := by ring

theorem scratch_dirichlet_remainder_integrableOn (T : ℝ) (hT : 0 < T) :
    IntegrableOn
      (fun y : ℝ =>
        Real.exp (-(T * y)) * (y * Real.sin T + Real.cos T) / (1 + y ^ 2))
      (Ioi (0 : ℝ)) volume := by
  let r : ℝ → ℝ := fun y =>
    Real.exp (-(T * y)) * (y * Real.sin T + Real.cos T) / (1 + y ^ 2)
  let g : ℝ → ℝ := fun y => 2 * Real.exp (-(T * y))
  have hneg : -T < 0 := by linarith
  have hg_int : IntegrableOn g (Ioi (0 : ℝ)) volume := by
    have hbase :
        IntegrableOn (fun y : ℝ => Real.exp ((-T) * y)) (Ioi (0 : ℝ)) volume :=
      integrableOn_exp_mul_Ioi hneg (0 : ℝ)
    have hbase' :
        IntegrableOn (fun y : ℝ => Real.exp (-(T * y))) (Ioi (0 : ℝ)) volume := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hbase
    rw [IntegrableOn] at hbase' ⊢
    simpa [g] using hbase'.const_mul (2 : ℝ)
  have hr_aesm : AEStronglyMeasurable r (volume.restrict (Ioi (0 : ℝ))) := by
    have hcont : Continuous r := by
      dsimp [r]
      exact
        ((Real.continuous_exp.comp
          ((continuous_const.mul continuous_id).neg)).mul
            ((continuous_id.mul continuous_const).add continuous_const)).div
          ((continuous_const.add (continuous_id.pow 2)))
          (fun y => by positivity)
    exact hcont.aestronglyMeasurable
  rw [IntegrableOn] at hg_int ⊢
  refine hg_int.mono hr_aesm ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall ?_
  intro y hy
  have hb := scratch_dirichlet_remainder_integrand_bound T y hT hy
  change |r y| ≤ |g y|
  have hg_abs : |g y| = 2 * Real.exp (-(T * y)) := by
    dsimp [g]
    exact abs_of_nonneg (by positivity)
  rw [hg_abs]
  dsimp [r]
  exact hb

theorem scratch_dirichlet_remainder_bound (T : ℝ) (hT : 0 < T) :
    |∫ y : ℝ in Ioi (0 : ℝ),
        Real.exp (-(T * y)) * (y * Real.sin T + Real.cos T) / (1 + y ^ 2)|
      ≤ 2 * T⁻¹ := by
  let r : ℝ → ℝ := fun y =>
    Real.exp (-(T * y)) * (y * Real.sin T + Real.cos T) / (1 + y ^ 2)
  let g : ℝ → ℝ := fun y => 2 * Real.exp (-(T * y))
  have hneg : -T < 0 := by linarith
  have hg_int : IntegrableOn g (Ioi (0 : ℝ)) volume := by
    have hbase :
        IntegrableOn (fun y : ℝ => Real.exp ((-T) * y)) (Ioi (0 : ℝ)) volume :=
      integrableOn_exp_mul_Ioi hneg (0 : ℝ)
    have hbase' :
        IntegrableOn (fun y : ℝ => Real.exp (-(T * y))) (Ioi (0 : ℝ)) volume := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hbase
    rw [IntegrableOn] at hbase' ⊢
    simpa [g] using hbase'.const_mul (2 : ℝ)
  have hr_aesm : AEStronglyMeasurable r (volume.restrict (Ioi (0 : ℝ))) := by
    have hcont : Continuous r := by
      dsimp [r]
      exact
        ((Real.continuous_exp.comp
          ((continuous_const.mul continuous_id).neg)).mul
            ((continuous_id.mul continuous_const).add continuous_const)).div
          ((continuous_const.add (continuous_id.pow 2)))
          (fun y => by positivity)
    exact hcont.aestronglyMeasurable
  have hr_int : IntegrableOn r (Ioi (0 : ℝ)) volume := by
    rw [IntegrableOn] at hg_int ⊢
    refine hg_int.mono hr_aesm ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall ?_
    intro y hy
    have hb := scratch_dirichlet_remainder_integrand_bound T y hT hy
    change |r y| ≤ |g y|
    have hg_abs : |g y| = 2 * Real.exp (-(T * y)) := by
      dsimp [g]
      exact abs_of_nonneg (by positivity)
    rw [hg_abs]
    dsimp [r]
    exact hb
  have hr_abs_int : IntegrableOn (fun y : ℝ => |r y|) (Ioi (0 : ℝ)) volume := by
    rw [IntegrableOn] at hr_int ⊢
    simpa [Real.norm_eq_abs] using hr_int.norm
  have habs :
      |∫ y : ℝ in Ioi (0 : ℝ), r y| ≤
        ∫ y : ℝ in Ioi (0 : ℝ), |r y| := by
    simpa using
      (MeasureTheory.abs_integral_le_integral_abs
        (μ := volume.restrict (Ioi (0 : ℝ))) (f := r))
  have hmono :
      (∫ y : ℝ in Ioi (0 : ℝ), |r y|) ≤
        ∫ y : ℝ in Ioi (0 : ℝ), g y := by
    exact
      setIntegral_mono_on hr_abs_int hg_int measurableSet_Ioi
        (fun y hy => by
          simpa [r, g] using scratch_dirichlet_remainder_integrand_bound T y hT hy)
  have hg_value :
      (∫ y : ℝ in Ioi (0 : ℝ), g y) = 2 * T⁻¹ := by
    change (∫ y : ℝ, 2 * Real.exp (-(T * y)) ∂volume.restrict (Ioi (0 : ℝ))) =
      2 * T⁻¹
    rw [MeasureTheory.integral_const_mul]
    change 2 * (∫ y : ℝ in Ioi (0 : ℝ), Real.exp (-(T * y))) = 2 * T⁻¹
    rw [scratch_integral_exp_neg_mul_Ioi T hT]
  calc
    |∫ y : ℝ in Ioi (0 : ℝ),
        Real.exp (-(T * y)) * (y * Real.sin T + Real.cos T) / (1 + y ^ 2)|
        = |∫ y : ℝ in Ioi (0 : ℝ), r y| := by rfl
    _ ≤ ∫ y : ℝ in Ioi (0 : ℝ), |r y| := habs
    _ ≤ ∫ y : ℝ in Ioi (0 : ℝ), g y := hmono
    _ = 2 * T⁻¹ := hg_value

theorem scratch_sinc_error_bound (T : ℝ) (hT : 0 < T) :
    |(∫ u in (0 : ℝ)..T, Real.sinc u) - Real.pi / 2| ≤ 2 * T⁻¹ := by
  let main : ℝ → ℝ := fun y => (1 + y ^ 2)⁻¹
  let rem : ℝ → ℝ := fun y =>
    Real.exp (-(T * y)) * (y * Real.sin T + Real.cos T) / (1 + y ^ 2)
  let form : ℝ → ℝ := fun y =>
    (1 - Real.exp (-(T * y)) * (y * Real.sin T + Real.cos T)) / (1 + y ^ 2)
  have hform_point : EqOn form (fun y => main y - rem y) (Ioi (0 : ℝ)) := by
    intro y _hy
    dsimp [form, main, rem]
    have hden : 1 + y ^ 2 ≠ 0 := by positivity
    field_simp [hden]
  have hform_eq :
      (∫ y : ℝ in Ioi (0 : ℝ), form y) =
        ∫ y : ℝ in Ioi (0 : ℝ), main y - rem y :=
    setIntegral_congr_fun measurableSet_Ioi hform_point
  have hmain_int :
      Integrable (fun y : ℝ => main y) (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [IntegrableOn, main] using
      (integrable_inv_one_add_sq.integrableOn (s := Ioi (0 : ℝ)))
  have hrem_int :
      Integrable (fun y : ℝ => rem y) (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [IntegrableOn, rem] using
      (scratch_dirichlet_remainder_integrableOn T hT)
  have hsub :
      (∫ y : ℝ in Ioi (0 : ℝ), main y - rem y) =
        (∫ y : ℝ in Ioi (0 : ℝ), main y) -
          ∫ y : ℝ in Ioi (0 : ℝ), rem y := by
    simpa using (integral_sub hmain_int hrem_int)
  have hmain_value :
      (∫ y : ℝ in Ioi (0 : ℝ), main y) = Real.pi / 2 := by
    simpa [main] using (integral_Ioi_inv_one_add_sq (i := (0 : ℝ)))
  have hS_eq :
      (∫ u in (0 : ℝ)..T, Real.sinc u) - Real.pi / 2 =
        -(∫ y : ℝ in Ioi (0 : ℝ), rem y) := by
    rw [scratch_sinc_laplace_integral_formula T hT]
    change (∫ y : ℝ in Ioi (0 : ℝ), form y) - Real.pi / 2 =
      -(∫ y : ℝ in Ioi (0 : ℝ), rem y)
    rw [hform_eq, hsub, hmain_value]
    ring
  calc
    |(∫ u in (0 : ℝ)..T, Real.sinc u) - Real.pi / 2|
        = |∫ y : ℝ in Ioi (0 : ℝ), rem y| := by
          rw [hS_eq, abs_neg]
    _ ≤ 2 * T⁻¹ := by
          simpa [rem] using scratch_dirichlet_remainder_bound T hT

theorem scratch_sinc_tendsto :
    Tendsto (fun T : ℝ => ∫ u in (0 : ℝ)..T, Real.sinc u)
      atTop (nhds (Real.pi / 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun T : ℝ => (2 : ℝ) * T⁻¹)
    (Eventually.of_forall fun T => norm_nonneg _) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    simpa [Real.norm_eq_abs] using scratch_sinc_error_bound T hT
  · have hmul :
        Tendsto (fun T : ℝ => (2 : ℝ) * T⁻¹) atTop (nhds (2 * 0)) :=
      tendsto_const_nhds.mul tendsto_inv_atTop_zero
    simpa using hmul

end CharacteristicInversionDirichletAux

theorem characteristicInversionDirichletIntegralLimit_proof :
    characteristicInversionDirichletIntegralLimit := by
  simpa [characteristicInversionDirichletIntegralLimit,
    characteristicInversionSinePrimitive] using
    CharacteristicInversionDirichletAux.scratch_sinc_tendsto

theorem characteristicInversionSinePrimitive_tendsto_atBot
    (hlim : characteristicInversionDirichletIntegralLimit) :
    Tendsto characteristicInversionSinePrimitive atBot
      (nhds (-(Real.pi / 2))) := by
  have hneg :
      Tendsto
        (fun v : ℝ => characteristicInversionSinePrimitive (-v))
        atBot
        (nhds (Real.pi / 2)) :=
    hlim.comp tendsto_neg_atBot_atTop
  have h := hneg.neg
  exact h.congr' (Eventually.of_forall fun v => by
    rw [characteristicInversionSinePrimitive_neg, neg_neg])

theorem characteristicInversionSinePrimitive_integral (r s : ℝ) :
    (∫ u in r..s, Real.sinc u) =
      characteristicInversionSinePrimitive s -
        characteristicInversionSinePrimitive r := by
  change (∫ u in r..s, Real.sinc u) =
    (fun v : ℝ => ∫ u in (0 : ℝ)..v, Real.sinc u) s -
      (fun v : ℝ => ∫ u in (0 : ℝ)..v, Real.sinc u) r
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun v : ℝ => ∫ u in (0 : ℝ)..v, Real.sinc u)
    (f' := Real.sinc) ?_ (Real.continuous_sinc.intervalIntegrable r s)
  intro x _hx
  exact intervalIntegral.integral_hasDerivAt_right
    (Real.continuous_sinc.intervalIntegrable 0 x)
    (Real.continuous_sinc.stronglyMeasurableAtFilter _ _)
    Real.continuous_sinc.continuousAt

theorem characteristicInversionSinMulDiv_integral_symm_eq_primitive
    (c T : ℝ) :
    (∫ t in (-T)..T, Real.sin (t * c) / t) =
      2 * characteristicInversionSinePrimitive (c * T) := by
  by_cases hc : c = 0
  · subst c
    simp [characteristicInversionSinePrimitive]
  · have hne0 : ∀ᵐ t : ℝ, t ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simpa using
        (MeasureTheory.NoAtoms.measure_singleton (μ := volume) (0 : ℝ))
    calc
      (∫ t in (-T)..T, Real.sin (t * c) / t)
          = ∫ t in (-T)..T, c * Real.sinc (c * t) := by
              refine intervalIntegral.integral_congr_ae ?_
              filter_upwards [hne0] with t ht0 htI
              have hct : c * t ≠ 0 := mul_ne_zero hc ht0
              rw [Real.sinc_of_ne_zero hct]
              field_simp [hc, ht0]
      _ = c * ∫ t in (-T)..T, Real.sinc (c * t) := by
              rw [intervalIntegral.integral_const_mul]
      _ = ∫ u in (c * (-T))..(c * T), Real.sinc u := by
              simpa using
                (intervalIntegral.smul_integral_comp_mul_left
                  (fun u : ℝ => Real.sinc u) c (a := (-T)) (b := T))
      _ = characteristicInversionSinePrimitive (c * T) -
            characteristicInversionSinePrimitive (c * (-T)) := by
              rw [characteristicInversionSinePrimitive_integral]
      _ = 2 * characteristicInversionSinePrimitive (c * T) := by
              have harg : c * (-T) = -(c * T) := by ring
              rw [harg, characteristicInversionSinePrimitive_neg]
              ring

theorem characteristicInversionRealSineTerm_integral_eq_primitive
    (a b x T : ℝ) :
    (∫ t in (-T)..T,
      (Real.sin (t * (x - a)) - Real.sin (t * (x - b))) / t) =
      2 * (characteristicInversionSinePrimitive ((b - x) * T) -
        characteristicInversionSinePrimitive ((a - x) * T)) := by
  have hsplit :
      (∫ t in (-T)..T,
        (Real.sin (t * (x - a)) - Real.sin (t * (x - b))) / t) =
        (∫ t in (-T)..T, Real.sin (t * (x - a)) / t) -
          ∫ t in (-T)..T, Real.sin (t * (x - b)) / t := by
    calc
      (∫ t in (-T)..T,
        (Real.sin (t * (x - a)) - Real.sin (t * (x - b))) / t)
          = ∫ t in (-T)..T,
              Real.sin (t * (x - a)) / t -
                Real.sin (t * (x - b)) / t := by
              apply intervalIntegral.integral_congr
              intro t ht
              by_cases ht0 : t = 0
              · subst t
                simp
              · field_simp [ht0]
      _ = (∫ t in (-T)..T, Real.sin (t * (x - a)) / t) -
          ∫ t in (-T)..T, Real.sin (t * (x - b)) / t := by
            rw [intervalIntegral.integral_sub]
            · exact
                characteristicInversionSinMulDiv_intervalIntegrable
                  (x - a) (-T) T
            · exact
                characteristicInversionSinMulDiv_intervalIntegrable
                  (x - b) (-T) T
  rw [hsplit, characteristicInversionSinMulDiv_integral_symm_eq_primitive,
    characteristicInversionSinMulDiv_integral_symm_eq_primitive]
  rw [show (x - a) * T = -((a - x) * T) by ring,
    show (x - b) * T = -((b - x) * T) by ring]
  rw [characteristicInversionSinePrimitive_neg,
    characteristicInversionSinePrimitive_neg]
  ring

theorem characteristicInversionSineKernel_eq_primitive
    (a b x T : ℝ) :
    characteristicInversionSineKernel a b x T =
      (2 : ℂ) *
        ((characteristicInversionSinePrimitive ((b - x) * T) -
          characteristicInversionSinePrimitive ((a - x) * T) : ℝ) : ℂ) := by
  rw [characteristicInversionSineKernel,
    characteristicInversionSinDiv_integral_eq_sinc_integral,
    characteristicInversionSinePrimitive_integral]
