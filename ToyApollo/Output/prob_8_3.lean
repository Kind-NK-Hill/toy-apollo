/-
TASK ID: prob_8_3
TYPE: Problem
SOURCE PLAN: 35_chap8_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_8_5
import ToyApollo.Output.thm_8_6

open MeasureTheory Set Real
open TVCore

noncomputable section

def exponentialPdf (la : ℝ) (x : ℝ) : ℝ :=
  if 0 < x then la * Real.exp (-(la * x)) else 0

def Exponential (la : ℝ) : Measure ℝ :=
  TVCore.densityMeasure (exponentialPdf la)

lemma totalVariationDistance_self {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) :
    totalVariationDistance P P = 0 := by
  unfold totalVariationDistance
  have hset :
      {d : ℝ | ∃ A : Set Ω, MeasurableSet A ∧ d = |P.real A - P.real A|} = {0} := by
    ext d
    constructor
    · rintro ⟨A, hA, rfl⟩
      simp
    · intro hd
      rw [Set.mem_singleton_iff] at hd
      subst d
      exact ⟨∅, MeasurableSet.empty, by simp⟩
  rw [hset]
  simp

lemma totalVariationDistance_comm {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) :
    totalVariationDistance P Q = totalVariationDistance Q P := by
  unfold totalVariationDistance
  congr 1
  ext d
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, hA, by rw [abs_sub_comm]⟩
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, hA, by rw [abs_sub_comm]⟩

lemma exponentialPdf_nonneg (la : ℝ) (hla : 0 < la) (x : ℝ) :
    0 ≤ exponentialPdf la x := by
  simp only [exponentialPdf]
  split_ifs with h
  · exact mul_nonneg (le_of_lt hla) (exp_nonneg _)
  · exact le_refl 0

lemma exponentialPdf_measurable (la : ℝ) : Measurable (exponentialPdf la) := by
  exact Measurable.ite measurableSet_Ioi
    (measurable_const.mul
      (Real.continuous_exp.measurable.comp
        (measurable_neg.comp (measurable_const.mul measurable_id'))))
    measurable_const

lemma exponentialPdf_integral (la : ℝ) (hla : 0 < la) :
    ∫ x, exponentialPdf la x = 1 := by
  erw [MeasureTheory.integral_indicator measurableSet_Ioi]
  have := integral_exp_neg_mul_rpow zero_lt_one hla
  simp_all +decide [Real.rpow_neg_one, mul_comm, MeasureTheory.integral_const_mul]
  norm_num [hla.ne']

lemma exponentialPdf_integrable (la : ℝ) (hla : 0 < la) :
    Integrable (exponentialPdf la) volume := by
  refine' MeasureTheory.integrable_of_integral_eq_one _
  exact exponentialPdf_integral la hla

lemma intervalIntegrable_exp_density {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) :
    IntervalIntegrable (fun x => r * Real.exp (-(r * x))) volume 0 c := by
  rw [intervalIntegrable_iff]
  have hIntOn : IntegrableOn (fun x => Real.exp (-(r * x))) (Set.Ioc 0 c) volume :=
    ProbabilityTheory.exp_neg_integrableOn_Ioc (b := r) (x := c) hr
  have hIntOn2 : IntegrableOn (fun x => r * Real.exp (-(r * x))) (Set.Ioc 0 c) volume :=
    hIntOn.const_mul r
  simpa [Set.uIoc_of_le hc] using hIntOn2

lemma integral_exp_density_interval {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) :
    ∫ x in 0..c, r * Real.exp (-(r * x)) = 1 - Real.exp (-(r * c)) := by
  have hcont : ContinuousOn (fun a => -Real.exp (-(r * a))) (Set.Icc 0 c) := by
    exact (Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)).neg.continuousOn
  have hderiv : ∀ x ∈ Set.Ioo 0 c,
      HasDerivWithinAt (fun a => -Real.exp (-(r * a)))
        (r * Real.exp (-(r * x))) (Set.Ioi x) x := by
    intro x hx
    exact (ProbabilityTheory.hasDerivAt_neg_exp_mul_exp (r := r) (x := x)).hasDerivWithinAt
  have hcalc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    (E := ℝ) (a := 0) (b := c)
    (f := fun a => -Real.exp (-(r * a)))
    (f' := fun a => r * Real.exp (-(r * a)))
    hc hcont hderiv (intervalIntegrable_exp_density hr hc)
  calc
    ∫ x in 0..c, r * Real.exp (-(r * x)) = -Real.exp (-(r * c)) + 1 := by
      simpa using hcalc
    _ = 1 - Real.exp (-(r * c)) := by ring

lemma integral_exp_density_Ioc {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) :
    ∫ x in Set.Ioc 0 c, r * Real.exp (-(r * x)) =
      1 - Real.exp (-(r * c)) := by
  rw [← intervalIntegral.integral_of_le hc]
  exact integral_exp_density_interval hr hc

lemma integral_exponentialPdf_Ioo {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c) :
    ∫ x in Set.Ioo 0 c, exponentialPdf r x = 1 - Real.exp (-(r * c)) := by
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
  convert integral_exp_density_Ioc (r := r) (c := c) hr hc using 1
  refine setIntegral_congr_fun measurableSet_Ioc ?_
  intro x hx
  simp [exponentialPdf, hx.1]

lemma cross_pos_of_gt {la mu : ℝ} (_hla : 0 < la) (hmu : 0 < mu) (hgt : mu < la) :
    0 < Real.log (la / mu) / (la - mu) := by
  have hdpos : 0 < la - mu := sub_pos.mpr hgt
  have hratio_gt_one : 1 < la / mu := by
    rw [one_lt_div hmu]
    exact hgt
  exact div_pos (Real.log_pos hratio_gt_one) hdpos

lemma cross_swap {la mu : ℝ} (hla : 0 < la) (hmu : 0 < mu) (hne : la ≠ mu) :
    Real.log (mu / la) / (mu - la) =
      Real.log (la / mu) / (la - mu) := by
  have hlog : Real.log (mu / la) = - Real.log (la / mu) := by
    have hratio : mu / la = (la / mu)⁻¹ := by
      field_simp [hla.ne', hmu.ne']
    rw [hratio, Real.log_inv]
  rw [hlog]
  have hden1 : mu - la = -(la - mu) := by ring
  rw [hden1]
  field_simp [sub_ne_zero.mpr hne]

lemma abs_exp_cross_of_gt {la mu c : ℝ} (hgt : mu < la) (hc : 0 < c) :
    |Real.exp (-(la * c)) - Real.exp (-(mu * c))| =
      Real.exp (-(mu * c)) - Real.exp (-(la * c)) := by
  have hmul : mu * c < la * c := mul_lt_mul_of_pos_right hgt hc
  have hneg : -(la * c) < -(mu * c) := by linarith
  have hexp : Real.exp (-(la * c)) < Real.exp (-(mu * c)) :=
    Real.exp_lt_exp.mpr hneg
  rw [abs_of_neg (sub_neg.mpr hexp)]
  ring

lemma exp_density_gt_of_lt_cross {la mu x : ℝ}
    (hla : 0 < la) (hmu : 0 < mu) (hgt : mu < la)
    (hxc : x < Real.log (la / mu) / (la - mu)) :
    mu * Real.exp (-(mu * x)) < la * Real.exp (-(la * x)) := by
  have hdpos : 0 < la - mu := sub_pos.mpr hgt
  have hratio_pos : 0 < la / mu := div_pos hla hmu
  have hlog : (la - mu) * x < Real.log (la / mu) := by
    have hmul := mul_lt_mul_of_pos_left hxc hdpos
    rwa [mul_div_cancel₀ _ hdpos.ne'] at hmul
  have hexp : Real.exp ((la - mu) * x) < la / mu := by
    exact (Real.lt_log_iff_exp_lt hratio_pos).mp hlog
  have hposmul : 0 < mu * Real.exp (-(la * x)) := mul_pos hmu (Real.exp_pos _)
  have hmul := mul_lt_mul_of_pos_left hexp hposmul
  calc
    mu * Real.exp (-(mu * x))
        = mu * (Real.exp (-(la * x)) * Real.exp ((la - mu) * x)) := by
            rw [← Real.exp_add]
            congr 2
            ring
    _ = (mu * Real.exp (-(la * x))) * Real.exp ((la - mu) * x) := by ring
    _ < (mu * Real.exp (-(la * x))) * (la / mu) := hmul
    _ = la * Real.exp (-(la * x)) := by field_simp [hmu.ne']

lemma exp_density_lt_of_cross_lt {la mu x : ℝ}
    (hla : 0 < la) (hmu : 0 < mu) (hgt : mu < la)
    (hxc : Real.log (la / mu) / (la - mu) < x) :
    la * Real.exp (-(la * x)) < mu * Real.exp (-(mu * x)) := by
  have hdpos : 0 < la - mu := sub_pos.mpr hgt
  have hratio_pos : 0 < la / mu := div_pos hla hmu
  have hlog : Real.log (la / mu) < (la - mu) * x := by
    have hmul := mul_lt_mul_of_pos_left hxc hdpos
    rwa [mul_div_cancel₀ _ hdpos.ne'] at hmul
  have hexp : la / mu < Real.exp ((la - mu) * x) := by
    exact (Real.log_lt_iff_lt_exp hratio_pos).mp hlog
  have hposmul : 0 < mu * Real.exp (-(la * x)) := mul_pos hmu (Real.exp_pos _)
  have hmul := mul_lt_mul_of_pos_left hexp hposmul
  calc
    la * Real.exp (-(la * x))
        = (mu * Real.exp (-(la * x))) * (la / mu) := by field_simp [hmu.ne']
    _ < (mu * Real.exp (-(la * x))) * Real.exp ((la - mu) * x) := hmul
    _ = mu * (Real.exp (-(la * x)) * Real.exp ((la - mu) * x)) := by ring
    _ = mu * Real.exp (-(mu * x)) := by
            rw [← Real.exp_add]
            congr 2
            ring

lemma exp_density_eq_at_cross {la mu : ℝ}
    (hla : 0 < la) (hmu : 0 < mu) (hgt : mu < la) :
    let c := Real.log (la / mu) / (la - mu)
    la * Real.exp (-(la * c)) = mu * Real.exp (-(mu * c)) := by
  intro c
  have hdpos : 0 < la - mu := sub_pos.mpr hgt
  have hratio_pos : 0 < la / mu := div_pos hla hmu
  have hc : (la - mu) * c = Real.log (la / mu) := by
    dsimp [c]
    exact mul_div_cancel₀ _ hdpos.ne'
  have hexp : Real.exp ((la - mu) * c) = la / mu := by
    rw [hc, Real.exp_log hratio_pos]
  symm
  have hmul := congrArg (fun z => (mu * Real.exp (-(la * c))) * z) hexp
  calc
    mu * Real.exp (-(mu * c))
        = mu * (Real.exp (-(la * c)) * Real.exp ((la - mu) * c)) := by
            rw [← Real.exp_add]
            congr 2
            ring
    _ = (mu * Real.exp (-(la * c))) * Real.exp ((la - mu) * c) := by ring
    _ = (mu * Real.exp (-(la * c))) * (la / mu) := hmul
    _ = la * Real.exp (-(la * c)) := by field_simp [hmu.ne']

lemma densityPositiveSet_exponentialPdf_eq_Ioo_of_gt {la mu : ℝ}
    (hla : 0 < la) (hmu : 0 < mu) (hgt : mu < la) :
    TVCore.densityPositiveSet (exponentialPdf la) (exponentialPdf mu) =
      Set.Ioo 0 (Real.log (la / mu) / (la - mu)) := by
  ext x
  constructor
  · intro hx
    have hx' : 0 < exponentialPdf la x - exponentialPdf mu x := by
      simpa [TVCore.densityPositiveSet, TVCore.densityDiff] using hx
    by_cases hx0 : 0 < x
    · have hdiff : 0 < la * Real.exp (-(la * x)) - mu * Real.exp (-(mu * x)) := by
        simpa [exponentialPdf, hx0] using hx'
      have hlt_or_eq_or_gt := lt_trichotomy x (Real.log (la / mu) / (la - mu))
      rcases hlt_or_eq_or_gt with hlt | heq | hgtx
      · exact ⟨hx0, hlt⟩
      · have heqdens := exp_density_eq_at_cross hla hmu hgt
        dsimp at heqdens
        subst x
        linarith
      · have hright := exp_density_lt_of_cross_lt hla hmu hgt hgtx
        linarith
    · have : exponentialPdf la x - exponentialPdf mu x = 0 := by
        simp [exponentialPdf, hx0]
      linarith
  · intro hx
    rcases hx with ⟨hx0, hxc⟩
    have hleft := exp_density_gt_of_lt_cross hla hmu hgt hxc
    have hdiff : 0 < exponentialPdf la x - exponentialPdf mu x := by
      simp [exponentialPdf, hx0]
      linarith
    simpa [TVCore.densityPositiveSet, TVCore.densityDiff] using hdiff

lemma exponential_tv_gt {la mu : ℝ} (hla : 0 < la) (hmu : 0 < mu) (hgt : mu < la) :
    totalVariationDistance (Exponential la) (Exponential mu) =
      Real.exp (-(mu * (Real.log (la / mu) / (la - mu)))) -
        Real.exp (-(la * (Real.log (la / mu) / (la - mu)))) := by
  let c := Real.log (la / mu) / (la - mu)
  have hc_nonneg : 0 ≤ c := (cross_pos_of_gt hla hmu hgt).le
  unfold Exponential
  rw [TVCore.continuous_totalVariationDistance_eq_half_integral_abs
    (exponentialPdf_measurable la) (exponentialPdf_measurable mu)
    (exponentialPdf_integrable la hla) (exponentialPdf_integrable mu hmu)
    (exponentialPdf_nonneg la hla) (exponentialPdf_nonneg mu hmu)
    (exponentialPdf_integral la hla) (exponentialPdf_integral mu hmu)]
  rw [← TVCore.densityPositiveSet_real_diff_eq_half_abs
    (exponentialPdf_measurable la) (exponentialPdf_measurable mu)
    (exponentialPdf_integrable la hla) (exponentialPdf_integrable mu hmu)
    (exponentialPdf_nonneg la hla) (exponentialPdf_nonneg mu hmu)
    (exponentialPdf_integral la hla) (exponentialPdf_integral mu hmu)]
  rw [densityPositiveSet_exponentialPdf_eq_Ioo_of_gt hla hmu hgt]
  rw [TVCore.densityMeasure_real_apply (exponentialPdf_integrable la hla)
    (exponentialPdf_nonneg la hla) _ measurableSet_Ioo]
  rw [TVCore.densityMeasure_real_apply (exponentialPdf_integrable mu hmu)
    (exponentialPdf_nonneg mu hmu) _ measurableSet_Ioo]
  rw [integral_exponentialPdf_Ioo (r := la) (c := c) hla hc_nonneg]
  rw [integral_exponentialPdf_Ioo (r := mu) (c := c) hmu hc_nonneg]
  ring

lemma exponential_tv_gt_abs {la mu : ℝ} (hla : 0 < la) (hmu : 0 < mu) (hgt : mu < la) :
    totalVariationDistance (Exponential la) (Exponential mu) =
      |Real.exp (-(la * (Real.log (la / mu) / (la - mu)))) -
        Real.exp (-(mu * (Real.log (la / mu) / (la - mu))))| := by
  rw [exponential_tv_gt hla hmu hgt]
  exact (abs_exp_cross_of_gt hgt (cross_pos_of_gt hla hmu hgt)).symm

theorem prob_8_3 (la mu : ℝ) (hlapos : 0 < la) (hmupos : 0 < mu) :
    totalVariationDistance (Exponential la) (Exponential mu) =
      if la = mu then 0 else
        |Real.exp (-(la * (Real.log (la / mu) / (la - mu)))) -
          Real.exp (-(mu * (Real.log (la / mu) / (la - mu))))| := by
  by_cases heq : la = mu
  · subst mu
    simp [totalVariationDistance_self]
  · have hlt_or_gt := lt_or_gt_of_ne heq
    rcases hlt_or_gt with hlt | hgt
    · rw [if_neg heq]
      rw [totalVariationDistance_comm]
      have hswap := exponential_tv_gt_abs hmupos hlapos hlt
      rw [hswap]
      have hcross := cross_swap hlapos hmupos heq
      rw [hcross]
      rw [abs_sub_comm]
    · rw [if_neg heq]
      exact exponential_tv_gt_abs hlapos hmupos hgt
