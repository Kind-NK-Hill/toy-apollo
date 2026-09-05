/-
TASK ID: prob_12_5
TYPE: Problem
SOURCE PLAN: chapter12-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_12.def_12_2
import ProbabilityTheory.chapter_12.thm_12_1
import ProbabilityTheory.chapter_12.thm_12_5
import ProbabilityTheory.chapter_12.ex_12_4_2




-- WRITE FINAL LEAN CODE BELOW

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

 
def prob_12_5_centered {Ω : Type*} (X : Ω → ℝ) (μ : ℝ) : Ω → ℝ :=
  fun ω => X ω - μ

 
def prob_12_5_measurement1 {Ω : Type*} (X N1 : Ω → ℝ) : Ω → ℝ :=
  fun ω => X ω + N1 ω

def prob_12_5_measurement2 {Ω : Type*} (X N2 : Ω → ℝ) : Ω → ℝ :=
  fun ω => X ω + N2 ω



structure Prob125SensorSetup {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X N1 N2 : Ω → ℝ) (μ v0 v1 v2 : ℝ) : Prop where
  centeredL2 : L2Function P (prob_12_5_centered X μ)
  noise1L2 : L2Function P N1
  noise2L2 : L2Function P N2
  centeredMean_zero :
    ex_12_4_2_mean (P := P) (prob_12_5_centered X μ) centeredL2 = 0
  noise1Mean_zero : ex_12_4_2_mean (P := P) N1 noise1L2 = 0
  noise2Mean_zero : ex_12_4_2_mean (P := P) N2 noise2L2 = 0
  centeredVariance :
    ex_12_4_2_secondMoment (P := P) (prob_12_5_centered X μ) centeredL2 = v0
  noise1Variance : ex_12_4_2_secondMoment (P := P) N1 noise1L2 = v1
  noise2Variance : ex_12_4_2_secondMoment (P := P) N2 noise2L2 = v2
  indep_X_N1 : def_5_2 P X N1
  indep_X_N2 : def_5_2 P X N2
  indep_N1_N2 : def_5_2 P N1 N2
  noise1Variance_pos : 0 < v1
  noise2Variance_pos : 0 < v2

 
theorem prob_12_5_centered_indep {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X N : Ω → ℝ} (μ : ℝ) (hXN : def_5_2 P X N) :
    def_5_2 P (prob_12_5_centered X μ) N := by
  have hIndep : X ⟂ᵢ[P] N := by simpa [def_5_2] using hXN
  have hcenter : Measurable (fun x : ℝ => x - μ) :=
    measurable_id.sub measurable_const
  have h := hIndep.comp hcenter measurable_id
  change (fun x => X x - μ) ⟂ᵢ[P] N
  simpa [Function.comp_def] using h

theorem Prob125SensorSetup.centered_noise1_inner_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X N1 N2 : Ω → ℝ} {μ v0 v1 v2 : ℝ}
    (S : Prob125SensorSetup P X N1 N2 μ v0 v1 v2) :
    ⟪L2Function.toLp S.centeredL2, L2Function.toLp S.noise1L2⟫_ℝ = 0 := by
  rw [ex_12_4_2_toLp_inner_eq_l2Inner (P := P) S.centeredL2 S.noise1L2]
  exact ex_12_4_2_independent_noise_orthogonal (P := P)
    S.centeredL2 S.noise1L2 (prob_12_5_centered_indep μ S.indep_X_N1)
    S.noise1Mean_zero

theorem Prob125SensorSetup.centered_noise2_inner_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X N1 N2 : Ω → ℝ} {μ v0 v1 v2 : ℝ}
    (S : Prob125SensorSetup P X N1 N2 μ v0 v1 v2) :
    ⟪L2Function.toLp S.centeredL2, L2Function.toLp S.noise2L2⟫_ℝ = 0 := by
  rw [ex_12_4_2_toLp_inner_eq_l2Inner (P := P) S.centeredL2 S.noise2L2]
  exact ex_12_4_2_independent_noise_orthogonal (P := P)
    S.centeredL2 S.noise2L2 (prob_12_5_centered_indep μ S.indep_X_N2)
    S.noise2Mean_zero

theorem Prob125SensorSetup.noise1_noise2_inner_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X N1 N2 : Ω → ℝ} {μ v0 v1 v2 : ℝ}
    (S : Prob125SensorSetup P X N1 N2 μ v0 v1 v2) :
    ⟪L2Function.toLp S.noise1L2, L2Function.toLp S.noise2L2⟫_ℝ = 0 := by
  rw [ex_12_4_2_toLp_inner_eq_l2Inner (P := P) S.noise1L2 S.noise2L2]
  exact ex_12_4_2_independent_noise_orthogonal (P := P)
    S.noise1L2 S.noise2L2 S.indep_N1_N2 S.noise2Mean_zero

theorem Prob125SensorSetup.centeredVariance_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X N1 N2 : Ω → ℝ} {μ v0 v1 v2 : ℝ}
    (S : Prob125SensorSetup P X N1 N2 μ v0 v1 v2) : 0 ≤ v0 := by
  have h := real_inner_self_nonneg (x := L2Function.toLp S.centeredL2)
  rw [ex_12_4_2_toLp_inner_eq_l2Inner (P := P) S.centeredL2 S.centeredL2] at h
  rw [← S.centeredVariance]
  simpa [ex_12_4_2_secondMoment] using h

 
noncomputable def prob_12_5_oneSensorError
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X N1 N2 : Ω → ℝ} {μ v0 v1 v2 : ℝ}
    (S : Prob125SensorSetup P X N1 N2 μ v0 v1 v2) (α : ℝ) : Ω →₂[P] ℝ :=
  (1 - α) • L2Function.toLp S.centeredL2 + (-α) • L2Function.toLp S.noise1L2

noncomputable def prob_12_5_twoSensorError
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X N1 N2 : Ω → ℝ} {μ v0 v1 v2 : ℝ}
    (S : Prob125SensorSetup P X N1 N2 μ v0 v1 v2) (α β : ℝ) : Ω →₂[P] ℝ :=
  (1 - α - β) • L2Function.toLp S.centeredL2 +
    (-α) • L2Function.toLp S.noise1L2 + (-β) • L2Function.toLp S.noise2L2



theorem prob_12_5_oneSensor_error_identity {Ω : Type*}
    (X N1 : Ω → ℝ) (μ α : ℝ) (ω : Ω) :
    X ω - μ - α * (prob_12_5_measurement1 X N1 ω - μ) =
      (1 - α) * prob_12_5_centered X μ ω + (-α) * N1 ω := by
  simp [prob_12_5_measurement1, prob_12_5_centered]
  ring

theorem prob_12_5_twoSensor_error_identity {Ω : Type*}
    (X N1 N2 : Ω → ℝ) (μ α β : ℝ) (ω : Ω) :
    X ω - μ - α * (prob_12_5_measurement1 X N1 ω - μ) -
        β * (prob_12_5_measurement2 X N2 ω - μ) =
      (1 - α - β) * prob_12_5_centered X μ ω +
        (-α) * N1 ω + (-β) * N2 ω := by
  simp [prob_12_5_measurement1, prob_12_5_measurement2, prob_12_5_centered]
  ring

 
noncomputable def prob_12_5_oneSensorActualMSE
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X N1 N2 : Ω → ℝ} {μ v0 v1 v2 : ℝ}
    (S : Prob125SensorSetup P X N1 N2 μ v0 v1 v2) (α : ℝ) : ℝ :=
  ⟪prob_12_5_oneSensorError S α, prob_12_5_oneSensorError S α⟫_ℝ

noncomputable def prob_12_5_twoSensorActualMSE
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X N1 N2 : Ω → ℝ} {μ v0 v1 v2 : ℝ}
    (S : Prob125SensorSetup P X N1 N2 μ v0 v1 v2) (α β : ℝ) : ℝ :=
  ⟪prob_12_5_twoSensorError S α β, prob_12_5_twoSensorError S α β⟫_ℝ




theorem prob_12_5_oneSensorActualMSE_eq_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X N1 N2 : Ω → ℝ} {μ v0 v1 v2 : ℝ}
    (S : Prob125SensorSetup P X N1 N2 μ v0 v1 v2) (α : ℝ) :
    prob_12_5_oneSensorActualMSE S α =
      ∫ ω, (X ω - μ -
        α * (prob_12_5_measurement1 X N1 ω - μ)) ^ 2 ∂P := by
  have hErr :
      ⇑(prob_12_5_oneSensorError S α) =ᵐ[P]
        fun ω => X ω - μ - α * (prob_12_5_measurement1 X N1 ω - μ) := by
    filter_upwards [
      Lp.coeFn_add ((1 - α) • L2Function.toLp S.centeredL2)
        ((-α) • L2Function.toLp S.noise1L2),
      Lp.coeFn_smul (1 - α) (L2Function.toLp S.centeredL2),
      Lp.coeFn_smul (-α) (L2Function.toLp S.noise1L2),
      L2Function.coeFn_toLp S.centeredL2,
      L2Function.coeFn_toLp S.noise1L2]
      with ω hadd hsmulX hsmul1 hXω h1ω
    rw [prob_12_5_oneSensorError, hadd]
    simp only [Pi.add_apply]
    rw [hsmulX, hsmul1]
    simp only [Pi.smul_apply, smul_eq_mul]
    change (1 - α) * (L2Function.toLp S.centeredL2) ω +
      (-α) * (L2Function.toLp S.noise1L2) ω = _
    rw [hXω, h1ω]
    simp [prob_12_5_measurement1, prob_12_5_centered]
    ring
  rw [prob_12_5_oneSensorActualMSE, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hErr] with ω hω
  rw [hω, real_inner_eq_re_inner ℝ, RCLike.inner_apply']
  simp [pow_two]



theorem prob_12_5_twoSensorActualMSE_eq_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X N1 N2 : Ω → ℝ} {μ v0 v1 v2 : ℝ}
    (S : Prob125SensorSetup P X N1 N2 μ v0 v1 v2) (α β : ℝ) :
    prob_12_5_twoSensorActualMSE S α β =
      ∫ ω, (X ω - μ -
        α * (prob_12_5_measurement1 X N1 ω - μ) -
        β * (prob_12_5_measurement2 X N2 ω - μ)) ^ 2 ∂P := by
  have hErr :
      ⇑(prob_12_5_twoSensorError S α β) =ᵐ[P]
        fun ω => X ω - μ - α * (prob_12_5_measurement1 X N1 ω - μ) -
          β * (prob_12_5_measurement2 X N2 ω - μ) := by
    filter_upwards [
      Lp.coeFn_add
        ((1 - α - β) • L2Function.toLp S.centeredL2 +
          (-α) • L2Function.toLp S.noise1L2)
        ((-β) • L2Function.toLp S.noise2L2),
      Lp.coeFn_add ((1 - α - β) • L2Function.toLp S.centeredL2)
        ((-α) • L2Function.toLp S.noise1L2),
      Lp.coeFn_smul (1 - α - β) (L2Function.toLp S.centeredL2),
      Lp.coeFn_smul (-α) (L2Function.toLp S.noise1L2),
      Lp.coeFn_smul (-β) (L2Function.toLp S.noise2L2),
      L2Function.coeFn_toLp S.centeredL2,
      L2Function.coeFn_toLp S.noise1L2,
      L2Function.coeFn_toLp S.noise2L2]
      with ω haddOuter haddInner hsmulX hsmul1 hsmul2 hXω h1ω h2ω
    rw [prob_12_5_twoSensorError, haddOuter]
    simp only [Pi.add_apply]
    rw [haddInner]
    simp only [Pi.add_apply]
    rw [hsmulX, hsmul1, hsmul2]
    simp only [Pi.smul_apply, smul_eq_mul]
    change (1 - α - β) * (L2Function.toLp S.centeredL2) ω +
      (-α) * (L2Function.toLp S.noise1L2) ω +
      (-β) * (L2Function.toLp S.noise2L2) ω = _
    rw [hXω, h1ω, h2ω]
    simp [prob_12_5_measurement1, prob_12_5_measurement2, prob_12_5_centered]
    ring
  rw [prob_12_5_twoSensorActualMSE, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hErr] with ω hω
  rw [hω, real_inner_eq_re_inner ℝ, RCLike.inner_apply']
  simp [pow_two]

def prob_12_5_oneSensorMSE (v0 v1 α : ℝ) : ℝ :=
  (1 - α) ^ 2 * v0 + α ^ 2 * v1

def prob_12_5_twoSensorMSE (v0 v1 v2 α β : ℝ) : ℝ :=
  (1 - α - β) ^ 2 * v0 + α ^ 2 * v1 + β ^ 2 * v2

 
theorem prob_12_5_oneSensorActualMSE_eq_quadratic
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X N1 N2 : Ω → ℝ} {μ v0 v1 v2 : ℝ}
    (S : Prob125SensorSetup P X N1 N2 μ v0 v1 v2) (α : ℝ) :
    prob_12_5_oneSensorActualMSE S α = prob_12_5_oneSensorMSE v0 v1 α := by
  have hXX : ⟪L2Function.toLp S.centeredL2, L2Function.toLp S.centeredL2⟫_ℝ = v0 := by
    rw [ex_12_4_2_toLp_inner_eq_l2Inner (P := P) S.centeredL2 S.centeredL2]
    exact S.centeredVariance
  have hNN : ⟪L2Function.toLp S.noise1L2, L2Function.toLp S.noise1L2⟫_ℝ = v1 := by
    rw [ex_12_4_2_toLp_inner_eq_l2Inner (P := P) S.noise1L2 S.noise1L2]
    exact S.noise1Variance
  have hXN := S.centered_noise1_inner_zero
  have hNX : ⟪L2Function.toLp S.noise1L2, L2Function.toLp S.centeredL2⟫_ℝ = 0 := by
    rw [real_inner_comm]; exact hXN
  simp only [prob_12_5_oneSensorActualMSE, prob_12_5_oneSensorError,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial]
  rw [hXX, hXN, hNX, hNN]
  unfold prob_12_5_oneSensorMSE
  ring

theorem prob_12_5_twoSensorActualMSE_eq_quadratic
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X N1 N2 : Ω → ℝ} {μ v0 v1 v2 : ℝ}
    (S : Prob125SensorSetup P X N1 N2 μ v0 v1 v2) (α β : ℝ) :
    prob_12_5_twoSensorActualMSE S α β = prob_12_5_twoSensorMSE v0 v1 v2 α β := by
  have hXX : ⟪L2Function.toLp S.centeredL2, L2Function.toLp S.centeredL2⟫_ℝ = v0 := by
    rw [ex_12_4_2_toLp_inner_eq_l2Inner (P := P) S.centeredL2 S.centeredL2]
    exact S.centeredVariance
  have h11 : ⟪L2Function.toLp S.noise1L2, L2Function.toLp S.noise1L2⟫_ℝ = v1 := by
    rw [ex_12_4_2_toLp_inner_eq_l2Inner (P := P) S.noise1L2 S.noise1L2]
    exact S.noise1Variance
  have h22 : ⟪L2Function.toLp S.noise2L2, L2Function.toLp S.noise2L2⟫_ℝ = v2 := by
    rw [ex_12_4_2_toLp_inner_eq_l2Inner (P := P) S.noise2L2 S.noise2L2]
    exact S.noise2Variance
  have hX1 := S.centered_noise1_inner_zero
  have hX2 := S.centered_noise2_inner_zero
  have h12 := S.noise1_noise2_inner_zero
  have h1X : ⟪L2Function.toLp S.noise1L2, L2Function.toLp S.centeredL2⟫_ℝ = 0 := by
    rw [real_inner_comm]; exact hX1
  have h2X : ⟪L2Function.toLp S.noise2L2, L2Function.toLp S.centeredL2⟫_ℝ = 0 := by
    rw [real_inner_comm]; exact hX2
  have h21 : ⟪L2Function.toLp S.noise2L2, L2Function.toLp S.noise1L2⟫_ℝ = 0 := by
    rw [real_inner_comm]; exact h12
  simp only [prob_12_5_twoSensorActualMSE, prob_12_5_twoSensorError,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial]
  rw [hXX, h11, h22, hX1, hX2, h12, h1X, h2X, h21]
  unfold prob_12_5_twoSensorMSE
  ring

 
def prob_12_5_oneSensorAlpha (v0 v1 : ℝ) (_hden : 0 < v0 + v1) : ℝ :=
  v0 / (v0 + v1)

def prob_12_5_twoSensorDen (v0 v1 v2 : ℝ) : ℝ :=
  v0 * v1 + v0 * v2 + v1 * v2

def prob_12_5_twoSensorAlpha (v0 v1 v2 : ℝ)
    (_hden : 0 < prob_12_5_twoSensorDen v0 v1 v2) : ℝ :=
  v0 * v2 / prob_12_5_twoSensorDen v0 v1 v2

def prob_12_5_twoSensorBeta (v0 v1 v2 : ℝ)
    (_hden : 0 < prob_12_5_twoSensorDen v0 v1 v2) : ℝ :=
  v0 * v1 / prob_12_5_twoSensorDen v0 v1 v2

theorem Prob125SensorSetup.oneSensorDen_pos
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X N1 N2 : Ω → ℝ} {μ v0 v1 v2 : ℝ}
    (S : Prob125SensorSetup P X N1 N2 μ v0 v1 v2) : 0 < v0 + v1 := by
  nlinarith [S.centeredVariance_nonneg, S.noise1Variance_pos]

theorem Prob125SensorSetup.twoSensorDen_pos
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X N1 N2 : Ω → ℝ} {μ v0 v1 v2 : ℝ}
    (S : Prob125SensorSetup P X N1 N2 μ v0 v1 v2) :
    0 < prob_12_5_twoSensorDen v0 v1 v2 := by
  have h0 := S.centeredVariance_nonneg
  have h12 : 0 < v1 * v2 := mul_pos S.noise1Variance_pos S.noise2Variance_pos
  have h01 : 0 ≤ v0 * v1 := mul_nonneg h0 S.noise1Variance_pos.le
  have h02 : 0 ≤ v0 * v2 := mul_nonneg h0 S.noise2Variance_pos.le
  unfold prob_12_5_twoSensorDen
  nlinarith

theorem prob_12_5_oneSensorMSE_sub_opt
    {v0 v1 : ℝ} (hden : 0 < v0 + v1) (α : ℝ) :
    prob_12_5_oneSensorMSE v0 v1 α -
        prob_12_5_oneSensorMSE v0 v1 (prob_12_5_oneSensorAlpha v0 v1 hden) =
      (v0 + v1) * (α - prob_12_5_oneSensorAlpha v0 v1 hden) ^ 2 := by
  unfold prob_12_5_oneSensorMSE prob_12_5_oneSensorAlpha
  field_simp [ne_of_gt hden]
  ring_nf

theorem prob_12_5_oneSensorAlpha_optimal
    {v0 v1 : ℝ} (hden : 0 < v0 + v1) (α : ℝ) :
    prob_12_5_oneSensorMSE v0 v1 (prob_12_5_oneSensorAlpha v0 v1 hden) ≤
      prob_12_5_oneSensorMSE v0 v1 α := by
  have hdiff := prob_12_5_oneSensorMSE_sub_opt hden α
  have hnonneg : 0 ≤ prob_12_5_oneSensorMSE v0 v1 α -
      prob_12_5_oneSensorMSE v0 v1 (prob_12_5_oneSensorAlpha v0 v1 hden) := by
    rw [hdiff]
    exact mul_nonneg hden.le (sq_nonneg _)
  linarith

theorem prob_12_5_twoSensorMSE_sub_stationary
    {v0 v1 v2 α0 β0 : ℝ}
    (hα : v1 * α0 = v0 * (1 - α0 - β0))
    (hβ : v2 * β0 = v0 * (1 - α0 - β0)) (α β : ℝ) :
    prob_12_5_twoSensorMSE v0 v1 v2 α β -
        prob_12_5_twoSensorMSE v0 v1 v2 α0 β0 =
      v0 * ((1 - α - β) - (1 - α0 - β0)) ^ 2 +
        v1 * (α - α0) ^ 2 + v2 * (β - β0) ^ 2 := by
  have hlinear :
      v0 * (1 - α0 - β0) * ((1 - α - β) - (1 - α0 - β0)) * 2 +
          v1 * α0 * (α - α0) * 2 + v2 * β0 * (β - β0) * 2 = 0 := by
    rw [hα, hβ]
    ring
  calc
    prob_12_5_twoSensorMSE v0 v1 v2 α β -
        prob_12_5_twoSensorMSE v0 v1 v2 α0 β0 =
      (v0 * ((1 - α - β) - (1 - α0 - β0)) ^ 2 +
          v1 * (α - α0) ^ 2 + v2 * (β - β0) ^ 2) +
        (v0 * (1 - α0 - β0) * ((1 - α - β) - (1 - α0 - β0)) * 2 +
          v1 * α0 * (α - α0) * 2 + v2 * β0 * (β - β0) * 2) := by
        unfold prob_12_5_twoSensorMSE
        ring
    _ = _ := by rw [hlinear]; ring

theorem prob_12_5_twoSensorCoefficients_stationary
    {v0 v1 v2 : ℝ} (hden : 0 < prob_12_5_twoSensorDen v0 v1 v2) :
    v1 * prob_12_5_twoSensorAlpha v0 v1 v2 hden =
        v0 * (1 - prob_12_5_twoSensorAlpha v0 v1 v2 hden -
          prob_12_5_twoSensorBeta v0 v1 v2 hden) ∧
      v2 * prob_12_5_twoSensorBeta v0 v1 v2 hden =
        v0 * (1 - prob_12_5_twoSensorAlpha v0 v1 v2 hden -
          prob_12_5_twoSensorBeta v0 v1 v2 hden) := by
  unfold prob_12_5_twoSensorAlpha prob_12_5_twoSensorBeta
  constructor <;> field_simp [ne_of_gt hden] <;>
    unfold prob_12_5_twoSensorDen <;> ring

theorem prob_12_5_twoSensorMSE_sub_opt
    {v0 v1 v2 : ℝ} (hden : 0 < prob_12_5_twoSensorDen v0 v1 v2)
    (α β : ℝ) :
    prob_12_5_twoSensorMSE v0 v1 v2 α β -
        prob_12_5_twoSensorMSE v0 v1 v2
          (prob_12_5_twoSensorAlpha v0 v1 v2 hden)
          (prob_12_5_twoSensorBeta v0 v1 v2 hden) =
      v0 * ((1 - α - β) -
          (1 - prob_12_5_twoSensorAlpha v0 v1 v2 hden -
            prob_12_5_twoSensorBeta v0 v1 v2 hden)) ^ 2 +
        v1 * (α - prob_12_5_twoSensorAlpha v0 v1 v2 hden) ^ 2 +
        v2 * (β - prob_12_5_twoSensorBeta v0 v1 v2 hden) ^ 2 := by
  have hstat := prob_12_5_twoSensorCoefficients_stationary hden
  exact prob_12_5_twoSensorMSE_sub_stationary hstat.1 hstat.2 α β

theorem prob_12_5_twoSensorCoefficients_optimal
    {v0 v1 v2 : ℝ} (hv0 : 0 ≤ v0) (hv1 : 0 ≤ v1) (hv2 : 0 ≤ v2)
    (hden : 0 < prob_12_5_twoSensorDen v0 v1 v2) (α β : ℝ) :
    prob_12_5_twoSensorMSE v0 v1 v2
        (prob_12_5_twoSensorAlpha v0 v1 v2 hden)
        (prob_12_5_twoSensorBeta v0 v1 v2 hden) ≤
      prob_12_5_twoSensorMSE v0 v1 v2 α β := by
  have hdiff := prob_12_5_twoSensorMSE_sub_opt hden α β
  have hnonneg : 0 ≤ prob_12_5_twoSensorMSE v0 v1 v2 α β -
      prob_12_5_twoSensorMSE v0 v1 v2
        (prob_12_5_twoSensorAlpha v0 v1 v2 hden)
        (prob_12_5_twoSensorBeta v0 v1 v2 hden) := by
    rw [hdiff]
    exact add_nonneg (add_nonneg (mul_nonneg hv0 (sq_nonneg _))
      (mul_nonneg hv1 (sq_nonneg _))) (mul_nonneg hv2 (sq_nonneg _))
  linarith



theorem prob_12_5
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X N1 N2 : Ω → ℝ} {μ v0 v1 v2 : ℝ}
    (S : Prob125SensorSetup P X N1 N2 μ v0 v1 v2) :
    (∀ α : ℝ,
      prob_12_5_oneSensorActualMSE S
          (prob_12_5_oneSensorAlpha v0 v1 S.oneSensorDen_pos) ≤
        prob_12_5_oneSensorActualMSE S α) ∧
    (∀ α β : ℝ,
      prob_12_5_twoSensorActualMSE S
          (prob_12_5_twoSensorAlpha v0 v1 v2 S.twoSensorDen_pos)
          (prob_12_5_twoSensorBeta v0 v1 v2 S.twoSensorDen_pos) ≤
        prob_12_5_twoSensorActualMSE S α β) := by
  constructor
  · intro α
    rw [prob_12_5_oneSensorActualMSE_eq_quadratic,
      prob_12_5_oneSensorActualMSE_eq_quadratic]
    exact prob_12_5_oneSensorAlpha_optimal S.oneSensorDen_pos α
  · intro α β
    rw [prob_12_5_twoSensorActualMSE_eq_quadratic,
      prob_12_5_twoSensorActualMSE_eq_quadratic]
    exact prob_12_5_twoSensorCoefficients_optimal S.centeredVariance_nonneg
      S.noise1Variance_pos.le S.noise2Variance_pos.le S.twoSensorDen_pos α β
