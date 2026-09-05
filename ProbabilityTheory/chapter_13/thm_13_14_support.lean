/-
TASK ID: thm_13_14_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.Phase2.DensityIntegralBridge
import ProbabilityTheory.Phase2.VectorMeasureBorelBridge




open MeasureTheory
open scoped ENNReal

noncomputable section

 
def thm_13_14_X (z : ℝ × ℝ) : ℝ :=
  z.1

 
def thm_13_14_Y (z : ℝ × ℝ) : ℝ :=
  z.2



def thm_13_14_jointDensityLaw
    (P : Measure (ℝ × ℝ)) (fXY : ℝ × ℝ → ℝ) : Prop :=
  ∀ B : Set (ℝ × ℝ), MeasurableSet B →
    P B = ∫⁻ z in B, ENNReal.ofReal (fXY z) ∂volume

 
def thm_13_14_marginalDensity (fXY : ℝ × ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ x : ℝ, fXY (x, y) ∂volume

 
def thm_13_14_conditionalDensity
    (fXY : ℝ × ℝ → ℝ) (x y : ℝ) : ℝ :=
  fXY (x, y) / thm_13_14_marginalDensity fXY y



def thm_13_14_conditionalExpectationKernel
    (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ x : ℝ, g x * thm_13_14_conditionalDensity fXY x y ∂volume

 
def thm_13_14_identityConditionalExpectationKernel
    (fXY : ℝ × ℝ → ℝ) (y : ℝ) : ℝ :=
  thm_13_14_conditionalExpectationKernel fXY (fun x : ℝ => x) y



def thm_13_14_verticalCylinder (S : Set ℝ) : Set (ℝ × ℝ) :=
  {z | z.2 ∈ S}



def thm_13_14_closedIntervalCylinder (a b : ℝ) : Set (ℝ × ℝ) :=
  thm_13_14_verticalCylinder (Set.Icc a b)

theorem thm_13_14_verticalCylinder_eq_prod (S : Set ℝ) :
    thm_13_14_verticalCylinder S = (Set.univ : Set ℝ) ×ˢ S := by
  ext z
  simp [thm_13_14_verticalCylinder]

theorem thm_13_14_closedIntervalCylinder_eq_prod (a b : ℝ) :
    thm_13_14_closedIntervalCylinder a b =
      (Set.univ : Set ℝ) ×ˢ (Set.Icc a b) := by
  rw [thm_13_14_closedIntervalCylinder, thm_13_14_verticalCylinder_eq_prod]

theorem thm_13_14_verticalCylinder_measurable
    {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurableSet (thm_13_14_verticalCylinder S) := by
  change MeasurableSet (Prod.snd ⁻¹' S)
  exact hS.preimage measurable_snd

theorem thm_13_14_closedIntervalCylinder_measurable (a b : ℝ) :
    MeasurableSet (thm_13_14_closedIntervalCylinder a b) := by
  exact thm_13_14_verticalCylinder_measurable measurableSet_Icc



def thm_13_14_sigmaYMeasurableSet (C : Set (ℝ × ℝ)) : Prop :=
  ∃ S : Set ℝ, MeasurableSet S ∧ C = thm_13_14_verticalCylinder S



def thm_13_14_integralIdentity
    (P : Measure (ℝ × ℝ)) (g h : ℝ → ℝ) (C : Set (ℝ × ℝ)) : Prop :=
  (∫ z in C, g z.1 ∂P) = ∫ z in C, h z.2 ∂P



def thm_13_14_intervalFubiniSupport
    (P : Measure (ℝ × ℝ)) (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, a ≤ b →
    thm_13_14_integralIdentity P g
      (thm_13_14_conditionalExpectationKernel fXY g)
      (thm_13_14_closedIntervalCylinder a b)



def thm_13_14_piLambdaExtensionSupport
    (P : Measure (ℝ × ℝ)) (g h : ℝ → ℝ) : Prop :=
  (∀ a b : ℝ, a ≤ b →
    thm_13_14_integralIdentity P g h
      (thm_13_14_closedIntervalCylinder a b)) →
    ∀ S : Set ℝ, MeasurableSet S →
      thm_13_14_integralIdentity P g h
        (thm_13_14_verticalCylinder S)



def thm_13_14_isConditionalExpectationVersion
    (P : Measure (ℝ × ℝ)) (g h : ℝ → ℝ) : Prop :=
  Measurable h ∧
    Integrable (fun z : ℝ × ℝ => g z.1) P ∧
    Integrable (fun z : ℝ × ℝ => h z.2) P ∧
    ∀ C : Set (ℝ × ℝ), thm_13_14_sigmaYMeasurableSet C →
      thm_13_14_integralIdentity P g h C

theorem thm_13_14_marginalDensity_eq
    (fXY : ℝ × ℝ → ℝ) (y : ℝ) :
    thm_13_14_marginalDensity fXY y =
      ∫ x : ℝ, fXY (x, y) ∂volume := by
  rfl

theorem thm_13_14_conditionalDensity_eq
    (fXY : ℝ × ℝ → ℝ) (x y : ℝ) :
    thm_13_14_conditionalDensity fXY x y =
      fXY (x, y) / thm_13_14_marginalDensity fXY y := by
  rfl

 
theorem thm_13_14_measure_eq_withDensity
    (P : Measure (ℝ × ℝ)) (fXY : ℝ × ℝ → ℝ)
    (hDensity : thm_13_14_jointDensityLaw P fXY) :
    P = volume.withDensity (fun z : ℝ × ℝ => ENNReal.ofReal (fXY z)) := by
  exact phase2_measure_eq_withDensity_of_forall_measurable P volume
    (fun z : ℝ × ℝ => ENNReal.ofReal (fXY z)) hDensity

 
theorem thm_13_14_setIntegral_jointDensity_eq
    (P : Measure (ℝ × ℝ)) (fXY : ℝ × ℝ → ℝ) (φ : ℝ × ℝ → ℝ)
    (C : Set (ℝ × ℝ)) (hC : MeasurableSet C)
    (hDensity : thm_13_14_jointDensityLaw P fXY)
    (hDensityAEMeas :
      AEMeasurable (fun z : ℝ × ℝ => ENNReal.ofReal (fXY z)) volume)
    (hDensityNonneg : ∀ᵐ z ∂volume, 0 ≤ fXY z) :
    (∫ z in C, φ z ∂P) = ∫ z in C, fXY z * φ z ∂volume := by
  exact phase2_setIntegral_withDensity_ofReal_eq P volume fXY φ C hC
    (thm_13_14_measure_eq_withDensity P fXY hDensity)
    hDensityAEMeas hDensityNonneg



theorem thm_13_14_integrable_under_jointDensity
    (P : Measure (ℝ × ℝ)) (fXY : ℝ × ℝ → ℝ) (φ : ℝ × ℝ → ℝ)
    (hDensity : thm_13_14_jointDensityLaw P fXY)
    (hDensityAEMeas :
      AEMeasurable (fun z : ℝ × ℝ => ENNReal.ofReal (fXY z)) volume)
    (hDensityNonneg : ∀ᵐ z ∂volume, 0 ≤ fXY z)
    (hWeighted : Integrable (fun z : ℝ × ℝ => fXY z * φ z) volume) :
    Integrable φ P := by
  exact phase2_integrable_withDensity_ofReal_of_weighted P volume fXY φ
    (thm_13_14_measure_eq_withDensity P fXY hDensity)
    hDensityAEMeas hDensityNonneg hWeighted



theorem thm_13_14_jointDensity_integrable
    (P : Measure (ℝ × ℝ)) [IsProbabilityMeasure P]
    (fXY : ℝ × ℝ → ℝ)
    (hDensity : thm_13_14_jointDensityLaw P fXY)
    (hDensityAEMeas :
      AEMeasurable (fun z : ℝ × ℝ => ENNReal.ofReal (fXY z)) volume)
    (hDensityNonneg : ∀ᵐ z ∂volume, 0 ≤ fXY z) :
    Integrable fXY volume := by
  have hlin :
      (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (fXY z) ∂volume) ≠ ∞ := by
    have h := hDensity Set.univ MeasurableSet.univ
    rw [Measure.restrict_univ] at h
    rw [← h, IsProbabilityMeasure.measure_univ]
    norm_num
  have hToRealInt := integrable_toReal_of_lintegral_ne_top
    hDensityAEMeas hlin
  refine hToRealInt.congr ?_
  filter_upwards [hDensityNonneg] with z hz
  simp [ENNReal.toReal_ofReal hz]



theorem thm_13_14_setIntegral_verticalCylinder_prod_symm
    (F : ℝ × ℝ → ℝ) (a b : ℝ)
    (hInt : IntegrableOn F (thm_13_14_closedIntervalCylinder a b) volume) :
    (∫ z in thm_13_14_closedIntervalCylinder a b, F z ∂volume) =
      ∫ y in Set.Icc a b, ∫ x : ℝ, F (x, y) ∂volume ∂volume := by
  have hInt' : IntegrableOn F ((Set.univ : Set ℝ) ×ˢ Set.Icc a b)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    simpa [thm_13_14_closedIntervalCylinder_eq_prod, Measure.volume_eq_prod] using hInt
  have hInt'' :
      Integrable F
        ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Icc a b))) := by
    rw [IntegrableOn, ← Measure.prod_restrict] at hInt'
    simpa [Measure.restrict_univ] using hInt'
  rw [thm_13_14_closedIntervalCylinder_eq_prod, Measure.volume_eq_prod]
  rw [← Measure.prod_restrict, Measure.restrict_univ]
  exact integral_prod_symm (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ).restrict (Set.Icc a b)) F hInt''



theorem thm_13_14_kernel_mul_marginal_eq_integral
    (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ) (y : ℝ)
    (hFY_ne_zero : thm_13_14_marginalDensity fXY y ≠ 0) :
    thm_13_14_conditionalExpectationKernel fXY g y *
        thm_13_14_marginalDensity fXY y =
      ∫ x : ℝ, g x * fXY (x, y) ∂volume := by
  unfold thm_13_14_conditionalExpectationKernel thm_13_14_conditionalDensity
  have hfun :
      (fun x : ℝ => g x * (fXY (x, y) / thm_13_14_marginalDensity fXY y)) =
        fun x : ℝ => (g x * fXY (x, y)) /
          thm_13_14_marginalDensity fXY y := by
    funext x
    ring
  rw [hfun, integral_div]
  field_simp [hFY_ne_zero]



theorem thm_13_14_kernel_stronglyMeasurable
    (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ)
    (hGMeas : Measurable g)
    (hDensityMeas : Measurable fXY) :
    StronglyMeasurable (thm_13_14_conditionalExpectationKernel fXY g) := by
  have hGFStrong : StronglyMeasurable (fun z : ℝ × ℝ => g z.1 * fXY z) :=
    (hGMeas.comp measurable_fst).stronglyMeasurable.mul
      hDensityMeas.stronglyMeasurable
  have hNStrong : StronglyMeasurable
      (fun y : ℝ => ∫ x : ℝ, g x * fXY (x, y) ∂volume) := by
    simpa using hGFStrong.integral_prod_left'
  have hFYStrong : StronglyMeasurable
      (fun y : ℝ => thm_13_14_marginalDensity fXY y) := by
    simpa [thm_13_14_marginalDensity] using
      hDensityMeas.stronglyMeasurable.integral_prod_left'
  have hK_eq :
      thm_13_14_conditionalExpectationKernel fXY g =
        fun y : ℝ =>
          (∫ x : ℝ, g x * fXY (x, y) ∂volume) /
            thm_13_14_marginalDensity fXY y := by
    funext y
    unfold thm_13_14_conditionalExpectationKernel thm_13_14_conditionalDensity
    have hfun :
        (fun x : ℝ => g x * (fXY (x, y) / thm_13_14_marginalDensity fXY y)) =
          fun x : ℝ => (g x * fXY (x, y)) /
            thm_13_14_marginalDensity fXY y := by
      funext x
      ring
    rw [hfun, integral_div]
  rw [hK_eq]
  exact hNStrong.div hFYStrong



theorem thm_13_14_gWeighted_abs_integrable
    (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ)
    (hDensityNonneg : ∀ z : ℝ × ℝ, 0 ≤ fXY z)
    (hGWeightedInt : Integrable (fun z : ℝ × ℝ => fXY z * g z.1) volume) :
    Integrable (fun z : ℝ × ℝ => |g z.1| * fXY z) volume := by
  refine hGWeightedInt.norm.congr ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hDensityNonneg z)]
  ring



theorem thm_13_14_marginalDensity_pos_of_nonneg_ne_zero
    (fXY : ℝ × ℝ → ℝ) (y : ℝ)
    (hFiberNonneg : ∀ x : ℝ, 0 ≤ fXY (x, y))
    (hFY_ne_zero : thm_13_14_marginalDensity fXY y ≠ 0) :
    0 < thm_13_14_marginalDensity fXY y := by
  have hnonneg : 0 ≤ thm_13_14_marginalDensity fXY y := by
    unfold thm_13_14_marginalDensity
    exact integral_nonneg hFiberNonneg
  exact lt_of_le_of_ne' hnonneg hFY_ne_zero



theorem thm_13_14_kernel_abs_mul_marginal_le_integral_abs
    (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ) (y : ℝ)
    (hFiberNonneg : ∀ x : ℝ, 0 ≤ fXY (x, y))
    (hFY_pos : 0 < thm_13_14_marginalDensity fXY y) :
    |thm_13_14_conditionalExpectationKernel fXY g y| *
        thm_13_14_marginalDensity fXY y ≤
      ∫ x : ℝ, |g x| * fXY (x, y) ∂volume := by
  let m : ℝ := thm_13_14_marginalDensity fXY y
  have hm_pos : 0 < m := hFY_pos
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have hnorm := norm_integral_le_integral_norm
    (μ := (volume : Measure ℝ))
    (f := fun x : ℝ => g x * thm_13_14_conditionalDensity fXY x y)
  have hnorm₁ :
      |thm_13_14_conditionalExpectationKernel fXY g y| ≤
        ∫ x : ℝ, |g x| * (|fXY (x, y)| / m) ∂volume := by
    simpa [Real.norm_eq_abs, thm_13_14_conditionalExpectationKernel,
      thm_13_14_conditionalDensity, m, abs_mul, abs_div,
      abs_of_pos hm_pos]
      using hnorm
  have hright :
      (∫ x : ℝ, |g x| * (|fXY (x, y)| / m) ∂volume) =
        ∫ x : ℝ, |g x| * fXY (x, y) / m ∂volume := by
    apply integral_congr_ae
    filter_upwards with x
    rw [abs_of_nonneg (hFiberNonneg x)]
    ring
  have hnorm' :
      |thm_13_14_conditionalExpectationKernel fXY g y| ≤
        ∫ x : ℝ, |g x| * fXY (x, y) / m ∂volume := by
    exact hnorm₁.trans_eq hright
  rw [integral_div] at hnorm'
  have hmul := mul_le_mul_of_nonneg_right hnorm' hm_pos.le
  simpa [div_mul_cancel₀ _ hm_ne, m] using hmul



theorem thm_13_14_kernelWeighted_integrable_from_gWeighted
    (P : Measure (ℝ × ℝ)) [IsProbabilityMeasure P]
    (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ)
    (hDensity : thm_13_14_jointDensityLaw P fXY)
    (hGMeas : Measurable g)
    (hDensityMeas : Measurable fXY)
    (hDensityNonneg : ∀ z : ℝ × ℝ, 0 ≤ fXY z)
    (hGWeightedInt : Integrable (fun z : ℝ × ℝ => fXY z * g z.1) volume)
    (hFY_ne_zero : ∀ y : ℝ, thm_13_14_marginalDensity fXY y ≠ 0) :
    Integrable
      (fun z : ℝ × ℝ =>
        fXY z * thm_13_14_conditionalExpectationKernel fXY g z.2) volume := by
  let K : ℝ → ℝ := thm_13_14_conditionalExpectationKernel fXY g
  let F : ℝ × ℝ → ℝ := fun z => fXY z * K z.2
  let A : ℝ → ℝ := fun y => ∫ x : ℝ, |g x| * fXY (x, y) ∂volume
  have hDensityAEMeas :
      AEMeasurable (fun z : ℝ × ℝ => ENNReal.ofReal (fXY z)) volume :=
    hDensityMeas.ennreal_ofReal.aemeasurable
  have hDensityNonnegAE : ∀ᵐ z ∂volume, 0 ≤ fXY z :=
    ae_of_all _ hDensityNonneg
  have hfxyInt : Integrable fXY volume :=
    thm_13_14_jointDensity_integrable P fXY hDensity
      hDensityAEMeas hDensityNonnegAE
  have hfxyInt_prod : Integrable fXY
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    simpa [Measure.volume_eq_prod] using hfxyInt
  have hAbsInt : Integrable (fun z : ℝ × ℝ => |g z.1| * fXY z) volume :=
    thm_13_14_gWeighted_abs_integrable fXY g hDensityNonneg hGWeightedInt
  have hAbsInt_prod : Integrable (fun z : ℝ × ℝ => |g z.1| * fXY z)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    simpa [Measure.volume_eq_prod] using hAbsInt
  have hGFStrong : StronglyMeasurable (fun z : ℝ × ℝ => g z.1 * fXY z) :=
    (hGMeas.comp measurable_fst).stronglyMeasurable.mul
      hDensityMeas.stronglyMeasurable
  have hNStrong : StronglyMeasurable
      (fun y : ℝ => ∫ x : ℝ, g x * fXY (x, y) ∂volume) := by
    simpa using hGFStrong.integral_prod_left'
  have hFYStrong : StronglyMeasurable
      (fun y : ℝ => thm_13_14_marginalDensity fXY y) := by
    simpa [thm_13_14_marginalDensity] using
      hDensityMeas.stronglyMeasurable.integral_prod_left'
  have hK_eq :
      K =
        fun y : ℝ =>
          (∫ x : ℝ, g x * fXY (x, y) ∂volume) /
            thm_13_14_marginalDensity fXY y := by
    funext y
    dsimp [K]
    unfold thm_13_14_conditionalExpectationKernel thm_13_14_conditionalDensity
    have hfun :
        (fun x : ℝ => g x * (fXY (x, y) / thm_13_14_marginalDensity fXY y)) =
          fun x : ℝ => (g x * fXY (x, y)) /
            thm_13_14_marginalDensity fXY y := by
      funext x
      ring
    rw [hfun, integral_div]
  have hKStrong : StronglyMeasurable K := by
    rw [hK_eq]
    exact hNStrong.div hFYStrong
  have hFStrong : StronglyMeasurable F := by
    dsimp [F]
    exact hDensityMeas.stronglyMeasurable.mul
      (hKStrong.comp_measurable measurable_snd)
  have hAInt : Integrable A volume := by
    refine hAbsInt_prod.integral_norm_prod_right.congr ?_
    filter_upwards with y
    dsimp [A]
    apply integral_congr_ae
    filter_upwards with x
    rw [abs_mul, abs_of_nonneg (abs_nonneg (g x)),
      abs_of_nonneg (hDensityNonneg (x, y))]
  have hBInt :
      Integrable (fun y : ℝ => ∫ x : ℝ, ‖F (x, y)‖ ∂volume) volume := by
    refine hAInt.mono'
      (hFStrong.norm.integral_prod_left'.aestronglyMeasurable) ?_
    filter_upwards [hfxyInt_prod.prod_left_ae] with y hy
    have hB_nonneg : 0 ≤ ∫ x : ℝ, ‖F (x, y)‖ ∂volume :=
      integral_nonneg (fun x => norm_nonneg _)
    have hB_eq :
        (∫ x : ℝ, ‖F (x, y)‖ ∂volume) =
          |K y| * thm_13_14_marginalDensity fXY y := by
      dsimp [F]
      calc
        (∫ x : ℝ, ‖fXY (x, y) * K y‖ ∂volume)
            = ∫ x : ℝ, |K y| * fXY (x, y) ∂volume := by
              apply integral_congr_ae
              filter_upwards with x
              rw [Real.norm_eq_abs, abs_mul,
                abs_of_nonneg (hDensityNonneg (x, y))]
              ring
        _ = |K y| * ∫ x : ℝ, fXY (x, y) ∂volume := by
              rw [integral_const_mul]
        _ = |K y| * thm_13_14_marginalDensity fXY y := by
              rfl
    have hFY_pos : 0 < thm_13_14_marginalDensity fXY y :=
      thm_13_14_marginalDensity_pos_of_nonneg_ne_zero fXY y
        (fun x : ℝ => hDensityNonneg (x, y)) (hFY_ne_zero y)
    have hdom :
        |K y| * thm_13_14_marginalDensity fXY y ≤ A y := by
      dsimp [K, A]
      exact thm_13_14_kernel_abs_mul_marginal_le_integral_abs
        fXY g y (fun x : ℝ => hDensityNonneg (x, y)) hFY_pos
    rw [Real.norm_eq_abs, abs_of_nonneg hB_nonneg]
    exact hB_eq.trans_le hdom
  have hFib : ∀ᵐ y ∂volume, Integrable (fun x : ℝ => F (x, y)) volume := by
    filter_upwards [hfxyInt_prod.prod_left_ae] with y hy
    dsimp [F]
    exact hy.mul_const (K y)
  have hFInt_prod : Integrable F
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    exact (integrable_prod_iff' hFStrong.aestronglyMeasurable).mpr
      ⟨hFib, hBInt⟩
  simpa [F, Measure.volume_eq_prod] using hFInt_prod

 
theorem thm_13_14_interval_weighted_identity
    (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ) (a b : ℝ)
    (hLeftInt : IntegrableOn (fun z : ℝ × ℝ => fXY z * g z.1)
      (thm_13_14_closedIntervalCylinder a b) volume)
    (hRightInt : IntegrableOn
      (fun z : ℝ × ℝ =>
        fXY z * thm_13_14_conditionalExpectationKernel fXY g z.2)
      (thm_13_14_closedIntervalCylinder a b) volume)
    (hFY_ne_zero : ∀ y : ℝ, thm_13_14_marginalDensity fXY y ≠ 0) :
    (∫ z in thm_13_14_closedIntervalCylinder a b, fXY z * g z.1 ∂volume) =
      ∫ z in thm_13_14_closedIntervalCylinder a b,
        fXY z * thm_13_14_conditionalExpectationKernel fXY g z.2 ∂volume := by
  rw [thm_13_14_setIntegral_verticalCylinder_prod_symm _ a b hLeftInt]
  rw [thm_13_14_setIntegral_verticalCylinder_prod_symm _ a b hRightInt]
  apply setIntegral_congr_fun measurableSet_Icc
  intro y _hy
  calc
    (∫ x : ℝ, fXY (x, y) * g x ∂volume)
        = ∫ x : ℝ, g x * fXY (x, y) ∂volume := by
          apply integral_congr_ae
          filter_upwards with x
          ring
    _ = thm_13_14_conditionalExpectationKernel fXY g y *
          thm_13_14_marginalDensity fXY y :=
          (thm_13_14_kernel_mul_marginal_eq_integral
            fXY g y (hFY_ne_zero y)).symm
    _ = (∫ x : ℝ, fXY (x, y) ∂volume) *
          thm_13_14_conditionalExpectationKernel fXY g y := by
          rw [thm_13_14_marginalDensity]
          ring
    _ = ∫ x : ℝ, fXY (x, y) *
          thm_13_14_conditionalExpectationKernel fXY g y ∂volume := by
          rw [integral_mul_const]



theorem thm_13_14_interval_fubini_from_joint_density
    (P : Measure (ℝ × ℝ)) [IsProbabilityMeasure P]
    (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ)
    (hDensity : thm_13_14_jointDensityLaw P fXY)
    (hDensityAEMeas :
      AEMeasurable (fun z : ℝ × ℝ => ENNReal.ofReal (fXY z)) volume)
    (hDensityNonneg : ∀ᵐ z ∂volume, 0 ≤ fXY z)
    (hGWeightedInt : Integrable (fun z : ℝ × ℝ => fXY z * g z.1) volume)
    (hKernelWeightedInt : Integrable
      (fun z : ℝ × ℝ =>
        fXY z * thm_13_14_conditionalExpectationKernel fXY g z.2) volume)
    (hFY_ne_zero : ∀ y : ℝ, thm_13_14_marginalDensity fXY y ≠ 0) :
    thm_13_14_intervalFubiniSupport P fXY g := by
  intro a b _hab
  unfold thm_13_14_integralIdentity
  rw [thm_13_14_setIntegral_jointDensity_eq P fXY (fun z : ℝ × ℝ => g z.1)
    (thm_13_14_closedIntervalCylinder a b)
    (thm_13_14_closedIntervalCylinder_measurable a b)
    hDensity hDensityAEMeas hDensityNonneg]
  rw [thm_13_14_setIntegral_jointDensity_eq P fXY
    (fun z : ℝ × ℝ => thm_13_14_conditionalExpectationKernel fXY g z.2)
    (thm_13_14_closedIntervalCylinder a b)
    (thm_13_14_closedIntervalCylinder_measurable a b)
    hDensity hDensityAEMeas hDensityNonneg]
  exact thm_13_14_interval_weighted_identity fXY g a b
    hGWeightedInt.integrableOn hKernelWeightedInt.integrableOn hFY_ne_zero



theorem thm_13_14_piLambdaExtensionSupport_from_integrable
    (P : Measure (ℝ × ℝ)) (g h : ℝ → ℝ)
    (hGInt : Integrable (fun z : ℝ × ℝ => g z.1) P)
    (hHInt : Integrable (fun z : ℝ × ℝ => h z.2) P) :
    thm_13_14_piLambdaExtensionSupport P g h := by
  intro hIntervals S hS
  let vG : VectorMeasure ℝ ℝ :=
    (P.withDensityᵥ (fun z : ℝ × ℝ => g z.1)).map Prod.snd
  let vH : VectorMeasure ℝ ℝ :=
    (P.withDensityᵥ (fun z : ℝ × ℝ => h z.2)).map Prod.snd
  have hIcc : ∀ a b : ℝ, a ≤ b → vG (Set.Icc a b) = vH (Set.Icc a b) := by
    intro a b hab
    dsimp [vG, vH]
    rw [VectorMeasure.map_apply
        (v := P.withDensityᵥ (fun z : ℝ × ℝ => g z.1))
        measurable_snd measurableSet_Icc,
      VectorMeasure.map_apply
        (v := P.withDensityᵥ (fun z : ℝ × ℝ => h z.2))
        measurable_snd measurableSet_Icc]
    change (P.withDensityᵥ (fun z : ℝ × ℝ => g z.1))
        (thm_13_14_closedIntervalCylinder a b) =
      (P.withDensityᵥ (fun z : ℝ × ℝ => h z.2))
        (thm_13_14_closedIntervalCylinder a b)
    rw [withDensityᵥ_apply hGInt (thm_13_14_closedIntervalCylinder_measurable a b),
      withDensityᵥ_apply hHInt (thm_13_14_closedIntervalCylinder_measurable a b)]
    exact hIntervals a b hab
  have hvEq : vG = vH := phase2_vectorMeasure_ext_of_Icc vG vH hIcc
  have hvG_S : vG S = ∫ z in thm_13_14_verticalCylinder S, g z.1 ∂P := by
    dsimp [vG]
    rw [VectorMeasure.map_apply
      (v := P.withDensityᵥ (fun z : ℝ × ℝ => g z.1)) measurable_snd hS]
    change (P.withDensityᵥ (fun z : ℝ × ℝ => g z.1))
      (thm_13_14_verticalCylinder S) = _
    exact withDensityᵥ_apply hGInt (thm_13_14_verticalCylinder_measurable hS)
  have hvH_S : vH S = ∫ z in thm_13_14_verticalCylinder S, h z.2 ∂P := by
    dsimp [vH]
    rw [VectorMeasure.map_apply
      (v := P.withDensityᵥ (fun z : ℝ × ℝ => h z.2)) measurable_snd hS]
    change (P.withDensityᵥ (fun z : ℝ × ℝ => h z.2))
      (thm_13_14_verticalCylinder S) = _
    exact withDensityᵥ_apply hHInt (thm_13_14_verticalCylinder_measurable hS)
  exact hvG_S.symm.trans
    ((congrArg (fun v : VectorMeasure ℝ ℝ => v S) hvEq).trans hvH_S)



theorem thm_13_14_from_intervalFubini_piLambda
    (P : Measure (ℝ × ℝ)) [IsProbabilityMeasure P]
    (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ)
    (hDensity : thm_13_14_jointDensityLaw P fXY)
    (hGMeas : Measurable g)
    (hDensityMeas : Measurable fXY)
    (hDensityNonneg : ∀ z : ℝ × ℝ, 0 ≤ fXY z)
    (hGWeightedInt : Integrable (fun z : ℝ × ℝ => fXY z * g z.1) volume)
    (hFY_ne_zero : ∀ y : ℝ, thm_13_14_marginalDensity fXY y ≠ 0) :
    thm_13_14_isConditionalExpectationVersion P g
      (thm_13_14_conditionalExpectationKernel fXY g) := by
  have hDensityAEMeas :
      AEMeasurable (fun z : ℝ × ℝ => ENNReal.ofReal (fXY z)) volume :=
    hDensityMeas.ennreal_ofReal.aemeasurable
  have hDensityNonnegAE : ∀ᵐ z ∂volume, 0 ≤ fXY z :=
    ae_of_all _ hDensityNonneg
  have hKernelMeas : Measurable (thm_13_14_conditionalExpectationKernel fXY g) :=
    (thm_13_14_kernel_stronglyMeasurable fXY g hGMeas hDensityMeas).measurable
  have hKernelWeightedInt : Integrable
      (fun z : ℝ × ℝ =>
        fXY z * thm_13_14_conditionalExpectationKernel fXY g z.2) volume :=
    thm_13_14_kernelWeighted_integrable_from_gWeighted P fXY g
      hDensity hGMeas hDensityMeas hDensityNonneg hGWeightedInt hFY_ne_zero
  have hGInt : Integrable (fun z : ℝ × ℝ => g z.1) P :=
    thm_13_14_integrable_under_jointDensity P fXY (fun z : ℝ × ℝ => g z.1)
      hDensity hDensityAEMeas hDensityNonnegAE hGWeightedInt
  have hKernelInt : Integrable
      (fun z : ℝ × ℝ => thm_13_14_conditionalExpectationKernel fXY g z.2) P :=
    thm_13_14_integrable_under_jointDensity P fXY
      (fun z : ℝ × ℝ => thm_13_14_conditionalExpectationKernel fXY g z.2)
      hDensity hDensityAEMeas hDensityNonnegAE hKernelWeightedInt
  have hIntervals : thm_13_14_intervalFubiniSupport P fXY g :=
    thm_13_14_interval_fubini_from_joint_density P fXY g
      hDensity hDensityAEMeas hDensityNonnegAE hGWeightedInt
      hKernelWeightedInt hFY_ne_zero
  have hExtend : thm_13_14_piLambdaExtensionSupport P g
      (thm_13_14_conditionalExpectationKernel fXY g) :=
    thm_13_14_piLambdaExtensionSupport_from_integrable P g
      (thm_13_14_conditionalExpectationKernel fXY g) hGInt hKernelInt
  refine ⟨hKernelMeas, hGInt, hKernelInt, ?_⟩
  intro C hC
  rcases hC with ⟨S, hS, rfl⟩
  exact hExtend hIntervals S hS
