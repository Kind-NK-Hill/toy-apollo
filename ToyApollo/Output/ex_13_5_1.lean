/-
TASK ID: ex_13_5_1
TYPE: Example_Proof
SOURCE PLAN: chapter13-continuous-random-variable
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Phase2.VectorMeasureBorelBridge

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

noncomputable section

def ex_13_5_1_unitSquare : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 1}

def ex_13_5_1_A : Set (ℝ × ℝ) :=
  {z | z.2 < z.1}

def ex_13_5_1_X (z : ℝ × ℝ) : ℝ :=
  z.1

def ex_13_5_1_Z (z : ℝ × ℝ) : ℝ :=
  if z.2 < z.1 then 1 else 0

theorem ex_13_5_1_Z_eq_indicator :
    ex_13_5_1_Z =
      (ex_13_5_1_A.indicator fun _ : ℝ × ℝ => (1 : ℝ)) := by
  funext z
  by_cases h : z.2 < z.1
  · simp [ex_13_5_1_Z, ex_13_5_1_A, h]
  · simp [ex_13_5_1_Z, ex_13_5_1_A, h]

def ex_13_5_1_xCylinder (C : Set ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ∈ C ∧ 0 ≤ z.2 ∧ z.2 ≤ 1}

def ex_13_5_1_yBand : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.2 ∧ z.2 ≤ 1}

theorem ex_13_5_1_xCylinder_eq_preimage_inter_yBand (C : Set ℝ) :
    ex_13_5_1_xCylinder C =
      Prod.fst ⁻¹' C ∩ ex_13_5_1_yBand := by
  ext z
  constructor
  · intro hz
    exact ⟨hz.1, hz.2.1, hz.2.2⟩
  · intro hz
    exact ⟨hz.1, hz.2.1, hz.2.2⟩

theorem ex_13_5_1_xCylinder_measurable
    {C : Set ℝ} (hC : MeasurableSet C) :
    MeasurableSet (ex_13_5_1_xCylinder C) := by
  rw [ex_13_5_1_xCylinder_eq_preimage_inter_yBand C]
  exact (hC.preimage measurable_fst).inter
    (measurableSet_Icc.preimage measurable_snd)

def ex_13_5_1_rectangle (a b : ℝ) : Set (ℝ × ℝ) :=
  ex_13_5_1_xCylinder (Set.Icc a b)

def ex_13_5_1_sigmaXMeasurableSet (B : Set (ℝ × ℝ)) : Prop :=
  ∃ C : Set ℝ, MeasurableSet C ∧ B = ex_13_5_1_xCylinder C

def ex_13_5_1_integralIdentity
    (P : Measure (ℝ × ℝ)) (B : Set (ℝ × ℝ)) : Prop :=
  (∫ z in B, ex_13_5_1_Z z ∂P) =
    ∫ z in B, ex_13_5_1_X z ∂P

def ex_13_5_1_uniformSquareLaw (P : Measure (ℝ × ℝ)) : Prop :=
  ∀ B : Set (ℝ × ℝ), MeasurableSet B →
    P B = volume (B ∩ ex_13_5_1_unitSquare)

theorem ex_13_5_1_uniformMeasure_eq_restrict
    (P : Measure (ℝ × ℝ))
    (hUniform : ex_13_5_1_uniformSquareLaw P) :
    P = volume.restrict ex_13_5_1_unitSquare := by
  apply Measure.ext
  intro s hs
  rw [hUniform s hs, Measure.restrict_apply hs]

theorem ex_13_5_1_rectangle_eq_prod (a b : ℝ) :
    ex_13_5_1_rectangle a b =
      (Set.Icc a b) ×ˢ (Set.Icc (0 : ℝ) 1) := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨hx, hy0, hy1⟩
    exact ⟨⟨hx.1, hx.2⟩, ⟨hy0, hy1⟩⟩
  · intro hz
    rcases hz with ⟨hx, hy⟩
    exact ⟨⟨hx.1, hx.2⟩, hy.1, hy.2⟩

theorem ex_13_5_1_rectangle_subset_unitSquare
    {a b : ℝ} (ha0 : 0 ≤ a) (hb1 : b ≤ 1) :
    ex_13_5_1_rectangle a b ⊆ ex_13_5_1_unitSquare := by
  intro z hz
  rcases hz with ⟨hx, hy0, hy1⟩
  exact ⟨le_trans ha0 hx.1, le_trans hx.2 hb1, hy0, hy1⟩

theorem ex_13_5_1_rectangle_X_integral_uniform
    (a b : ℝ) (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    (∫ z in ex_13_5_1_rectangle a b,
        ex_13_5_1_X z ∂(volume.restrict ex_13_5_1_unitSquare)) =
      (b ^ 2 - a ^ 2) / 2 := by
  have hsub := ex_13_5_1_rectangle_subset_unitSquare (a := a) (b := b) ha0 hb1
  change
    (∫ z, ex_13_5_1_X z ∂
      ((volume.restrict ex_13_5_1_unitSquare).restrict
        (ex_13_5_1_rectangle a b))) =
      (b ^ 2 - a ^ 2) / 2
  rw [Measure.restrict_restrict_of_subset hsub]
  rw [ex_13_5_1_rectangle_eq_prod a b]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [integral_prod]
  · simp [ex_13_5_1_X, integral_const]
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab, integral_id]
  · rw [Measure.prod_restrict]
    exact (ContinuousOn.integrableOn_compact
      ((isCompact_Icc).prod isCompact_Icc)
      (continuous_fst.continuousOn)).integrable

private theorem ex_13_5_1_inner_Z_integral
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (∫ y in Set.Icc (0 : ℝ) 1, if y < x then (1 : ℝ) else 0) = x := by
  have h_ind :
      (fun y : ℝ => if y < x then (1 : ℝ) else 0) =
        (Set.Iio x).indicator (fun _ : ℝ => (1 : ℝ)) := by
    funext y
    by_cases hy : y < x <;> simp [Set.indicator, hy]
  rw [h_ind, MeasureTheory.setIntegral_indicator measurableSet_Iio]
  have hset : Set.Icc (0 : ℝ) 1 ∩ Set.Iio x = Set.Ico (0 : ℝ) x := by
    ext y
    constructor
    · intro hy
      exact ⟨hy.1.1, hy.2⟩
    · intro hy
      exact ⟨⟨hy.1, le_trans hy.2.le hx1⟩, hy.2⟩
  rw [hset, MeasureTheory.setIntegral_const]
  simp [Real.volume_real_Ico_of_le hx0]

theorem ex_13_5_1_rectangle_Z_integral_uniform
    (a b : ℝ) (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    (∫ z in ex_13_5_1_rectangle a b,
        ex_13_5_1_Z z ∂(volume.restrict ex_13_5_1_unitSquare)) =
      (b ^ 2 - a ^ 2) / 2 := by
  have hsub := ex_13_5_1_rectangle_subset_unitSquare (a := a) (b := b) ha0 hb1
  change
    (∫ z, ex_13_5_1_Z z ∂
      ((volume.restrict ex_13_5_1_unitSquare).restrict
        (ex_13_5_1_rectangle a b))) =
      (b ^ 2 - a ^ 2) / 2
  rw [Measure.restrict_restrict_of_subset hsub]
  rw [ex_13_5_1_rectangle_eq_prod a b]
  rw [Measure.volume_eq_prod ℝ ℝ]
  have hAmeas : MeasurableSet ex_13_5_1_A := by
    simpa [ex_13_5_1_A] using measurableSet_lt measurable_snd measurable_fst
  have hfinite :
      (volume.prod volume) (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) ≠ ⊤ := by
    rw [Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hZint : IntegrableOn ex_13_5_1_Z
      (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) (volume.prod volume) := by
    rw [ex_13_5_1_Z_eq_indicator]
    exact (integrableOn_const (C := (1 : ℝ))
      (s := Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1)
      (μ := volume.prod volume) (hs := hfinite)).indicator hAmeas
  calc
    ∫ z in Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1,
        ex_13_5_1_Z z ∂volume.prod volume
        = ∫ x in Set.Icc a b,
            ∫ y in Set.Icc (0 : ℝ) 1, ex_13_5_1_Z (x, y) ∂volume ∂volume := by
          exact MeasureTheory.setIntegral_prod
            (μ := volume) (ν := volume) (f := ex_13_5_1_Z)
            (s := Set.Icc a b) (t := Set.Icc (0 : ℝ) 1) hZint
    _ = ∫ x in Set.Icc a b, x := by
          exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun x hx => by
            have hx0 : 0 ≤ x := le_trans ha0 hx.1
            have hx1 : x ≤ 1 := le_trans hx.2 hb1
            simpa [ex_13_5_1_Z] using ex_13_5_1_inner_Z_integral x hx0 hx1)
    _ = (b ^ 2 - a ^ 2) / 2 := by
          rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le hab, integral_id]

def ex_13_5_1_rectangleAreaSupport
    (P : Measure (ℝ × ℝ)) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    (∫ z in ex_13_5_1_rectangle a b, ex_13_5_1_Z z ∂P) =
        (b ^ 2 - a ^ 2) / 2 ∧
      (∫ z in ex_13_5_1_rectangle a b, ex_13_5_1_X z ∂P) =
        (b ^ 2 - a ^ 2) / 2

theorem ex_13_5_1_rectangleAreaSupport_of_uniformSquareLaw
    (P : Measure (ℝ × ℝ))
    (hUniform : ex_13_5_1_uniformSquareLaw P) :
    ex_13_5_1_rectangleAreaSupport P := by
  have hP := ex_13_5_1_uniformMeasure_eq_restrict P hUniform
  intro a b ha0 hab hb1
  rw [hP]
  exact ⟨
    ex_13_5_1_rectangle_Z_integral_uniform a b ha0 hab hb1,
    ex_13_5_1_rectangle_X_integral_uniform a b ha0 hab hb1⟩

theorem ex_13_5_1_xCylinderIntegralIdentity_uniform
    (C : Set ℝ) (hC : MeasurableSet C) :
    ex_13_5_1_integralIdentity (volume.restrict ex_13_5_1_unitSquare)
      (ex_13_5_1_xCylinder C) := by
  let S : Set ℝ := C ∩ Set.Icc (0 : ℝ) 1
  have hCylMeas : MeasurableSet (ex_13_5_1_xCylinder C) := by
    have h1 : MeasurableSet {z : ℝ × ℝ | z.1 ∈ C} :=
      hC.preimage measurable_fst
    have h2 : MeasurableSet {z : ℝ × ℝ | z.2 ∈ Set.Icc (0 : ℝ) 1} :=
      measurableSet_Icc.preimage measurable_snd
    change MeasurableSet
      ({z : ℝ × ℝ | z.1 ∈ C} ∩
        {z : ℝ × ℝ | z.2 ∈ Set.Icc (0 : ℝ) 1})
    exact h1.inter h2
  have hset : ex_13_5_1_xCylinder C ∩ ex_13_5_1_unitSquare =
      S ×ˢ Set.Icc (0 : ℝ) 1 := by
    ext z
    constructor
    · intro hz
      exact ⟨⟨hz.1.1, ⟨hz.2.1, hz.2.2.1⟩⟩, ⟨hz.1.2.1, hz.1.2.2⟩⟩
    · intro hz
      exact ⟨
        ⟨hz.1.1, hz.2.1, hz.2.2⟩,
        ⟨hz.1.2.1, hz.1.2.2, hz.2.1, hz.2.2⟩⟩
  have hSmeas : MeasurableSet S := hC.inter measurableSet_Icc
  have hTfinite : volume (Set.Icc (0 : ℝ) 1) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hSfinite : volume S ≠ ⊤ :=
    ne_top_of_le_ne_top hTfinite
      (MeasureTheory.measure_mono Set.inter_subset_right)
  have hfinite :
      (volume.prod volume) (S ×ˢ Set.Icc (0 : ℝ) 1) ≠ ⊤ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hSfinite hTfinite
  have hAmeas : MeasurableSet ex_13_5_1_A := by
    simpa [ex_13_5_1_A] using measurableSet_lt measurable_snd measurable_fst
  have hZint : IntegrableOn ex_13_5_1_Z
      (S ×ˢ Set.Icc (0 : ℝ) 1) (volume.prod volume) := by
    rw [ex_13_5_1_Z_eq_indicator]
    exact (integrableOn_const (C := (1 : ℝ))
      (s := S ×ˢ Set.Icc (0 : ℝ) 1)
      (μ := volume.prod volume) (hs := hfinite)).indicator hAmeas
  have hXint_full : IntegrableOn ex_13_5_1_X
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) (volume.prod volume) := by
    exact (ContinuousOn.integrableOn_compact
      ((isCompact_Icc).prod isCompact_Icc)
      (continuous_fst.continuousOn)).integrable
  have hXint : IntegrableOn ex_13_5_1_X
      (S ×ˢ Set.Icc (0 : ℝ) 1) (volume.prod volume) := by
    exact hXint_full.mono_set (by
      intro z hz
      exact ⟨hz.1.2, hz.2⟩)
  have hZcalc :
      (∫ z in S ×ˢ Set.Icc (0 : ℝ) 1,
          ex_13_5_1_Z z ∂volume.prod volume) = ∫ x in S, x := by
    calc
      ∫ z in S ×ˢ Set.Icc (0 : ℝ) 1, ex_13_5_1_Z z ∂volume.prod volume
          = ∫ x in S,
              ∫ y in Set.Icc (0 : ℝ) 1, ex_13_5_1_Z (x, y) ∂volume ∂volume := by
            exact MeasureTheory.setIntegral_prod
              (μ := volume) (ν := volume) (f := ex_13_5_1_Z)
              (s := S) (t := Set.Icc (0 : ℝ) 1) hZint
      _ = ∫ x in S, x := by
            exact MeasureTheory.setIntegral_congr_fun hSmeas (fun x hx => by
              have hx0 : 0 ≤ x := hx.2.1
              have hx1 : x ≤ 1 := hx.2.2
              simpa [ex_13_5_1_Z] using ex_13_5_1_inner_Z_integral x hx0 hx1)
  have hXcalc :
      (∫ z in S ×ˢ Set.Icc (0 : ℝ) 1,
          ex_13_5_1_X z ∂volume.prod volume) = ∫ x in S, x := by
    calc
      ∫ z in S ×ˢ Set.Icc (0 : ℝ) 1, ex_13_5_1_X z ∂volume.prod volume
          = ∫ x in S,
              ∫ y in Set.Icc (0 : ℝ) 1, ex_13_5_1_X (x, y) ∂volume ∂volume := by
            exact MeasureTheory.setIntegral_prod
              (μ := volume) (ν := volume) (f := ex_13_5_1_X)
              (s := S) (t := Set.Icc (0 : ℝ) 1) hXint
      _ = ∫ x in S, x := by
            exact MeasureTheory.setIntegral_congr_fun hSmeas (fun x _hx => by
              simp [ex_13_5_1_X])
  change
    (∫ z, ex_13_5_1_Z z ∂
      ((volume.restrict ex_13_5_1_unitSquare).restrict
        (ex_13_5_1_xCylinder C))) =
      ∫ z, ex_13_5_1_X z ∂
        ((volume.restrict ex_13_5_1_unitSquare).restrict
          (ex_13_5_1_xCylinder C))
  rw [Measure.restrict_restrict hCylMeas, hset, Measure.volume_eq_prod ℝ ℝ]
  exact hZcalc.trans hXcalc.symm

theorem ex_13_5_1_xCylinderIntegralIdentity_of_uniformSquareLaw
    (P : Measure (ℝ × ℝ))
    (hUniform : ex_13_5_1_uniformSquareLaw P)
    (C : Set ℝ) (hC : MeasurableSet C) :
    ex_13_5_1_integralIdentity P (ex_13_5_1_xCylinder C) := by
  rw [ex_13_5_1_uniformMeasure_eq_restrict P hUniform]
  exact ex_13_5_1_xCylinderIntegralIdentity_uniform C hC

private theorem ex_13_5_1_rectangleIntegralIdentity
    (P : Measure (ℝ × ℝ))
    (hArea : ex_13_5_1_rectangleAreaSupport P)
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    ex_13_5_1_integralIdentity P (ex_13_5_1_rectangle a b) := by
  rcases hArea a b ha0 hab hb1 with ⟨hZ, hX⟩
  exact hZ.trans hX.symm

def ex_13_5_1_piLambdaExtensionSupport
    (P : Measure (ℝ × ℝ)) : Prop :=
  (∀ a b : ℝ, a ≤ b →
    ex_13_5_1_integralIdentity P (ex_13_5_1_rectangle a b)) →
    ∀ C : Set ℝ, MeasurableSet C →
      ex_13_5_1_integralIdentity P (ex_13_5_1_xCylinder C)

private theorem ex_13_5_1_vectorMeasure_value
    (P : Measure (ℝ × ℝ)) (f : ℝ × ℝ → ℝ)
    (hf : Integrable f (P.restrict ex_13_5_1_yBand))
    (C : Set ℝ) (hC : MeasurableSet C) :
    (((P.restrict ex_13_5_1_yBand).withDensityᵥ f).map Prod.fst) C =
      ∫ z in ex_13_5_1_xCylinder C, f z ∂P := by
  rw [VectorMeasure.map_apply
    (v := (P.restrict ex_13_5_1_yBand).withDensityᵥ f)
    measurable_fst hC]
  rw [withDensityᵥ_apply hf (hC.preimage measurable_fst)]
  change (∫ z, f z ∂
      ((P.restrict ex_13_5_1_yBand).restrict (Prod.fst ⁻¹' C))) =
    ∫ z, f z ∂(P.restrict (ex_13_5_1_xCylinder C))
  rw [Measure.restrict_restrict (hC.preimage measurable_fst)]
  rw [ex_13_5_1_xCylinder_eq_preimage_inter_yBand C]

theorem ex_13_5_1_piLambdaExtensionSupport_from_integrable
    (P : Measure (ℝ × ℝ))
    (hZInt : Integrable ex_13_5_1_Z P)
    (hXInt : Integrable ex_13_5_1_X P) :
    ex_13_5_1_piLambdaExtensionSupport P := by
  intro hIntervals C hC
  let PY : Measure (ℝ × ℝ) := P.restrict ex_13_5_1_yBand
  let vZ : VectorMeasure ℝ ℝ := (PY.withDensityᵥ ex_13_5_1_Z).map Prod.fst
  let vX : VectorMeasure ℝ ℝ := (PY.withDensityᵥ ex_13_5_1_X).map Prod.fst
  have hZIntY : Integrable ex_13_5_1_Z PY :=
    hZInt.mono_measure Measure.restrict_le_self
  have hXIntY : Integrable ex_13_5_1_X PY :=
    hXInt.mono_measure Measure.restrict_le_self
  have hIcc : ∀ a b : ℝ, a ≤ b → vZ (Set.Icc a b) = vX (Set.Icc a b) := by
    intro a b hab
    have hZ :=
      ex_13_5_1_vectorMeasure_value P ex_13_5_1_Z hZIntY
        (Set.Icc a b) measurableSet_Icc
    have hX :=
      ex_13_5_1_vectorMeasure_value P ex_13_5_1_X hXIntY
        (Set.Icc a b) measurableSet_Icc
    exact hZ.trans ((hIntervals a b hab).trans hX.symm)
  have hvEq : vZ = vX := phase2_vectorMeasure_ext_of_Icc vZ vX hIcc
  have hZC := ex_13_5_1_vectorMeasure_value P ex_13_5_1_Z hZIntY C hC
  have hXC := ex_13_5_1_vectorMeasure_value P ex_13_5_1_X hXIntY C hC
  exact hZC.symm.trans ((congrArg (fun v : VectorMeasure ℝ ℝ => v C) hvEq).trans hXC)

def ex_13_5_1_isConditionalExpectationVersion
    (P : Measure (ℝ × ℝ)) : Prop :=
  ∀ B : Set (ℝ × ℝ), ex_13_5_1_sigmaXMeasurableSet B →
    ex_13_5_1_integralIdentity P B

theorem ex_13_5_1
    (P : Measure (ℝ × ℝ)) [IsProbabilityMeasure P]
    (hUniform : ex_13_5_1_uniformSquareLaw P) :
    ex_13_5_1_isConditionalExpectationVersion P := by
  have hArea : ex_13_5_1_rectangleAreaSupport P :=
    ex_13_5_1_rectangleAreaSupport_of_uniformSquareLaw P hUniform
  have hZInt : Integrable ex_13_5_1_Z P := by
    rw [ex_13_5_1_Z_eq_indicator]
    exact (integrable_const (c := (1 : ℝ))).indicator
      (by simpa [ex_13_5_1_A] using measurableSet_lt measurable_snd measurable_fst)
  have hXInt : Integrable ex_13_5_1_X P := by
    rw [ex_13_5_1_uniformMeasure_eq_restrict P hUniform]
    have hsq :
        ex_13_5_1_unitSquare =
          Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
      ext z
      constructor
      · intro hz
        exact ⟨⟨hz.1, hz.2.1⟩, ⟨hz.2.2.1, hz.2.2.2⟩⟩
      · intro hz
        exact ⟨hz.1.1, hz.1.2, hz.2.1, hz.2.2⟩
    rw [hsq]
    exact (ContinuousOn.integrableOn_compact
      ((isCompact_Icc).prod isCompact_Icc)
      (continuous_fst.continuousOn)).integrable
  have hIntervals :
      ∀ a b : ℝ, a ≤ b →
        ex_13_5_1_integralIdentity P (ex_13_5_1_rectangle a b) := by
    intro a b hab
    by_cases ha0 : 0 ≤ a
    · by_cases hb1 : b ≤ 1
      · exact ex_13_5_1_rectangleIntegralIdentity P hArea ha0 hab hb1
      · exact ex_13_5_1_xCylinderIntegralIdentity_of_uniformSquareLaw
          P hUniform (Set.Icc a b) measurableSet_Icc
    · exact ex_13_5_1_xCylinderIntegralIdentity_of_uniformSquareLaw
        P hUniform (Set.Icc a b) measurableSet_Icc
  have hExtend : ex_13_5_1_piLambdaExtensionSupport P :=
    ex_13_5_1_piLambdaExtensionSupport_from_integrable P hZInt hXInt
  intro B hB
  rcases hB with ⟨C, hC, rfl⟩
  exact hExtend hIntervals C hC
