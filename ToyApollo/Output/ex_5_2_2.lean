/-
TASK ID: ex_5_2_2
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_5_4

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable def dependentPairPdf (x y : ℝ) : ℝ :=
  if x ∈ Set.Icc (-1 : ℝ) 1 ∧ y ∈ Set.Icc (-1 : ℝ) 1 then
    ((1 : ℝ) / 4) * (1 + x * y)
  else
    0

noncomputable def dependentPairMarginalPdf (x : ℝ) : ℝ :=
  if x ∈ Set.Icc (-1 : ℝ) 1 then (1 : ℝ) / 2 else 0

def dependentPairSupport : Set (ℝ × ℝ) :=
  Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1

noncomputable def dependentPairMeasure : Measure (ℝ × ℝ) :=
  (volume : Measure (ℝ × ℝ)).withDensity
    (fun z => ENNReal.ofReal (dependentPairPdf z.1 z.2))

def dependentX : ℝ × ℝ → ℝ := Prod.fst

def dependentY : ℝ × ℝ → ℝ := Prod.snd

lemma dependentX_measurable : Measurable dependentX := by
  simpa [dependentX] using measurable_fst

lemma dependentY_measurable : Measurable dependentY := by
  simpa [dependentY] using measurable_snd

theorem dependentPairPdf_at_one :
    dependentPairPdf 1 1 = (1 : ℝ) / 2 := by
  norm_num [dependentPairPdf]

theorem dependentPairMarginalPdf_on_support {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    dependentPairMarginalPdf x = (1 : ℝ) / 2 := by
  simp [dependentPairMarginalPdf, hx]

theorem dependentPairPdf_not_factorized_at_one :
    dependentPairPdf 1 1 ≠ dependentPairMarginalPdf 1 * dependentPairMarginalPdf 1 := by
  rw [dependentPairPdf_at_one, dependentPairMarginalPdf_on_support (by constructor <;> norm_num)]
  norm_num

noncomputable def squarePairMarginalCdf (x : ℝ) : ENNReal :=
  if x < 0 then 0 else if x ≤ 1 then ENNReal.ofReal (Real.sqrt x) else 1

theorem squarePairMarginalCdf_on_unit_interval {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    squarePairMarginalCdf x = ENNReal.ofReal (Real.sqrt x) := by
  have hx_nonneg : ¬ x < 0 := not_lt.mpr hx.1
  have hx_le_one : x ≤ 1 := hx.2
  simp [squarePairMarginalCdf, hx_nonneg, hx_le_one]

lemma integral_Icc_id {u v : ℝ} (huv : u ≤ v) :
    ∫ x in Set.Icc u v, x ∂(volume : Measure ℝ) = (v ^ 2 - u ^ 2) / 2 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le huv, integral_id]

lemma integral_Icc_one {u v : ℝ} (huv : u ≤ v) :
    ∫ x in Set.Icc u v, (1 : ℝ) ∂(volume : Measure ℝ) = v - u := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le huv,
    intervalIntegral.integral_const]
  simp [smul_eq_mul]

lemma dependentPairPdf_eq_poly_on_rect
    {u v w t : ℝ}
    (hu : -1 ≤ u) (huv : u ≤ v) (hv : v ≤ 1)
    (hw : -1 ≤ w) (hwt : w ≤ t) (ht : t ≤ 1) :
    EqOn
      (fun z : ℝ × ℝ => dependentPairPdf z.1 z.2)
      (fun z : ℝ × ℝ => (1 / 4 : ℝ) + (1 / 4 : ℝ) * (z.1 * z.2))
      (Set.Icc u v ×ˢ Set.Icc w t) := by
  intro z hz
  have hx : z.1 ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hu, huv, hv, hz.1.1, hz.1.2]
  have hy : z.2 ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hw, hwt, ht, hz.2.1, hz.2.2]
  simp [dependentPairPdf, hx, hy]
  ring

lemma dependentPairPdf_integral_on_rect
    {u v w t : ℝ}
    (hu : -1 ≤ u) (huv : u ≤ v) (hv : v ≤ 1)
    (hw : -1 ≤ w) (hwt : w ≤ t) (ht : t ≤ 1) :
    ∫ z in Set.Icc u v ×ˢ Set.Icc w t, dependentPairPdf z.1 z.2
      ∂(volume : Measure (ℝ × ℝ)) =
      ((v - u) * (t - w)) / 4 + (((v ^ 2 - u ^ 2) / 2) * ((t ^ 2 - w ^ 2) / 2)) / 4 := by
  let s : Set ℝ := Set.Icc u v
  let r : Set ℝ := Set.Icc w t
  let μ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume
  have hs : MeasurableSet s := by
    dsimp [s]
    exact measurableSet_Icc
  have hr : MeasurableSet r := by
    dsimp [r]
    exact measurableSet_Icc
  have hEq :
      EqOn
        (fun z : ℝ × ℝ => dependentPairPdf z.1 z.2)
        (fun z : ℝ × ℝ => (1 / 4 : ℝ) + (1 / 4 : ℝ) * (z.1 * z.2))
        (s ×ˢ r) := by
    simpa [s, r] using dependentPairPdf_eq_poly_on_rect hu huv hv hw hwt ht
  have hμBox : μ (s ×ˢ r) ≠ ∞ := by
    exact ne_of_lt (((isCompact_Icc).prod isCompact_Icc).measure_lt_top (μ := μ))
  have hIntConst : IntegrableOn (fun _ : ℝ × ℝ => (1 / 4 : ℝ)) (s ×ˢ r) μ := by
    exact integrableOn_const (μ := μ) (s := s ×ˢ r) (C := (1 / 4 : ℝ)) hμBox
  have hIntMul : IntegrableOn (fun z : ℝ × ℝ => (1 / 4 : ℝ) * (z.1 * z.2)) (s ×ˢ r) μ := by
    have hcont : ContinuousOn (fun z : ℝ × ℝ => (1 / 4 : ℝ) * (z.1 * z.2)) (s ×ˢ r) := by
      change ContinuousOn
        ((fun _ : ℝ × ℝ => (1 / 4 : ℝ)) * (Prod.fst * Prod.snd)) (s ×ˢ r)
      exact (continuous_const.mul (continuous_fst.mul continuous_snd)).continuousOn
    exact hcont.integrableOn_compact ((isCompact_Icc).prod isCompact_Icc)
  change
    ∫ z in s ×ˢ r, dependentPairPdf z.1 z.2 ∂μ =
      ((v - u) * (t - w)) / 4 + (((v ^ 2 - u ^ 2) / 2) * ((t ^ 2 - w ^ 2) / 2)) / 4
  rw [MeasureTheory.setIntegral_congr_fun (hs.prod hr) hEq]
  rw [integral_add hIntConst hIntMul]
  rw [show ∫ z in s ×ˢ r, (1 / 4 : ℝ) ∂μ = (1 / 4 : ℝ) * ∫ z in s ×ˢ r, (1 : ℝ) ∂μ by
      simpa [μ, smul_eq_mul] using
        (integral_const_mul (μ := μ.restrict (s ×ˢ r)) (r := (1 / 4 : ℝ))
          (f := fun _ : ℝ × ℝ => (1 : ℝ)))]
  rw [show ∫ z in s ×ˢ r, (1 : ℝ) ∂μ =
      (∫ x in s, (1 : ℝ) ∂(volume : Measure ℝ)) *
        ∫ y in r, (1 : ℝ) ∂(volume : Measure ℝ) by
      simpa [μ] using
        (MeasureTheory.setIntegral_prod_mul (fun _ : ℝ => (1 : ℝ)) (fun _ : ℝ => (1 : ℝ)) s r)]
  rw [show ∫ z in s ×ˢ r, (1 / 4 : ℝ) * (z.1 * z.2) ∂μ =
      (1 / 4 : ℝ) * ∫ z in s ×ˢ r, z.1 * z.2 ∂μ by
      simpa [μ, smul_eq_mul] using
        (integral_const_mul (μ := μ.restrict (s ×ˢ r)) (r := (1 / 4 : ℝ))
          (f := fun z : ℝ × ℝ => z.1 * z.2))]
  rw [show ∫ z in s ×ˢ r, z.1 * z.2 ∂μ =
      (∫ x in s, x ∂(volume : Measure ℝ)) *
        ∫ y in r, y ∂(volume : Measure ℝ) by
      simpa [μ] using
        (MeasureTheory.setIntegral_prod_mul (fun x : ℝ => x) (fun y : ℝ => y) s r)]
  rw [integral_Icc_one huv, integral_Icc_one hwt, integral_Icc_id huv, integral_Icc_id hwt]
  ring

lemma dependentPairPdf_nonneg_on_rect
    {u v w t : ℝ}
    (hu : -1 ≤ u) (huv : u ≤ v) (hv : v ≤ 1)
    (hw : -1 ≤ w) (hwt : w ≤ t) (ht : t ≤ 1) :
    0 ≤ᵐ[(volume : Measure (ℝ × ℝ)).restrict (Set.Icc u v ×ˢ Set.Icc w t)]
      fun z : ℝ × ℝ => (1 / 4 : ℝ) + (1 / 4 : ℝ) * (z.1 * z.2) := by
  refine (ae_restrict_iff' (μ := (volume : Measure (ℝ × ℝ)))
    (measurableSet_Icc.prod measurableSet_Icc)).2 ?_
  refine Filter.Eventually.of_forall ?_
  intro z hz
  have hz1 : z.1 ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hu, huv, hv, hz.1.1, hz.1.2]
  have hz2 : z.2 ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hw, hwt, ht, hz.2.1, hz.2.2]
  have hmul : -1 ≤ z.1 * z.2 := by
    nlinarith [hz1.1, hz1.2, hz2.1, hz2.2]
  have hsum : 0 ≤ 1 + z.1 * z.2 := by
    linarith
  have htarget : 0 ≤ (1 / 4 : ℝ) + (1 / 4 : ℝ) * (z.1 * z.2) := by
    nlinarith [hsum]
  exact htarget

lemma dependentPairMeasure_rect
    {u v w t : ℝ}
    (hu : -1 ≤ u) (huv : u ≤ v) (hv : v ≤ 1)
    (hw : -1 ≤ w) (hwt : w ≤ t) (ht : t ≤ 1) :
    dependentPairMeasure (Set.Icc u v ×ˢ Set.Icc w t) =
      ENNReal.ofReal
        (((v - u) * (t - w)) / 4 + (((v ^ 2 - u ^ 2) / 2) * ((t ^ 2 - w ^ 2) / 2)) / 4) := by
  let box : Set (ℝ × ℝ) := Set.Icc u v ×ˢ Set.Icc w t
  let poly : ℝ × ℝ → ℝ := fun z => (1 / 4 : ℝ) + (1 / 4 : ℝ) * (z.1 * z.2)
  have hBoxMeas : MeasurableSet box := by
    dsimp [box]
    exact measurableSet_Icc.prod measurableSet_Icc
  have hEqOn :
      EqOn (fun z : ℝ × ℝ => dependentPairPdf z.1 z.2) poly box := by
    simpa [box, poly] using dependentPairPdf_eq_poly_on_rect hu huv hv hw hwt ht
  have hIntPolyOn : IntegrableOn poly box (volume : Measure (ℝ × ℝ)) := by
    have hμBox : (volume : Measure (ℝ × ℝ)) box ≠ ∞ := by
      exact ne_of_lt (((isCompact_Icc).prod isCompact_Icc).measure_lt_top (μ := (volume : Measure (ℝ × ℝ))))
    have hIntConst :
        IntegrableOn (fun _ : ℝ × ℝ => (1 / 4 : ℝ)) box (volume : Measure (ℝ × ℝ)) := by
      exact integrableOn_const (μ := (volume : Measure (ℝ × ℝ))) (s := box) (C := (1 / 4 : ℝ))
        hμBox
    have hIntMul :
        IntegrableOn (fun z : ℝ × ℝ => (1 / 4 : ℝ) * (z.1 * z.2)) box (volume : Measure (ℝ × ℝ)) := by
      have hcont : ContinuousOn (fun z : ℝ × ℝ => (1 / 4 : ℝ) * (z.1 * z.2)) box := by
        change ContinuousOn
          ((fun _ : ℝ × ℝ => (1 / 4 : ℝ)) * (Prod.fst * Prod.snd)) box
        exact (continuous_const.mul (continuous_fst.mul continuous_snd)).continuousOn
      exact hcont.integrableOn_compact ((isCompact_Icc).prod isCompact_Icc)
    change IntegrableOn
      ((fun _ : ℝ × ℝ => (1 / 4 : ℝ)) +
        (fun z : ℝ × ℝ => (1 / 4 : ℝ) * (z.1 * z.2)))
      box (volume : Measure (ℝ × ℝ))
    exact hIntConst.add hIntMul
  have hNonnegPoly :
      0 ≤ᵐ[(volume : Measure (ℝ × ℝ)).restrict box] poly := by
    simpa [box, poly] using dependentPairPdf_nonneg_on_rect hu huv hv hw hwt ht
  have hEqAe :
      (fun z : ℝ × ℝ => ENNReal.ofReal (dependentPairPdf z.1 z.2)) =ᵐ[
        (volume : Measure (ℝ × ℝ)).restrict box] fun z => ENNReal.ofReal (poly z) := by
    refine (ae_restrict_iff' (μ := (volume : Measure (ℝ × ℝ))) hBoxMeas).2 ?_
    exact Filter.Eventually.of_forall fun z hz => by
      simp [hEqOn hz]
  rw [dependentPairMeasure, withDensity_apply _ hBoxMeas]
  calc
    ∫⁻ z in box, ENNReal.ofReal (dependentPairPdf z.1 z.2) ∂(volume : Measure (ℝ × ℝ)) =
        ∫⁻ z in box, ENNReal.ofReal (poly z) ∂(volume : Measure (ℝ × ℝ)) := by
          apply lintegral_congr_ae
          exact hEqAe
    _ = ENNReal.ofReal (∫ z in box, poly z ∂(volume : Measure (ℝ × ℝ))) := by
          symm
          simpa [box, IntegrableOn] using
            (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
              (μ := (volume : Measure (ℝ × ℝ)).restrict box)
              hIntPolyOn hNonnegPoly)
    _ = ENNReal.ofReal (∫ z in box, dependentPairPdf z.1 z.2 ∂(volume : Measure (ℝ × ℝ))) := by
          congr 1
          symm
          exact MeasureTheory.setIntegral_congr_fun hBoxMeas hEqOn
    _ = ENNReal.ofReal
        (((v - u) * (t - w)) / 4 + (((v ^ 2 - u ^ 2) / 2) * ((t ^ 2 - w ^ 2) / 2)) / 4) := by
          rw [dependentPairPdf_integral_on_rect hu huv hv hw hwt ht]

lemma dependentPairMeasure_support :
    dependentPairMeasure dependentPairSupport = 1 := by
  have h :=
    dependentPairMeasure_rect (u := -1) (v := 1) (w := -1) (t := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  simpa [dependentPairSupport] using h

lemma dependentPairMeasure_support_compl :
    dependentPairMeasure dependentPairSupportᶜ = 0 := by
  rw [dependentPairMeasure, dependentPairSupport,
    withDensity_apply _ (measurableSet_Icc.prod measurableSet_Icc).compl]
  refine MeasureTheory.setLIntegral_eq_zero (measurableSet_Icc.prod measurableSet_Icc).compl ?_
  intro z hz
  by_cases hmem : z.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ z.2 ∈ Set.Icc (-1 : ℝ) 1
  · exfalso
    have hz' : z ∉ Set.Icc ((-1 : ℝ), -1) (1, 1) := by
      simpa [Icc_prod_Icc] using hz
    have hzbox : z ∈ Set.Icc ((-1 : ℝ), -1) (1, 1) := by
      exact ⟨⟨hmem.1.1, hmem.2.1⟩, ⟨hmem.1.2, hmem.2.2⟩⟩
    exact hz' hzbox
  · have hmem' : ¬ (((-1 ≤ z.1 ∧ z.1 ≤ 1) ∧ -1 ≤ z.2 ∧ z.2 ≤ 1) : Prop) := by
      simpa using hmem
    have hzero : dependentPairPdf z.1 z.2 = 0 := by
      simp [dependentPairPdf, hmem']
    simp [hzero]

noncomputable instance : IsProbabilityMeasure dependentPairMeasure := by
  refine ⟨?_⟩
  calc
    dependentPairMeasure Set.univ =
        dependentPairMeasure dependentPairSupport +
          dependentPairMeasure dependentPairSupportᶜ := by
            rw [← union_compl_self dependentPairSupport]
            exact measure_union disjoint_compl_right (measurableSet_Icc.prod measurableSet_Icc).compl
    _ = 1 := by rw [dependentPairMeasure_support, dependentPairMeasure_support_compl, add_zero]

lemma dependentPairMeasure_eq_inter_support {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    dependentPairMeasure A = dependentPairMeasure (A ∩ dependentPairSupport) := by
  have hzero : dependentPairMeasure (A ∩ dependentPairSupportᶜ) = 0 := by
    exact measure_mono_null (by intro z hz; exact hz.2) dependentPairMeasure_support_compl
  calc
    dependentPairMeasure A =
        dependentPairMeasure ((A ∩ dependentPairSupport) ∪ (A ∩ dependentPairSupportᶜ)) := by
          rw [inter_union_compl]
    _ = dependentPairMeasure (A ∩ dependentPairSupport) +
          dependentPairMeasure (A ∩ dependentPairSupportᶜ) := by
            refine measure_union ?_ ?_
            · exact Set.disjoint_left.2 fun z hz1 hz2 => hz2.2 hz1.2
            · exact hA.inter (measurableSet_Icc.prod measurableSet_Icc).compl
    _ = dependentPairMeasure (A ∩ dependentPairSupport) := by rw [hzero, add_zero]

lemma square_preimage_eq_symm_Icc {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ((fun u : ℝ => u ^ 2) ⁻¹' Set.Iic x) ∩ Set.Icc (-1 : ℝ) 1 =
      Set.Icc (-Real.sqrt x) (Real.sqrt x) := by
  ext u
  constructor
  · intro hu
    have hsquare : u ^ 2 ≤ (Real.sqrt x) ^ 2 := by
      simpa [Real.sq_sqrt hx.1] using hu.1
    have habs : |u| ≤ Real.sqrt x := by
      simpa [abs_of_nonneg (Real.sqrt_nonneg x)] using (sq_le_sq).1 hsquare
    exact abs_le.mp (by simpa using habs)
  · intro hu
    have hsquare : u ^ 2 ≤ (Real.sqrt x) ^ 2 := by
      nlinarith [hu.1, hu.2, Real.sqrt_nonneg x]
    have : u ^ 2 ≤ x := by simpa [Real.sq_sqrt hx.1] using hsquare
    have hsqrt_le_one : Real.sqrt x ≤ 1 := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · simpa using hx.2
    have hneg : (-1 : ℝ) ≤ -Real.sqrt x := by
      linarith
    exact ⟨this, ⟨le_trans hneg hu.1, le_trans hu.2 hsqrt_le_one⟩⟩

lemma fstSquare_preimage_inter_support {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ((fun z : ℝ × ℝ => z.1 ^ 2) ⁻¹' Set.Iic x) ∩ dependentPairSupport =
      Set.Icc (-Real.sqrt x) (Real.sqrt x) ×ˢ Set.Icc (-1 : ℝ) 1 := by
  ext z
  constructor
  · intro hz
    have hz1 : z.1 ∈ ((fun u : ℝ => u ^ 2) ⁻¹' Set.Iic x) ∩ Set.Icc (-1 : ℝ) 1 := by
      exact ⟨hz.1, hz.2.1⟩
    have hz1' : z.1 ∈ Set.Icc (-Real.sqrt x) (Real.sqrt x) := by
      simpa [square_preimage_eq_symm_Icc (x := x) hx] using hz1
    exact ⟨hz1', hz.2.2⟩
  · intro hz
    have hz1 : z.1 ∈ ((fun u : ℝ => u ^ 2) ⁻¹' Set.Iic x) ∩ Set.Icc (-1 : ℝ) 1 := by
      simpa [square_preimage_eq_symm_Icc (x := x) hx] using hz.1
    exact ⟨hz1.1, ⟨hz1.2, hz.2⟩⟩

lemma sndSquare_preimage_inter_support {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    ((fun z : ℝ × ℝ => z.2 ^ 2) ⁻¹' Set.Iic y) ∩ dependentPairSupport =
      Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-Real.sqrt y) (Real.sqrt y) := by
  ext z
  constructor
  · intro hz
    have hz2 : z.2 ∈ ((fun u : ℝ => u ^ 2) ⁻¹' Set.Iic y) ∩ Set.Icc (-1 : ℝ) 1 := by
      exact ⟨hz.1, hz.2.2⟩
    have hz2' : z.2 ∈ Set.Icc (-Real.sqrt y) (Real.sqrt y) := by
      simpa [square_preimage_eq_symm_Icc (x := y) hy] using hz2
    exact ⟨hz.2.1, hz2'⟩
  · intro hz
    have hz2 : z.2 ∈ ((fun u : ℝ => u ^ 2) ⁻¹' Set.Iic y) ∩ Set.Icc (-1 : ℝ) 1 := by
      simpa [square_preimage_eq_symm_Icc (x := y) hy] using hz.2
    exact ⟨hz2.1, ⟨hz.1, hz2.2⟩⟩

lemma squareJoint_preimage_inter_support {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (((fun z : ℝ × ℝ => z.1 ^ 2) ⁻¹' Set.Iic x) ∩
      ((fun z : ℝ × ℝ => z.2 ^ 2) ⁻¹' Set.Iic y)) ∩ dependentPairSupport =
        Set.Icc (-Real.sqrt x) (Real.sqrt x) ×ˢ Set.Icc (-Real.sqrt y) (Real.sqrt y) := by
  ext z
  constructor
  · intro hz
    have hz1 : z.1 ∈ ((fun u : ℝ => u ^ 2) ⁻¹' Set.Iic x) ∩ Set.Icc (-1 : ℝ) 1 := by
      exact ⟨hz.1.1, hz.2.1⟩
    have hz2 : z.2 ∈ ((fun u : ℝ => u ^ 2) ⁻¹' Set.Iic y) ∩ Set.Icc (-1 : ℝ) 1 := by
      exact ⟨hz.1.2, hz.2.2⟩
    have hz1' : z.1 ∈ Set.Icc (-Real.sqrt x) (Real.sqrt x) := by
      simpa [square_preimage_eq_symm_Icc (x := x) hx] using hz1
    have hz2' : z.2 ∈ Set.Icc (-Real.sqrt y) (Real.sqrt y) := by
      simpa [square_preimage_eq_symm_Icc (x := y) hy] using hz2
    exact ⟨hz1', hz2'⟩
  · intro hz
    have hz1 : z.1 ∈ ((fun u : ℝ => u ^ 2) ⁻¹' Set.Iic x) ∩ Set.Icc (-1 : ℝ) 1 := by
      simpa [square_preimage_eq_symm_Icc (x := x) hx] using hz.1
    have hz2 : z.2 ∈ ((fun u : ℝ => u ^ 2) ⁻¹' Set.Iic y) ∩ Set.Icc (-1 : ℝ) 1 := by
      simpa [square_preimage_eq_symm_Icc (x := y) hy] using hz.2
    exact ⟨⟨hz1.1, hz2.1⟩, ⟨hz1.2, hz2.2⟩⟩

lemma fstSquare_preimage_empty_of_lt_zero {x : ℝ} (hx : x < 0) :
    (fun z : ℝ × ℝ => z.1 ^ 2) ⁻¹' Set.Iic x = ∅ := by
  ext z
  constructor
  · intro hz
    have hzsq : z.1 ^ 2 ≤ x := by
      simpa using hz
    exfalso
    nlinarith [sq_nonneg (z.1), hzsq]
  · intro hz
    simp at hz

lemma sndSquare_preimage_empty_of_lt_zero {y : ℝ} (hy : y < 0) :
    (fun z : ℝ × ℝ => z.2 ^ 2) ⁻¹' Set.Iic y = ∅ := by
  ext z
  constructor
  · intro hz
    have hzsq : z.2 ^ 2 ≤ y := by
      simpa using hz
    exfalso
    nlinarith [sq_nonneg (z.2), hzsq]
  · intro hz
    simp at hz

lemma fstSquare_preimage_inter_support_of_one_lt {x : ℝ} (hx : 1 < x) :
    ((fun z : ℝ × ℝ => z.1 ^ 2) ⁻¹' Set.Iic x) ∩ dependentPairSupport = dependentPairSupport := by
  ext z
  constructor
  · intro hz
    exact hz.2
  · intro hz
    have hsq : z.1 ^ 2 ≤ x := by
      nlinarith [hz.1.1, hz.1.2, hx]
    exact ⟨hsq, hz⟩

lemma sndSquare_preimage_inter_support_of_one_lt {y : ℝ} (hy : 1 < y) :
    ((fun z : ℝ × ℝ => z.2 ^ 2) ⁻¹' Set.Iic y) ∩ dependentPairSupport = dependentPairSupport := by
  ext z
  constructor
  · intro hz
    exact hz.2
  · intro hz
    have hsq : z.2 ^ 2 ≤ y := by
      nlinarith [hz.2.1, hz.2.2, hy]
    exact ⟨hsq, hz⟩

lemma squareJoint_preimage_inter_support_of_right_gt_one {x y : ℝ} (hy : 1 < y) :
    (((fun z : ℝ × ℝ => z.1 ^ 2) ⁻¹' Set.Iic x) ∩
      ((fun z : ℝ × ℝ => z.2 ^ 2) ⁻¹' Set.Iic y)) ∩ dependentPairSupport =
        ((fun z : ℝ × ℝ => z.1 ^ 2) ⁻¹' Set.Iic x) ∩ dependentPairSupport := by
  ext z
  constructor
  · intro hz
    exact ⟨hz.1.1, hz.2⟩
  · intro hz
    have hysq : z.2 ^ 2 ≤ y := by
      nlinarith [hz.2.2.1, hz.2.2.2, hy]
    exact ⟨⟨hz.1, hysq⟩, hz.2⟩

lemma squareJoint_preimage_inter_support_of_left_gt_one {x y : ℝ} (hx : 1 < x) :
    (((fun z : ℝ × ℝ => z.1 ^ 2) ⁻¹' Set.Iic x) ∩
      ((fun z : ℝ × ℝ => z.2 ^ 2) ⁻¹' Set.Iic y)) ∩ dependentPairSupport =
        ((fun z : ℝ × ℝ => z.2 ^ 2) ⁻¹' Set.Iic y) ∩ dependentPairSupport := by
  ext z
  constructor
  · intro hz
    exact ⟨hz.1.2, hz.2⟩
  · intro hz
    have hxsq : z.1 ^ 2 ≤ x := by
      nlinarith [hz.2.1.1, hz.2.1.2, hx]
    exact ⟨⟨hxsq, hz.1⟩, hz.2⟩

lemma squareJoint_preimage_inter_support_of_both_gt_one {x y : ℝ}
    (hx : 1 < x) (hy : 1 < y) :
    (((fun z : ℝ × ℝ => z.1 ^ 2) ⁻¹' Set.Iic x) ∩
      ((fun z : ℝ × ℝ => z.2 ^ 2) ⁻¹' Set.Iic y)) ∩ dependentPairSupport =
        dependentPairSupport := by
  ext z
  constructor
  · intro hz
    exact hz.2
  · intro hz
    have hxsq : z.1 ^ 2 ≤ x := by
      nlinarith [hz.1.1, hz.1.2, hx]
    have hysq : z.2 ^ 2 ≤ y := by
      nlinarith [hz.2.1, hz.2.2, hy]
    exact ⟨⟨hxsq, hysq⟩, hz⟩

lemma dependentX_nonpos_inter_support :
    (dependentX ⁻¹' Set.Iic (0 : ℝ)) ∩ dependentPairSupport =
      Set.Icc (-1 : ℝ) 0 ×ˢ Set.Icc (-1 : ℝ) 1 := by
  ext z
  constructor
  · intro hz
    exact ⟨⟨hz.2.1.1, hz.1⟩, hz.2.2⟩
  · intro hz
    exact ⟨hz.1.2, ⟨⟨hz.1.1, le_trans hz.1.2 (by norm_num)⟩, hz.2⟩⟩

lemma dependentY_nonpos_inter_support :
    (dependentY ⁻¹' Set.Iic (0 : ℝ)) ∩ dependentPairSupport =
      Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 0 := by
  ext z
  constructor
  · intro hz
    exact ⟨hz.2.1, ⟨hz.2.2.1, hz.1⟩⟩
  · intro hz
    exact ⟨hz.2.2, ⟨hz.1, ⟨hz.2.1, le_trans hz.2.2 (by norm_num)⟩⟩⟩

lemma dependentXY_nonpos_inter_support :
    ((dependentX ⁻¹' Set.Iic (0 : ℝ)) ∩ (dependentY ⁻¹' Set.Iic (0 : ℝ))) ∩ dependentPairSupport =
      Set.Icc (-1 : ℝ) 0 ×ˢ Set.Icc (-1 : ℝ) 0 := by
  ext z
  constructor
  · intro hz
    exact ⟨⟨hz.2.1.1, hz.1.1⟩, ⟨hz.2.2.1, hz.1.2⟩⟩
  · intro hz
    exact ⟨⟨hz.1.2, hz.2.2⟩,
      ⟨⟨hz.1.1, le_trans hz.1.2 (by norm_num)⟩, ⟨hz.2.1, le_trans hz.2.2 (by norm_num)⟩⟩⟩

lemma dependentPairMeasure_rect_left_half :
    dependentPairMeasure (Set.Icc (-1 : ℝ) 0 ×ˢ Set.Icc (-1 : ℝ) 1) = (1 / 2 : ℝ≥0∞) := by
  have h :=
    dependentPairMeasure_rect (u := -1) (v := 0) (w := -1) (t := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  simpa [Icc_prod_Icc] using h

lemma dependentPairMeasure_rect_lower_left :
    dependentPairMeasure (Set.Icc (-1 : ℝ) 0 ×ˢ Set.Icc (-1 : ℝ) 0) = ENNReal.ofReal ((5 : ℝ) / 16) := by
  have h :=
    dependentPairMeasure_rect (u := -1) (v := 0) (w := -1) (t := 0)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  simpa [Icc_prod_Icc] using h

lemma dependentPairMeasure_symmetric_box {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    dependentPairMeasure (Set.Icc (-a) a ×ˢ Set.Icc (-b) b) = ENNReal.ofReal (a * b) := by
  convert
    (dependentPairMeasure_rect (u := -a) (v := a) (w := -b) (t := b)
      (by linarith [ha.1, ha.2]) (by linarith [ha.1]) (by linarith [ha.2])
      (by linarith [hb.1, hb.2]) (by linarith [hb.1]) (by linarith [hb.2])) using 1
  ring_nf

lemma dependentPairMeasure_square_joint_cdf_on_unit_interval {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    jointCDF dependentPairMeasure (fun z => dependentX z ^ 2) (fun z => dependentY z ^ 2) x y =
      ENNReal.ofReal (Real.sqrt x * Real.sqrt y) := by
  rw [jointCDF, dependentX, dependentY]
  have hA :
      MeasurableSet
        (((fun z : ℝ × ℝ => z.1 ^ 2) ⁻¹' Set.Iic x) ∩
          ((fun z : ℝ × ℝ => z.2 ^ 2) ⁻¹' Set.Iic y)) := by
    exact
      (measurableSet_Iic.preimage (measurable_fst.pow_const 2)).inter
        (measurableSet_Iic.preimage (measurable_snd.pow_const 2))
  rw [dependentPairMeasure_eq_inter_support hA, squareJoint_preimage_inter_support hx hy]
  simpa [Real.sqrt_mul hx.1] using
    dependentPairMeasure_symmetric_box
      ⟨Real.sqrt_nonneg x, by
        rw [Real.sqrt_le_iff]
        constructor
        · positivity
        · simpa using hx.2⟩
      ⟨Real.sqrt_nonneg y, by
        rw [Real.sqrt_le_iff]
        constructor
        · positivity
        · simpa using hy.2⟩

lemma dependentPairMeasure_square_marginal_cdfX_on_unit_interval {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    marginalCDF dependentPairMeasure (fun z => dependentX z ^ 2) x = ENNReal.ofReal (Real.sqrt x) := by
  rw [marginalCDF, dependentX]
  have hA : MeasurableSet ((fun z : ℝ × ℝ => z.1 ^ 2) ⁻¹' Set.Iic x) := by
    exact measurableSet_Iic.preimage (measurable_fst.pow_const 2)
  rw [dependentPairMeasure_eq_inter_support hA, fstSquare_preimage_inter_support hx]
  convert
    (dependentPairMeasure_rect (u := -Real.sqrt x) (v := Real.sqrt x) (w := -1) (t := 1)
      (by
        have hsqrt_le_one : Real.sqrt x ≤ 1 := by
          rw [Real.sqrt_le_iff]
          constructor
          · positivity
          · simpa using hx.2
        linarith [Real.sqrt_nonneg x, hsqrt_le_one])
      (by nlinarith [Real.sqrt_nonneg x])
      (by
        rw [Real.sqrt_le_iff]
        constructor
        · positivity
        · simpa using hx.2)
      (by norm_num) (by norm_num) (by norm_num)) using 1
  ring_nf

lemma dependentPairMeasure_square_marginal_cdfY_on_unit_interval {y : ℝ}
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    marginalCDF dependentPairMeasure (fun z => dependentY z ^ 2) y = ENNReal.ofReal (Real.sqrt y) := by
  rw [marginalCDF, dependentY]
  have hA : MeasurableSet ((fun z : ℝ × ℝ => z.2 ^ 2) ⁻¹' Set.Iic y) := by
    exact measurableSet_Iic.preimage (measurable_snd.pow_const 2)
  rw [dependentPairMeasure_eq_inter_support hA, sndSquare_preimage_inter_support hy]
  convert
    (dependentPairMeasure_rect (u := -1) (v := 1) (w := -Real.sqrt y) (t := Real.sqrt y)
      (by norm_num) (by norm_num) (by norm_num)
      (by
        have hsqrt_le_one : Real.sqrt y ≤ 1 := by
          rw [Real.sqrt_le_iff]
          constructor
          · positivity
          · simpa using hy.2
        linarith [Real.sqrt_nonneg y, hsqrt_le_one])
      (by nlinarith [Real.sqrt_nonneg y])
      (by
        rw [Real.sqrt_le_iff]
        constructor
        · positivity
        · simpa using hy.2)) using 1
  ring_nf

lemma dependentPairMeasure_square_marginal_cdfX (x : ℝ) :
    marginalCDF dependentPairMeasure (fun z => dependentX z ^ 2) x = squarePairMarginalCdf x := by
  by_cases hxlt : x < 0
  · rw [squarePairMarginalCdf, if_pos hxlt]
    rw [marginalCDF, dependentX, fstSquare_preimage_empty_of_lt_zero hxlt]
    simp
  · by_cases hxle : x ≤ 1
    · have hx : x ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_not_gt hxlt, hxle⟩
      rw [squarePairMarginalCdf, if_neg hxlt, if_pos hxle]
      exact dependentPairMeasure_square_marginal_cdfX_on_unit_interval hx
    · have hxgt : 1 < x := lt_of_not_ge hxle
      rw [squarePairMarginalCdf, if_neg hxlt, if_neg hxle]
      rw [marginalCDF, dependentX]
      have hA : MeasurableSet ((fun z : ℝ × ℝ => z.1 ^ 2) ⁻¹' Set.Iic x) := by
        exact measurableSet_Iic.preimage (measurable_fst.pow_const 2)
      rw [dependentPairMeasure_eq_inter_support hA, fstSquare_preimage_inter_support_of_one_lt hxgt,
        dependentPairMeasure_support]

lemma dependentPairMeasure_square_marginal_cdfY (y : ℝ) :
    marginalCDF dependentPairMeasure (fun z => dependentY z ^ 2) y = squarePairMarginalCdf y := by
  by_cases hylt : y < 0
  · rw [squarePairMarginalCdf, if_pos hylt]
    rw [marginalCDF, dependentY, sndSquare_preimage_empty_of_lt_zero hylt]
    simp
  · by_cases hyle : y ≤ 1
    · have hy : y ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_not_gt hylt, hyle⟩
      rw [squarePairMarginalCdf, if_neg hylt, if_pos hyle]
      exact dependentPairMeasure_square_marginal_cdfY_on_unit_interval hy
    · have hygt : 1 < y := lt_of_not_ge hyle
      rw [squarePairMarginalCdf, if_neg hylt, if_neg hyle]
      rw [marginalCDF, dependentY]
      have hA : MeasurableSet ((fun z : ℝ × ℝ => z.2 ^ 2) ⁻¹' Set.Iic y) := by
        exact measurableSet_Iic.preimage (measurable_snd.pow_const 2)
      rw [dependentPairMeasure_eq_inter_support hA, sndSquare_preimage_inter_support_of_one_lt hygt,
        dependentPairMeasure_support]

lemma dependentPair_not_indep :
    ¬ ProbabilityTheory.IndepFun dependentX dependentY dependentPairMeasure := by
  intro hIndep
  have hCDF := (thm_5_4 dependentPairMeasure dependentX dependentY dependentX_measurable
    dependentY_measurable).1 hIndep
  have hjoint : jointCDF dependentPairMeasure dependentX dependentY 0 0 =
      ENNReal.ofReal ((5 : ℝ) / 16) := by
    rw [jointCDF, dependentX, dependentY]
    have hA : MeasurableSet ((Prod.fst ⁻¹' Set.Iic (0 : ℝ)) ∩ (Prod.snd ⁻¹' Set.Iic (0 : ℝ))) := by
      exact (measurable_fst measurableSet_Iic).inter (measurable_snd measurableSet_Iic)
    rw [dependentPairMeasure_eq_inter_support hA]
    have hEq :
        ((Prod.fst ⁻¹' Set.Iic (0 : ℝ)) ∩ (Prod.snd ⁻¹' Set.Iic (0 : ℝ))) ∩ dependentPairSupport =
          Set.Icc (-1 : ℝ) 0 ×ˢ Set.Icc (-1 : ℝ) 0 := by
      simpa [dependentX, dependentY] using dependentXY_nonpos_inter_support
    rw [hEq]
    exact dependentPairMeasure_rect_lower_left
  have hmx : marginalCDF dependentPairMeasure dependentX 0 = (1 / 2 : ℝ≥0∞) := by
    rw [marginalCDF, dependentX]
    change dependentPairMeasure (((fun z : ℝ × ℝ => z.1) ⁻¹' Set.Iic (0 : ℝ))) = (1 / 2 : ℝ≥0∞)
    have hA : MeasurableSet (((fun z : ℝ × ℝ => z.1) ⁻¹' Set.Iic (0 : ℝ))) := by
      exact measurableSet_Iic.preimage measurable_fst
    rw [dependentPairMeasure_eq_inter_support hA]
    have hEq :
        (((fun z : ℝ × ℝ => z.1) ⁻¹' Set.Iic (0 : ℝ))) ∩ dependentPairSupport =
          Set.Icc (-1 : ℝ) 0 ×ˢ Set.Icc (-1 : ℝ) 1 := by
      simpa [dependentX] using dependentX_nonpos_inter_support
    rw [hEq]
    exact dependentPairMeasure_rect_left_half
  have hmy : marginalCDF dependentPairMeasure dependentY 0 = (1 / 2 : ℝ≥0∞) := by
    rw [marginalCDF, dependentY]
    change dependentPairMeasure (((fun z : ℝ × ℝ => z.2) ⁻¹' Set.Iic (0 : ℝ))) = (1 / 2 : ℝ≥0∞)
    have hA : MeasurableSet (((fun z : ℝ × ℝ => z.2) ⁻¹' Set.Iic (0 : ℝ))) := by
      exact measurableSet_Iic.preimage measurable_snd
    rw [dependentPairMeasure_eq_inter_support hA]
    have hEq :
        (((fun z : ℝ × ℝ => z.2) ⁻¹' Set.Iic (0 : ℝ))) ∩ dependentPairSupport =
          Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 0 := by
      simpa [dependentY] using dependentY_nonpos_inter_support
    rw [hEq]
    have h :=
      dependentPairMeasure_rect (u := -1) (v := 1) (w := -1) (t := 0)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at h
    simpa [Icc_prod_Icc] using h
  have h00 := hCDF 0 0
  rw [hjoint, hmx, hmy] at h00
  have h00Real := congrArg (fun r : ℝ≥0∞ => r.toReal) h00
  norm_num at h00Real

lemma dependentPairMeasure_square_joint_cdf (x y : ℝ) :
    jointCDF dependentPairMeasure (fun z => dependentX z ^ 2) (fun z => dependentY z ^ 2) x y =
      squarePairMarginalCdf x * squarePairMarginalCdf y := by
  by_cases hxlt : x < 0
  · rw [squarePairMarginalCdf, if_pos hxlt, zero_mul]
    rw [jointCDF, dependentX, dependentY, fstSquare_preimage_empty_of_lt_zero hxlt]
    simp
  · by_cases hylt : y < 0
    · have hyzero : squarePairMarginalCdf y = 0 := by
        simp [squarePairMarginalCdf, hylt]
      rw [hyzero, mul_zero]
      rw [jointCDF, dependentX, dependentY, sndSquare_preimage_empty_of_lt_zero hylt]
      simp
    · by_cases hxle : x ≤ 1
      · by_cases hyle : y ≤ 1
        · have hx : x ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_not_gt hxlt, hxle⟩
          have hy : y ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_not_gt hylt, hyle⟩
          rw [dependentPairMeasure_square_joint_cdf_on_unit_interval hx hy,
            squarePairMarginalCdf_on_unit_interval hx,
            squarePairMarginalCdf_on_unit_interval hy]
          rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg x)]
        · have hygt : 1 < y := lt_of_not_ge hyle
          have hyone : squarePairMarginalCdf y = 1 := by
            simp [squarePairMarginalCdf, hylt, hyle]
          rw [hyone, mul_one]
          rw [jointCDF, dependentX, dependentY]
          have hA :
              MeasurableSet
                (((fun z : ℝ × ℝ => z.1 ^ 2) ⁻¹' Set.Iic x) ∩
                  ((fun z : ℝ × ℝ => z.2 ^ 2) ⁻¹' Set.Iic y)) := by
            exact
              (measurableSet_Iic.preimage (measurable_fst.pow_const 2)).inter
                (measurableSet_Iic.preimage (measurable_snd.pow_const 2))
          rw [dependentPairMeasure_eq_inter_support hA,
            squareJoint_preimage_inter_support_of_right_gt_one hygt]
          have hmx := dependentPairMeasure_square_marginal_cdfX x
          rw [marginalCDF, dependentX] at hmx
          have hB : MeasurableSet ((fun z : ℝ × ℝ => z.1 ^ 2) ⁻¹' Set.Iic x) := by
            exact measurableSet_Iic.preimage (measurable_fst.pow_const 2)
          rw [dependentPairMeasure_eq_inter_support hB] at hmx
          exact hmx
      · have hxgt : 1 < x := lt_of_not_ge hxle
        by_cases hyle : y ≤ 1
        · have hxone : squarePairMarginalCdf x = 1 := by
            simp [squarePairMarginalCdf, hxlt, hxle]
          rw [hxone, one_mul]
          rw [jointCDF, dependentX, dependentY]
          have hA :
              MeasurableSet
                (((fun z : ℝ × ℝ => z.1 ^ 2) ⁻¹' Set.Iic x) ∩
                  ((fun z : ℝ × ℝ => z.2 ^ 2) ⁻¹' Set.Iic y)) := by
            exact
              (measurableSet_Iic.preimage (measurable_fst.pow_const 2)).inter
                (measurableSet_Iic.preimage (measurable_snd.pow_const 2))
          rw [dependentPairMeasure_eq_inter_support hA,
            squareJoint_preimage_inter_support_of_left_gt_one hxgt]
          have hmy := dependentPairMeasure_square_marginal_cdfY y
          rw [marginalCDF, dependentY] at hmy
          have hB : MeasurableSet ((fun z : ℝ × ℝ => z.2 ^ 2) ⁻¹' Set.Iic y) := by
            exact measurableSet_Iic.preimage (measurable_snd.pow_const 2)
          rw [dependentPairMeasure_eq_inter_support hB] at hmy
          exact hmy
        · have hygt : 1 < y := lt_of_not_ge hyle
          have hxone : squarePairMarginalCdf x = 1 := by
            simp [squarePairMarginalCdf, hxlt, hxle]
          have hyone : squarePairMarginalCdf y = 1 := by
            simp [squarePairMarginalCdf, hylt, hyle]
          rw [hxone, hyone]
          rw [jointCDF, dependentX, dependentY]
          have hA :
              MeasurableSet
                (((fun z : ℝ × ℝ => z.1 ^ 2) ⁻¹' Set.Iic x) ∩
                  ((fun z : ℝ × ℝ => z.2 ^ 2) ⁻¹' Set.Iic y)) := by
            exact
              (measurableSet_Iic.preimage (measurable_fst.pow_const 2)).inter
                (measurableSet_Iic.preimage (measurable_snd.pow_const 2))
          rw [dependentPairMeasure_eq_inter_support hA,
            squareJoint_preimage_inter_support_of_both_gt_one hxgt hygt,
            dependentPairMeasure_support]
          simp [hxone, hyone]

lemma dependentPairSquares_indep :
    ProbabilityTheory.IndepFun (fun z => dependentX z ^ 2) (fun z => dependentY z ^ 2)
      dependentPairMeasure := by
  apply (thm_5_4 dependentPairMeasure (fun z => dependentX z ^ 2) (fun z => dependentY z ^ 2)
    (dependentX_measurable.pow_const 2) (dependentY_measurable.pow_const 2)).2
  intro x y
  rw [dependentPairMeasure_square_joint_cdf x y,
    dependentPairMeasure_square_marginal_cdfX x,
    dependentPairMeasure_square_marginal_cdfY y]

theorem ex_5_2_2 :
    dependentPairPdf 1 1 ≠ dependentPairMarginalPdf 1 * dependentPairMarginalPdf 1 ∧
      (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → dependentPairMarginalPdf x = (1 : ℝ) / 2) ∧
      (∀ x y : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
        jointCDF dependentPairMeasure (fun z => dependentX z ^ 2) (fun z => dependentY z ^ 2) x y =
          ENNReal.ofReal (Real.sqrt x * Real.sqrt y) ∧
        jointCDF dependentPairMeasure (fun z => dependentX z ^ 2) (fun z => dependentY z ^ 2) x y =
          marginalCDF dependentPairMeasure (fun z => dependentX z ^ 2) x *
            marginalCDF dependentPairMeasure (fun z => dependentY z ^ 2) y) ∧
      ¬ ProbabilityTheory.IndepFun dependentX dependentY dependentPairMeasure ∧
      ProbabilityTheory.IndepFun (fun z => dependentX z ^ 2) (fun z => dependentY z ^ 2)
        dependentPairMeasure := by
  refine ⟨dependentPairPdf_not_factorized_at_one, ?_, ?_, dependentPair_not_indep,
    dependentPairSquares_indep⟩
  · intro x hx
    exact dependentPairMarginalPdf_on_support hx
  · intro x y hx hy
    refine ⟨dependentPairMeasure_square_joint_cdf_on_unit_interval hx hy, ?_⟩
    rw [dependentPairMeasure_square_joint_cdf x y,
      dependentPairMeasure_square_marginal_cdfX x,
      dependentPairMeasure_square_marginal_cdfY y]
