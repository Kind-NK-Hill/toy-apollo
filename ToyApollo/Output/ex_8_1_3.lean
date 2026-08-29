/-
TASK ID: ex_8_1_3
TYPE: Example_Proof
SOURCE PLAN: 31_chap8_coupling
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_8_1
import ToyApollo.Output.def_8_2

open MeasureTheory ProbabilityTheory Set

noncomputable section

abbrev OpenUnitInterval := Ioo (0 : ℝ) 1

namespace OpenUnitInterval

noncomputable instance instMeasureSpace : MeasureSpace OpenUnitInterval :=
  Measure.Subtype.measureSpace

noncomputable instance instIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure OpenUnitInterval) := by
  refine ⟨?_⟩
  rw [Measure.Subtype.volume_univ measurableSet_Ioo.nullMeasurableSet, Real.volume_Ioo]
  norm_num

lemma measurableEmbedding_coe :
    MeasurableEmbedding ((↑) : OpenUnitInterval → ℝ) where
  injective := Subtype.val_injective
  measurable := measurable_subtype_coe
  measurableSet_image' _ := measurableSet_Ioo.subtype_image

lemma volume_apply {s : Set OpenUnitInterval} :
    (volume : Measure OpenUnitInterval) s = volume (Subtype.val '' s) := by
  rw [Measure.Subtype.volume_def]
  exact measurableEmbedding_coe.comap_apply volume s

@[simp] lemma volume_Iic (u : OpenUnitInterval) :
    (volume : Measure OpenUnitInterval) (Iic u) = ENNReal.ofReal (u : ℝ) := by
  simp only [volume_apply, image_subtype_val_Ioo_Iic, Real.volume_Ioc, sub_zero]

end OpenUnitInterval

lemma cdf_pos_of_strictMono
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (hstrict : StrictMono (cdf P)) (x : ℝ) : 0 < cdf P x := by
  have hlt : x - 1 < x := by linarith
  exact lt_of_le_of_lt (cdf_nonneg P (x - 1)) (hstrict hlt)

lemma cdf_lt_one_of_strictMono
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (hstrict : StrictMono (cdf P)) (x : ℝ) : cdf P x < 1 := by
  have hlt : x < x + 1 := by linarith
  exact lt_of_lt_of_le (hstrict hlt) (cdf_le_one P (x + 1))

noncomputable def cdfOpen
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (hstrict : StrictMono (cdf P)) (x : ℝ) : OpenUnitInterval :=
  ⟨cdf P x, cdf_pos_of_strictMono P hstrict x, cdf_lt_one_of_strictMono P hstrict x⟩

structure InvertibleCDFData (P : Measure ℝ) [IsProbabilityMeasure P] where
  strictMono_cdf : StrictMono (cdf P)
  quantile : OpenUnitInterval → ℝ
  measurable_quantile : Measurable quantile
  left_inv : ∀ x : ℝ, quantile (cdfOpen P strictMono_cdf x) = x
  right_inv : ∀ u : OpenUnitInterval, cdfOpen P strictMono_cdf (quantile u) = u

lemma measurable_cdfOpen
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (hstrict : StrictMono (cdf P)) : Measurable (cdfOpen P hstrict) := by
  exact (monotone_cdf P).measurable.subtype_mk

theorem map_quantile_openUnit_eq
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (d : InvertibleCDFData P) :
    Measure.map d.quantile (volume : Measure OpenUnitInterval) = P := by
  letI : IsProbabilityMeasure
      (Measure.map d.quantile (volume : Measure OpenUnitInterval)) :=
    Measure.isProbabilityMeasure_map d.measurable_quantile.aemeasurable
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply d.measurable_quantile measurableSet_Iic]
  have hpre :
      d.quantile ⁻¹' Iic x = Iic (cdfOpen P d.strictMono_cdf x) := by
    ext u
    simp only [mem_preimage, mem_Iic]
    have hright : cdf P (d.quantile u) = (u : ℝ) := by
      simpa [cdfOpen] using congrArg Subtype.val (d.right_inv u)
    rw [← d.strictMono_cdf.le_iff_le, hright]
    rfl
  rw [hpre, OpenUnitInterval.volume_Iic]
  exact ofReal_cdf P x

noncomputable def inverseCDFCoupling
    (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (dP : InvertibleCDFData P) (dQ : InvertibleCDFData Q) : Coupling P Q :=
  { Ω := OpenUnitInterval
    instMeasurableSpaceΩ := inferInstance
    μ := volume
    instIsProbabilityMeasureμ := inferInstance
    X := dP.quantile
    Y := dQ.quantile
    measurable_X := dP.measurable_quantile
    measurable_Y := dQ.measurable_quantile
    map_X := map_quantile_openUnit_eq P dP
    map_Y := map_quantile_openUnit_eq Q dQ }

noncomputable def inverseCDFTransport
    (P : Measure ℝ) [IsProbabilityMeasure P]
    {Q : Measure ℝ} [IsProbabilityMeasure Q]
    (dP : InvertibleCDFData P) (dQ : InvertibleCDFData Q) : ℝ → ℝ :=
  dQ.quantile ∘ cdfOpen P dP.strictMono_cdf

lemma measurable_inverseCDFTransport
    (P : Measure ℝ) [IsProbabilityMeasure P]
    {Q : Measure ℝ} [IsProbabilityMeasure Q]
    (dP : InvertibleCDFData P) (dQ : InvertibleCDFData Q) :
    Measurable (inverseCDFTransport P dP dQ) :=
  dQ.measurable_quantile.comp (measurable_cdfOpen P dP.strictMono_cdf)

noncomputable def inverseCDFDeterministicCoupling
    (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (dP : InvertibleCDFData P) (dQ : InvertibleCDFData Q) :
    DeterministicCoupling P Q where
  toCoupling := inverseCDFCoupling P Q dP dQ
  T := inverseCDFTransport P dP dQ
  measurable_T := measurable_inverseCDFTransport P dP dQ
  Y_eq_transport := by
    funext u
    change dQ.quantile u =
      dQ.quantile (cdfOpen P dP.strictMono_cdf (dP.quantile u))
    rw [dP.right_inv u]

structure CouplingMorphism
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {P : Measure α} {Q : Measure β} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (π : Coupling P Q) (π' : Coupling P Q) where
  toFun : π.Ω → π'.Ω
  measurable_toFun : Measurable toFun
  comm_X : π.X = π'.X ∘ toFun
  comm_Y : π.Y = π'.Y ∘ toFun
  map_μ : Measure.map toFun π.μ = π'.μ

structure EquivalentCouplings
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {P : Measure α} {Q : Measure β} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (π : Coupling P Q) (π' : Coupling P Q) where
  forward : CouplingMorphism π π'
  backward : CouplingMorphism π' π
  left_inv_ae : ∀ᵐ ω ∂π.μ, backward.toFun (forward.toFun ω) = ω
  right_inv_ae : ∀ᵐ ω' ∂π'.μ, forward.toFun (backward.toFun ω') = ω'

theorem measurable_product_projections
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    Measurable (@Prod.fst α β) ∧ Measurable (@Prod.snd α β) :=
  ⟨measurable_fst, measurable_snd⟩

theorem fst_preimage_eq_rectangle
    {α β : Type*} (s : Set α) :
    (@Prod.fst α β) ⁻¹' s = s ×ˢ (Set.univ : Set β) := by
  ext z
  simp

theorem snd_preimage_eq_rectangle
    {α β : Type*} (t : Set β) :
    (@Prod.snd α β) ⁻¹' t = (Set.univ : Set α) ×ˢ t := by
  ext z
  simp

theorem measurableSet_rectangle
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    MeasurableSet (s ×ˢ t) :=
  hs.prod ht

theorem ex_8_1_3
    (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (dP : InvertibleCDFData P) (dQ : InvertibleCDFData Q) :
    ∃ δ : DeterministicCoupling P Q,
      δ.toCoupling = inverseCDFCoupling P Q dP dQ ∧
      δ.T = dQ.quantile ∘ cdfOpen P dP.strictMono_cdf := by
  exact ⟨inverseCDFDeterministicCoupling P Q dP dQ, rfl, rfl⟩
