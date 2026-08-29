/-
TASK ID: thm_7_11
TYPE: Theorem_with_Proof
SOURCE PLAN: 28_chap7_pushforward_change_of_variable
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set
open scoped ENNReal

theorem thm_7_11_indicator_preimage_lintegral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → ℝ} (hX : Measurable X) {B : Set ℝ} (hB : MeasurableSet B) :
    (∫⁻ ω, (X ⁻¹' B).indicator (1 : Ω → ℝ≥0∞) ω ∂μ) =
      ∫⁻ x, B.indicator (1 : ℝ → ℝ≥0∞) x ∂Measure.map X μ := by
  rw [lintegral_indicator_one (hB.preimage hX)]
  rw [lintegral_indicator_one hB]
  exact (Measure.map_apply hX hB).symm

theorem thm_7_11_simple_lintegral_map
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → ℝ} (hX : Measurable X) (g : SimpleFunc ℝ ℝ≥0∞) :
    g.lintegral (Measure.map X μ) = (g.comp X hX).lintegral μ := by
  exact SimpleFunc.lintegral_map g hX

theorem thm_7_11_lintegral_map_source_spine
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → ℝ} (hX : Measurable X)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂Measure.map X μ) = ∫⁻ ω, f (X ω) ∂μ := by
  rw [lintegral_eq_iSup_eapprox_lintegral hf]
  simp only [← Function.comp_apply (f := f) (g := X)]
  rw [lintegral_eq_iSup_eapprox_lintegral (hf.comp hX)]
  congr with n : 1
  convert! thm_7_11_simple_lintegral_map μ hX _
  ext1 x
  simp only [SimpleFunc.eapprox_comp hf hX, SimpleFunc.coe_comp]

theorem thm_7_11_nonnegative_extended
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → ℝ} {h : ℝ → ℝ}
    (hX : Measurable X) (hh : Measurable h) (_hnonneg : ∀ x, 0 ≤ h x) :
    (∫⁻ ω, ENNReal.ofReal (h (X ω)) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (h x) ∂Measure.map X μ := by
  exact
    (thm_7_11_lintegral_map_source_spine μ hX
      (ENNReal.measurable_ofReal.comp hh)).symm

theorem thm_7_11_integrable_iff_source_spine
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → ℝ} {h : ℝ → ℝ}
    (hX : Measurable X) (hh : Measurable h) :
    Integrable (fun ω => h (X ω)) μ ↔
      Integrable h (Measure.map X μ) := by
  have hnorm : Measurable (fun x : ℝ => ‖h x‖ₑ) := hh.enorm
  have hnorm_eq :
      (∫⁻ x, ‖h x‖ₑ ∂Measure.map X μ) = ∫⁻ ω, ‖h (X ω)‖ₑ ∂μ :=
    thm_7_11_lintegral_map_source_spine μ hX hnorm
  constructor
  · intro hcomp
    refine ⟨hh.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, hnorm_eq]
    exact hasFiniteIntegral_iff_enorm.mp hcomp.hasFiniteIntegral
  · intro hmap
    refine ⟨(hh.comp hX).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, ← hnorm_eq]
    exact hasFiniteIntegral_iff_enorm.mp hmap.hasFiniteIntegral

theorem thm_7_11_signed_integral_eq_source_spine
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → ℝ} {h : ℝ → ℝ}
    (hX : Measurable X) (hh : Measurable h)
    (hcomp : Integrable (fun ω => h (X ω)) μ) :
    (∫ ω, h (X ω) ∂μ) = ∫ x, h x ∂Measure.map X μ := by
  have hmap : Integrable h (Measure.map X μ) :=
    (thm_7_11_integrable_iff_source_spine μ hX hh).mp hcomp
  have hpos :
      (∫⁻ x, ENNReal.ofReal (h x) ∂Measure.map X μ) =
        ∫⁻ ω, ENNReal.ofReal (h (X ω)) ∂μ :=
    thm_7_11_lintegral_map_source_spine μ hX
      (ENNReal.measurable_ofReal.comp hh)
  have hneg :
      (∫⁻ x, ENNReal.ofReal (-h x) ∂Measure.map X μ) =
        ∫⁻ ω, ENNReal.ofReal (-h (X ω)) ∂μ :=
    thm_7_11_lintegral_map_source_spine μ hX
      (ENNReal.measurable_ofReal.comp hh.neg)
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hcomp]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hmap]
  rw [hpos, hneg]

theorem thm_7_11 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → ℝ} {h : ℝ → ℝ} (hX : Measurable X) (hh : Measurable h) :
    (Integrable (fun ω => h (X ω)) μ ↔ Integrable h (Measure.map X μ)) ∧
      (∫ ω, h (X ω) ∂μ = ∫ x, h x ∂Measure.map X μ) := by
  have hiff := thm_7_11_integrable_iff_source_spine μ hX hh
  refine ⟨hiff, ?_⟩
  by_cases hcomp : Integrable (fun ω => h (X ω)) μ
  · exact thm_7_11_signed_integral_eq_source_spine μ hX hh hcomp
  · have hmap : ¬ Integrable h (Measure.map X μ) := by
      intro h
      exact hcomp (hiff.mpr h)
    rw [integral_undef hcomp, integral_undef hmap]
