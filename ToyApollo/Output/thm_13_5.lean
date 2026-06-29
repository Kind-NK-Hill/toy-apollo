/-
TASK ID: thm_13_5
TYPE: Theorem_Statement
SOURCE PLAN: chapter13-properties
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped ENNReal

noncomputable section

theorem thm_13_5_density_measurable {Ω : Type*} [MeasurableSpace Ω]
    (ν μ : Measure Ω) : Measurable (ν.rnDeriv μ) :=
  Measure.measurable_rnDeriv ν μ

theorem thm_13_5_density_ne_top {Ω : Type*} [MeasurableSpace Ω]
    (ν μ : Measure Ω) [SigmaFinite ν] : ∀ᵐ ω ∂μ, ν.rnDeriv μ ω ≠ ∞ :=
  Measure.rnDeriv_ne_top ν μ

theorem thm_13_5_withDensity {Ω : Type*} [MeasurableSpace Ω]
    (ν μ : Measure Ω) [SigmaFinite ν] [SigmaFinite μ] (hνμ : ν ≪ μ) :
    μ.withDensity (ν.rnDeriv μ) = ν :=
  Measure.withDensity_rnDeriv_eq ν μ hνμ

theorem thm_13_5_set_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (ν μ : Measure Ω) [SigmaFinite ν] [SigmaFinite μ] (hνμ : ν ≪ μ)
    {B : Set Ω} (hB : MeasurableSet B) :
    ν B = ∫⁻ ω in B, ν.rnDeriv μ ω ∂μ := by
  calc
    ν B = (μ.withDensity (ν.rnDeriv μ)) B := by
      rw [thm_13_5_withDensity ν μ hνμ]
    _ = ∫⁻ ω in B, ν.rnDeriv μ ω ∂μ := withDensity_apply (ν.rnDeriv μ) hB

theorem thm_13_5 {Ω : Type*} [MeasurableSpace Ω]
    (ν μ : Measure Ω) [SigmaFinite ν] [SigmaFinite μ] (hνμ : ν ≪ μ) :
    ∃ f : Ω → ℝ≥0∞,
      Measurable f ∧
        (∀ᵐ ω ∂μ, f ω ≠ ∞) ∧
          (∀ ⦃B : Set Ω⦄, MeasurableSet B → ν B = ∫⁻ ω in B, f ω ∂μ) ∧
            ∀ g : Ω → ℝ≥0∞,
              Measurable g →
                (∀ ⦃B : Set Ω⦄, MeasurableSet B → ν B = ∫⁻ ω in B, g ω ∂μ) →
                  g =ᵐ[μ] f := by
  refine ⟨ν.rnDeriv μ, thm_13_5_density_measurable ν μ,
    thm_13_5_density_ne_top ν μ, ?_, ?_⟩
  · intro B hB
    exact thm_13_5_set_lintegral ν μ hνμ hB
  · intro g hg hg_integrals
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hg
      (thm_13_5_density_measurable ν μ) ?_
    intro B hB _hB_finite
    rw [← hg_integrals hB, ← thm_13_5_set_lintegral ν μ hνμ hB]
