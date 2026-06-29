/-
TASK ID: thm_7_2
TYPE: Theorem_with_Proof
SOURCE PLAN: 25_chap7_ae_equality
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

theorem thm_7_2 {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜] {μ : Measure Ω}
    {X : Ω → 𝕜} (hX : Measurable X) :
    (∫⁻ ω, ENNReal.ofReal ‖X ω‖ ∂μ = 0) ↔ X =ᵐ[μ] 0 := by
  let nX : Ω → ENNReal := fun ω => ENNReal.ofReal ‖X ω‖
  have hnX : AEMeasurable nX μ := ((hX.norm).ennreal_ofReal).aemeasurable
  constructor
  · intro h_zero
    have hnX_zero : nX =ᵐ[μ] 0 := (MeasureTheory.lintegral_eq_zero_iff' hnX).1 h_zero
    filter_upwards [hnX_zero] with ω hω
    have hnorm : ‖X ω‖ = 0 := by
      simpa [nX] using hω
    exact norm_eq_zero.mp hnorm
  · intro hX_zero
    have hnX_zero : nX =ᵐ[μ] 0 := by
      filter_upwards [hX_zero] with ω hω
      simp [nX, hω]
    exact (MeasureTheory.lintegral_eq_zero_iff' hnX).2 hnX_zero
