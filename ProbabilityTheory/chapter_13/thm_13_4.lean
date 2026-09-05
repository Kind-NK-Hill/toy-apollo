/-
TASK ID: thm_13_4
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-sub-sigma-algebra
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_13.def_13_3




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

noncomputable section



theorem thm_13_4_set_integral_uniqueness {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {𝓖 : SigmaField Ω}
    (h𝓖 : IsSubSigmaField 𝓖 𝓕) {Z1 Z2 : Ω → ℝ}
    (hZ1int : @AmbientIntegrable Ω 𝓕 P Z1)
    (hZ2int : @AmbientIntegrable Ω 𝓕 P Z2)
    (hZ1meas : GMeasurable 𝓖 Z1)
    (hZ2meas : GMeasurable 𝓖 Z2)
    (hset : ∀ ⦃B : Set Ω⦄, IsMeasurableIn 𝓖 B →
      ∫ ω in B, Z1 ω ∂P = ∫ ω in B, Z2 ω ∂P) :
    Z1 =ᵐ[P] Z2 := by
  exact ae_eq_of_forall_setIntegral_eq_of_sigmaFinite'
    (μ := P) (m := 𝓖) (m0 := 𝓕) (F' := ℝ) h𝓖
    (fun B _ _ => hZ1int.integrableOn)
    (fun B _ _ => hZ2int.integrableOn)
    (fun B hB _ => hset hB)
    hZ1meas.aestronglyMeasurable hZ2meas.aestronglyMeasurable



theorem thm_13_4 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {𝓖 : SigmaField Ω}
    {h𝓖 : IsSubSigmaField 𝓖 𝓕} {X Z1 Z2 : Ω → ℝ}
    (h1 : @def_13_3 Ω 𝓕 P 𝓖 h𝓖 X Z1)
    (h2 : @def_13_3 Ω 𝓕 P 𝓖 h𝓖 X Z2) :
    Z1 =ᵐ[P] Z2 := by
  refine @thm_13_4_set_integral_uniqueness Ω 𝓕 P _ 𝓖 h𝓖 Z1 Z2
    (@def_13_3_integrable_version Ω 𝓕 P 𝓖 h𝓖 X Z1 h1)
    (@def_13_3_integrable_version Ω 𝓕 P 𝓖 h𝓖 X Z2 h2)
    (@def_13_3_measurable Ω 𝓕 P 𝓖 h𝓖 X Z1 h1)
    (@def_13_3_measurable Ω 𝓕 P 𝓖 h𝓖 X Z2 h2) ?_
  intro B hB
  have hZ1X :
      ∫ ω in B, Z1 ω ∂P = ∫ ω in B, X ω ∂P :=
    @def_13_3_set_integral_eq Ω 𝓕 P 𝓖 h𝓖 X Z1 h1 B hB
  have hZ2X :
      ∫ ω in B, Z2 ω ∂P = ∫ ω in B, X ω ∂P :=
    @def_13_3_set_integral_eq Ω 𝓕 P 𝓖 h𝓖 X Z2 h2 B hB
  exact hZ1X.trans hZ2X.symm
