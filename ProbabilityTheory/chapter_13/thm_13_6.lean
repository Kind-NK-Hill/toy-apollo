/-
TASK ID: thm_13_6
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-properties
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_13.def_13_3
import ProbabilityTheory.chapter_13.thm_13_5




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

noncomputable section



theorem thm_13_6_rn_deriv_ae_eq_condExp {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω}
    {h𝓖 : IsSubSigmaField 𝓖 𝓕} [SigmaFinite (P.trim h𝓖)]
    {X : Ω → ℝ} (hX : @AmbientIntegrable Ω 𝓕 P X) :
    SignedMeasure.rnDeriv ((P.withDensityᵥ X).trim h𝓖) (P.trim h𝓖)
      =ᵐ[P] P[X | 𝓖] :=
  rnDeriv_ae_eq_condExp (hm := h𝓖) hX



theorem thm_13_6_condExp_measurable {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω}
    {X : Ω → ℝ} :
    GMeasurable 𝓖 (P[X | 𝓖]) :=
  stronglyMeasurable_condExp.measurable

 
theorem thm_13_6_condExp_integrable {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω} {X : Ω → ℝ} :
    @AmbientIntegrable Ω 𝓕 P (P[X | 𝓖]) :=
  integrable_condExp



theorem thm_13_6_condExp_set_integral {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω}
    {h𝓖 : IsSubSigmaField 𝓖 𝓕} [SigmaFinite (P.trim h𝓖)]
    {X : Ω → ℝ} (hX : @AmbientIntegrable Ω 𝓕 P X)
    {B : Set Ω} (hB : IsMeasurableIn 𝓖 B) :
    ∫ ω in B, P[X | 𝓖] ω ∂P = ∫ ω in B, X ω ∂P :=
  setIntegral_condExp h𝓖 hX hB



theorem thm_13_6 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω}
    (h𝓖 : IsSubSigmaField 𝓖 𝓕) [SigmaFinite (P.trim h𝓖)]
    {X : Ω → ℝ} (hX : @AmbientIntegrable Ω 𝓕 P X) :
    ∃ Y : Ω → ℝ, @def_13_3 Ω 𝓕 P 𝓖 h𝓖 X Y := by
  refine ⟨P[X | 𝓖], ?_⟩
  refine ⟨hX, @thm_13_6_condExp_integrable Ω 𝓕 P 𝓖 X,
    @thm_13_6_condExp_measurable Ω 𝓕 P 𝓖 X, ?_⟩
  intro B hB
  exact @thm_13_6_condExp_set_integral Ω 𝓕 P 𝓖 h𝓖 _ X hX B hB
