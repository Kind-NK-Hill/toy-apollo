/-
TASK ID: thm_13_8
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-properties
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_13.def_13_3
import ProbabilityTheory.chapter_13.thm_13_4
import ProbabilityTheory.chapter_13.thm_13_6




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

noncomputable section



theorem thm_13_8_left_set_integral {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓗 : SigmaField Ω}
    (h𝓗 : IsSubSigmaField 𝓗 𝓕)
    [SigmaFinite (P.trim h𝓗)]
    {X : Ω → ℝ} (hX : @AmbientIntegrable Ω 𝓕 P X)
    {B : Set Ω} (hB : IsMeasurableIn 𝓗 B) :
    ∫ ω in B, P[X | 𝓗] ω ∂P = ∫ ω in B, X ω ∂P :=
  @thm_13_6_condExp_set_integral Ω 𝓕 P 𝓗 h𝓗 _ X hX B hB



theorem thm_13_8_right_set_integral {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 𝓗 : SigmaField Ω}
    (h𝓖 : IsSubSigmaField 𝓖 𝓕) (h𝓗 : IsSubSigmaField 𝓗 𝓕)
    (h𝓗𝓖 : IsSubSigmaField 𝓗 𝓖)
    [SigmaFinite (P.trim h𝓖)] [SigmaFinite (P.trim h𝓗)]
    {X : Ω → ℝ} (hX : @AmbientIntegrable Ω 𝓕 P X)
    {B : Set Ω} (hB : IsMeasurableIn 𝓗 B) :
    ∫ ω in B, P[P[X | 𝓖] | 𝓗] ω ∂P = ∫ ω in B, X ω ∂P := by
  calc
    ∫ ω in B, P[P[X | 𝓖] | 𝓗] ω ∂P
        = ∫ ω in B, P[X | 𝓖] ω ∂P :=
      @thm_13_6_condExp_set_integral Ω 𝓕 P 𝓗 h𝓗 _
        (P[X | 𝓖]) (@thm_13_6_condExp_integrable Ω 𝓕 P 𝓖 X) B hB
    _ = ∫ ω in B, X ω ∂P :=
      @thm_13_6_condExp_set_integral Ω 𝓕 P 𝓖 h𝓖 _ X hX B (h𝓗𝓖 hB)



theorem thm_13_8_iterated_condExp_is_version {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 𝓗 : SigmaField Ω}
    (h𝓖 : IsSubSigmaField 𝓖 𝓕) (h𝓗 : IsSubSigmaField 𝓗 𝓕)
    (h𝓗𝓖 : IsSubSigmaField 𝓗 𝓖)
    [SigmaFinite (P.trim h𝓖)] [SigmaFinite (P.trim h𝓗)]
    {X : Ω → ℝ} (hX : @AmbientIntegrable Ω 𝓕 P X) :
    @def_13_3 Ω 𝓕 P 𝓗 h𝓗 X (P[P[X | 𝓖] | 𝓗]) := by
  refine ⟨hX, @thm_13_6_condExp_integrable Ω 𝓕 P 𝓗 (P[X | 𝓖]),
    @thm_13_6_condExp_measurable Ω 𝓕 P 𝓗 (P[X | 𝓖]), ?_⟩
  intro B hB
  exact @thm_13_8_right_set_integral Ω 𝓕 P 𝓖 𝓗 h𝓖 h𝓗 h𝓗𝓖 _ _ X hX B hB



theorem thm_13_8_via_versions {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {𝓖 𝓗 : SigmaField Ω}
    (h𝓖 : IsSubSigmaField 𝓖 𝓕) (h𝓗 : IsSubSigmaField 𝓗 𝓕)
    (h𝓗𝓖 : IsSubSigmaField 𝓗 𝓖)
    [SigmaFinite (P.trim h𝓖)] [SigmaFinite (P.trim h𝓗)]
    {X : Ω → ℝ} (hX : @AmbientIntegrable Ω 𝓕 P X) :
    P[X | 𝓗] =ᵐ[P] P[P[X | 𝓖] | 𝓗] := by
  have h_left : @def_13_3 Ω 𝓕 P 𝓗 h𝓗 X (P[X | 𝓗]) := by
    refine ⟨hX, @thm_13_6_condExp_integrable Ω 𝓕 P 𝓗 X,
      @thm_13_6_condExp_measurable Ω 𝓕 P 𝓗 X, ?_⟩
    intro B hB
    exact @thm_13_8_left_set_integral Ω 𝓕 P 𝓗 h𝓗 _ X hX B hB
  have h_right : @def_13_3 Ω 𝓕 P 𝓗 h𝓗 X (P[P[X | 𝓖] | 𝓗]) :=
    @thm_13_8_iterated_condExp_is_version Ω 𝓕 P 𝓖 𝓗 h𝓖 h𝓗 h𝓗𝓖 _ _ X hX
  exact @thm_13_4 Ω 𝓕 P _ 𝓗 h𝓗 X (P[X | 𝓗]) (P[P[X | 𝓖] | 𝓗])
    h_left h_right

 
theorem thm_13_8 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {𝓖 𝓗 : SigmaField Ω}
    (h𝓖 : IsSubSigmaField 𝓖 𝓕) (h𝓗𝓖 : IsSubSigmaField 𝓗 𝓖)
    [SigmaFinite (P.trim h𝓖)] {X : Ω → ℝ}
    (hX : @AmbientIntegrable Ω 𝓕 P X) :
    P[X | 𝓗] =ᵐ[P] P[P[X | 𝓖] | 𝓗] := by
  have h𝓗 : IsSubSigmaField 𝓗 𝓕 := fun {A} hA => h𝓖 (h𝓗𝓖 hA)
  haveI : SigmaFinite (P.trim h𝓗) := inferInstance
  exact @thm_13_8_via_versions Ω 𝓕 P _ 𝓖 𝓗 h𝓖 h𝓗 h𝓗𝓖 _ _ X hX
