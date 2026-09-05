/-
TASK ID: ex_13_3_1
TYPE: Example_Proof
SOURCE PLAN: chapter13-properties
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_13.def_13_4
import ProbabilityTheory.chapter_13.ex_13_2_1
import ProbabilityTheory.chapter_13.thm_13_8




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

noncomputable section



theorem ex_13_3_1_sigmaY_subSigma {Ω S : Type*} [𝓕 : MeasurableSpace Ω]
    [MeasurableSpace S] {Y : Ω → S} (hY : @Measurable Ω S 𝓕 _ Y) :
    IsSubSigmaField (def_13_4_sigma Y) 𝓕 :=
  def_13_4_sigma_subSigma_of_measurable hY



theorem ex_13_3_1_bottom_under_sigmaY {Ω S : Type*} [MeasurableSpace S]
    (Y : Ω → S) :
    IsSubSigmaField (⊥ : SigmaField Ω) (def_13_4_sigma Y) :=
  @ex_13_2_1_bottom_subSigma Ω (def_13_4_sigma Y)



theorem ex_13_3_1_bottom_version {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {Z : Ω → ℝ}
    (hZ : @AmbientIntegrable Ω 𝓕 P Z) :
    @def_13_3 Ω 𝓕 P (⊥ : SigmaField Ω)
      (@ex_13_2_1_bottom_subSigma Ω 𝓕) Z
      (ex_13_2_1_trivialConditionalExpectation P Z) :=
  ex_13_2_1 P hZ

 
theorem ex_13_3_1_tower_to_bottom {Ω S : Type*} [𝓕 : MeasurableSpace Ω]
    [MeasurableSpace S] {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → S}
    (hY : @Measurable Ω S 𝓕 _ Y)
    {X : Ω → ℝ} (hX : @AmbientIntegrable Ω 𝓕 P X) :
    P[X | (⊥ : SigmaField Ω)] =ᵐ[P]
      P[P[X | def_13_4_sigma Y] | (⊥ : SigmaField Ω)] :=
  thm_13_8 (P := P) (𝓖 := def_13_4_sigma Y) (𝓗 := ⊥) (X := X)
    (ex_13_3_1_sigmaY_subSigma hY)
    (ex_13_3_1_bottom_under_sigmaY Y) hX



theorem ex_13_3_1_mathlib_bottom_version {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : Ω → ℝ}
    (hZ : @AmbientIntegrable Ω 𝓕 P Z) :
    @def_13_3 Ω 𝓕 P (⊥ : SigmaField Ω)
      (@ex_13_2_1_bottom_subSigma Ω 𝓕) Z
      (P[Z | (⊥ : SigmaField Ω)]) := by
  refine ⟨hZ, @thm_13_6_condExp_integrable Ω 𝓕 P (⊥ : SigmaField Ω) Z,
    @thm_13_6_condExp_measurable Ω 𝓕 P (⊥ : SigmaField Ω) Z, ?_⟩
  intro B hB
  exact @thm_13_6_condExp_set_integral Ω 𝓕 P (⊥ : SigmaField Ω)
    (@ex_13_2_1_bottom_subSigma Ω 𝓕) _ Z hZ B hB



theorem ex_13_3_1_condExp_bottom_eq_trivial {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : Ω → ℝ} (hZ : @AmbientIntegrable Ω 𝓕 P Z) :
    P[Z | (⊥ : SigmaField Ω)] =ᵐ[P]
      (@ex_13_2_1_trivialConditionalExpectation Ω 𝓕 P Z) :=
  @thm_13_4 Ω 𝓕 P _ (⊥ : SigmaField Ω)
    (@ex_13_2_1_bottom_subSigma Ω 𝓕) Z
    (P[Z | (⊥ : SigmaField Ω)])
    (@ex_13_2_1_trivialConditionalExpectation Ω 𝓕 P Z)
    (ex_13_3_1_mathlib_bottom_version hZ)
    (@ex_13_3_1_bottom_version Ω 𝓕 P _ Z hZ)



theorem ex_13_3_1 {Ω S : Type*} [𝓕 : MeasurableSpace Ω] [MeasurableSpace S]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → S}
    (hY : @Measurable Ω S 𝓕 _ Y)
    {X : Ω → ℝ} (hX : @AmbientIntegrable Ω 𝓕 P X) :
    ∫ ω, P[X | def_13_4_sigma Y] ω ∂P = ∫ ω, X ω ∂P := by
  let 𝓖 : SigmaField Ω := def_13_4_sigma Y
  have h_tower : P[X | (⊥ : SigmaField Ω)] =ᵐ[P]
      P[P[X | 𝓖] | (⊥ : SigmaField Ω)] := by
    exact @ex_13_3_1_tower_to_bottom Ω S 𝓕 _ P _ Y hY X hX
  have h_bottom_X : P[X | (⊥ : SigmaField Ω)] =ᵐ[P]
      (@ex_13_2_1_trivialConditionalExpectation Ω 𝓕 P X) :=
    @ex_13_3_1_condExp_bottom_eq_trivial Ω 𝓕 P _ X hX
  have h_bottom_cond : P[P[X | 𝓖] | (⊥ : SigmaField Ω)] =ᵐ[P]
      (@ex_13_2_1_trivialConditionalExpectation Ω 𝓕 P (P[X | 𝓖])) :=
    @ex_13_3_1_condExp_bottom_eq_trivial Ω 𝓕 P _ (P[X | 𝓖])
      (@thm_13_6_condExp_integrable Ω 𝓕 P 𝓖 X)
  have h_constants :
      (@ex_13_2_1_trivialConditionalExpectation Ω 𝓕 P X) =ᵐ[P]
        (@ex_13_2_1_trivialConditionalExpectation Ω 𝓕 P (P[X | 𝓖])) :=
    h_bottom_X.symm.trans (h_tower.trans h_bottom_cond)
  have h_integrals :
      ∫ ω, (@ex_13_2_1_trivialConditionalExpectation Ω 𝓕 P X) ω ∂P =
        ∫ ω, (@ex_13_2_1_trivialConditionalExpectation Ω 𝓕 P (P[X | 𝓖])) ω ∂P :=
    integral_congr_ae h_constants
  simpa [ex_13_2_1_trivialConditionalExpectation] using h_integrals.symm
