/-
TASK ID: thm_13_3
TYPE: Theorem_Statement
SOURCE PLAN: chapter13-sub-sigma-algebra
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_12.thm_12_6
import ProbabilityTheory.chapter_13.thm_13_3_l2_support




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory
open scoped InnerProductSpace

noncomputable section



def thm_13_3_candidate {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (P : Measure Ω) (𝓖 : SigmaField Ω) (Z : Ω → ℝ) : Prop :=
  GMeasurable 𝓖 Z ∧ @L2Function Ω 𝓕 P Z



def thm_13_3_l2Error {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (P : Measure Ω) (X Z : Ω → ℝ)
    (hX : @L2Function Ω 𝓕 P X) (hZ : @L2Function Ω 𝓕 P Z) : ℝ :=
  ‖@L2Function.toLp Ω 𝓕 P X hX - @L2Function.toLp Ω 𝓕 P Z hZ‖



def thm_13_3_MMSE {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (P : Measure Ω) (𝓖 : SigmaField Ω) (X Y : Ω → ℝ) : Prop :=
  ∃ hX : @L2Function Ω 𝓕 P X, ∃ hY : @L2Function Ω 𝓕 P Y,
    GMeasurable 𝓖 Y ∧
      ∀ Z : Ω → ℝ, ∀ hZ : @thm_13_3_candidate Ω 𝓕 P 𝓖 Z,
        @thm_13_3_l2Error Ω 𝓕 P X Y hX hY ≤
          @thm_13_3_l2Error Ω 𝓕 P X Z hX hZ.2



theorem thm_13_3_candidate_of_l2_projection {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω} {X Y : Ω → ℝ}
    (h : @ConditionalExpectationL2ProjectionFormula Ω 𝓕 P 𝓖 X Y) :
    @thm_13_3_candidate Ω 𝓕 P 𝓖 Y := by
  rcases h with ⟨_hX, hY, hYg, _hinner⟩
  exact ⟨hYg, hY⟩



theorem thm_13_3_equal_inner_products {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω} {X Y Z : Ω → ℝ}
    (h :
      @ConditionalExpectationL2ProjectionFormula Ω 𝓕 P 𝓖 X Y)
    (hZ : @thm_13_3_candidate Ω 𝓕 P 𝓖 Z) :
    ∃ hX : @L2Function Ω 𝓕 P X, ∃ hY : @L2Function Ω 𝓕 P Y,
      @l2Inner Ω 𝓕 P Y Z hY hZ.2 =
        @l2Inner Ω 𝓕 P X Z hX hZ.2 := by
  rcases h with ⟨hX, hY, _hYg, hinner⟩
  exact ⟨hX, hY, hinner Z hZ.1 hZ.2⟩



theorem thm_13_3_sigma_measurable_factorization {Ω S : Type*}
    [MeasurableSpace S] (feature : Ω → S) (Y : Ω → ℝ) :
    (∃ g : S → ℝ, Measurable g ∧ Y = g ∘ feature) ↔
      Measurable[(inferInstance : MeasurableSpace S).comap feature] Y :=
  thm_12_6 feature Y



theorem thm_13_3_mmse_of_l2_projection_formula {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω} {𝓖 : SigmaField Ω} {X Y : Ω → ℝ}
    (hCE : @ConditionalExpectationL2ProjectionFormula Ω 𝓕 P 𝓖 X Y) :
    @thm_13_3_MMSE Ω 𝓕 P 𝓖 X Y := by
  rcases hCE with ⟨hX, hY, hYg, hinner⟩
  refine ⟨hX, hY, hYg, ?_⟩
  intro Z hZc
  rcases hZc with ⟨hZg, hZ⟩
  let D : Ω → ℝ := Z - Y
  have hDg : GMeasurable 𝓖 D := by
    exact gMeasurable_sub hZg hYg
  have hD : @L2Function Ω 𝓕 P D :=
    @l2Function_sub Ω 𝓕 P Z Y hZ hY
  have hraw :
      @l2Inner Ω 𝓕 P Y D hY hD =
        @l2Inner Ω 𝓕 P X D hX hD :=
    hinner D hDg hD
  have horthD :
      ⟪@L2Function.toLp Ω 𝓕 P X hX - @L2Function.toLp Ω 𝓕 P Y hY,
        @L2Function.toLp Ω 𝓕 P D hD⟫_ℝ = 0 := by
    rw [inner_sub_left,
      @l2Function_toLp_inner_eq_l2Inner Ω 𝓕 P X D hX hD,
      @l2Function_toLp_inner_eq_l2Inner Ω 𝓕 P Y D hY hD]
    linarith
  have hD_toLp :
      @L2Function.toLp Ω 𝓕 P D hD =
        @L2Function.toLp Ω 𝓕 P Z hZ - @L2Function.toLp Ω 𝓕 P Y hY := by
    dsimp [D]
    unfold L2Function.toLp
    rw [MemLp.toLp_sub]
  have horth :
      ⟪@L2Function.toLp Ω 𝓕 P X hX - @L2Function.toLp Ω 𝓕 P Y hY,
        @L2Function.toLp Ω 𝓕 P Z hZ - @L2Function.toLp Ω 𝓕 P Y hY⟫_ℝ = 0 := by
    rw [← hD_toLp]
    exact horthD
  exact
    hilbert_norm_le_of_inner_sub_eq_zero
      (@L2Function.toLp Ω 𝓕 P X hX)
      (@L2Function.toLp Ω 𝓕 P Y hY)
      (@L2Function.toLp Ω 𝓕 P Z hZ)
      horth



theorem thm_13_3 {Ω : Type*} [𝓕 : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓖 : SigmaField Ω)
    (h𝓖 : IsSubSigmaField 𝓖 𝓕) {X Y : Ω → ℝ}
    (hCE : @def_13_3 Ω 𝓕 P 𝓖 h𝓖 X Y)
    (hX : @L2Function Ω 𝓕 P X) :
    @thm_13_3_MMSE Ω 𝓕 P 𝓖 X Y := by
  exact thm_13_3_mmse_of_l2_projection_formula
    (Ω := Ω) (𝓕 := 𝓕) (P := P) (𝓖 := 𝓖) (X := X) (Y := Y)
    (def_13_3_to_l2_projection_formula
      (Ω := Ω) (𝓕 := 𝓕) (P := P) (𝓖 := 𝓖) (h𝓖 := h𝓖)
      (X := X) (Y := Y) hCE hX)
