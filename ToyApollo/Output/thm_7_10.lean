/-
TASK ID: thm_7_10
TYPE: Theorem_with_Proof
SOURCE PLAN: 28_chap7_pushforward_change_of_variable
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

namespace Thm710Support

def preimageSetFunction {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (B : Set ℝ) (_hB : MeasurableSet B) : ENNReal :=
  μ (X ⁻¹' B)

theorem preimageSetFunction_empty {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) :
    preimageSetFunction μ X ∅ MeasurableSet.empty = 0 := by
  simp [preimageSetFunction]

theorem preimageSetFunction_iUnion {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (hX : Measurable X) {B : ℕ → Set ℝ}
    (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Function.onFun Disjoint B)) :
    preimageSetFunction μ X (⋃ i, B i) (MeasurableSet.iUnion hB) =
      ∑' i, preimageSetFunction μ X (B i) (hB i) := by
  have hpre_meas : ∀ i, MeasurableSet (X ⁻¹' B i) := fun i => hX (hB i)
  have hpre_disj :
      Pairwise (Function.onFun Disjoint fun i => X ⁻¹' B i) := by
    intro i j hij
    exact Set.disjoint_left.2 fun _ hxi hxj =>
      Set.disjoint_left.1 (hdisj hij) hxi hxj
  change μ (X ⁻¹' ⋃ i, B i) = ∑' i, μ (X ⁻¹' B i)
  rw [Set.preimage_iUnion]
  exact μ.m_iUnion hpre_meas hpre_disj

noncomputable def constructedPushForward {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : Measurable X) : Measure ℝ :=
  Measure.ofMeasurable
    (preimageSetFunction μ X)
    (preimageSetFunction_empty μ X)
    (by
      intro B hB hdisj
      exact preimageSetFunction_iUnion μ X hX hB hdisj)

theorem constructedPushForward_apply {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : Measurable X)
    {B : Set ℝ} (hB : MeasurableSet B) :
    constructedPushForward μ X hX B = μ (X ⁻¹' B) := by
  rw [constructedPushForward, Measure.ofMeasurable_apply B hB]
  rfl

end Thm710Support

noncomputable def pushForwardRealMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) : Measure ℝ :=
  Measure.map X μ

theorem pushForwardRealMeasure_eq_constructed {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : Measurable X) :
    pushForwardRealMeasure μ X = Thm710Support.constructedPushForward μ X hX := by
  apply Measure.ext
  intro B hB
  rw [Thm710Support.constructedPushForward_apply μ X hX hB]
  simpa [pushForwardRealMeasure] using (Measure.map_apply hX hB)

theorem thm_7_10 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ)
    (hX : Measurable X) {B : Set ℝ} (hB : MeasurableSet B) :
    pushForwardRealMeasure μ X B = μ (X ⁻¹' B) := by
  rw [pushForwardRealMeasure_eq_constructed μ X hX]
  exact Thm710Support.constructedPushForward_apply μ X hX hB
