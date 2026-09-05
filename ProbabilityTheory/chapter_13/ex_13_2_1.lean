/-
TASK ID: ex_13_2_1
TYPE: Example_Proof
SOURCE PLAN: chapter13-sub-sigma-algebra
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_13.def_13_3




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

noncomputable section

 
theorem ex_13_2_1_bottom_subSigma {Ω : Type*} [𝓕 : MeasurableSpace Ω] :
    IsSubSigmaField (⊥ : SigmaField Ω) 𝓕 := by
  intro A hA
  rcases MeasurableSpace.measurableSet_bot_iff.mp hA with rfl | rfl
  · exact MeasurableSet.empty
  · exact MeasurableSet.univ



def ex_13_2_1_trivialConditionalExpectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) : Ω → ℝ :=
  fun _ => ∫ ω, X ω ∂P



theorem ex_13_2_1 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Integrable X P) :
    @def_13_3 Ω 𝓕 P (⊥ : SigmaField Ω)
      (@ex_13_2_1_bottom_subSigma Ω 𝓕) X
      (ex_13_2_1_trivialConditionalExpectation P X) := by
  refine ⟨hX, ?_, ?_, ?_⟩
  · unfold ex_13_2_1_trivialConditionalExpectation
    exact integrable_const _
  · unfold ex_13_2_1_trivialConditionalExpectation
    exact measurable_const
  · intro B hB
    rcases MeasurableSpace.measurableSet_bot_iff.mp hB with rfl | rfl
    · simp [ex_13_2_1_trivialConditionalExpectation]
    · simp [ex_13_2_1_trivialConditionalExpectation]
