/-
TASK ID: thm_13_1
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-finite-partition
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_13.def_13_1




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

noncomputable section



theorem thm_13_1_indicator_formula {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A B : Set Ω) (hA : MeasurableSet A)
    (hA0 : P A ≠ 0) (hA_top : P A ≠ ⊤) :
    def_13_1 P A hA hA0 hA_top (B.indicator fun _ => (1 : ℝ)) =
      (∫ ω in A, B.indicator (fun _ => (1 : ℝ)) ω ∂P) / (P A).toReal := by
  unfold def_13_1 def_13_1_conditionalEventExpectation def_13_1_conditionalMeasure
  rw [integral_smul_measure]
  simp [smul_eq_mul, one_div, div_eq_inv_mul]



theorem thm_13_1_simple_formula {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (hA0 : P A ≠ 0) (hA_top : P A ≠ ⊤) (X : Ω → ℝ) :
    def_13_1 P A hA hA0 hA_top X = (∫ ω in A, X ω ∂P) / (P A).toReal := by
  unfold def_13_1 def_13_1_conditionalEventExpectation def_13_1_conditionalMeasure
  rw [integral_smul_measure]
  simp [smul_eq_mul, one_div, div_eq_inv_mul]



theorem thm_13_1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (hA0 : P A ≠ 0) (hA_top : P A ≠ ⊤) (X : Ω → ℝ) :
    def_13_1 P A hA hA0 hA_top X =
      (1 / (P A).toReal) * ∫ ω in A, X ω ∂P := by
  unfold def_13_1 def_13_1_conditionalEventExpectation def_13_1_conditionalMeasure
  rw [integral_smul_measure]
  simp [smul_eq_mul, one_div, div_eq_inv_mul]
