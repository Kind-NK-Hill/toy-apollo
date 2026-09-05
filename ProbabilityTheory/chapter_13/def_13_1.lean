/-
TASK ID: def_13_1
TYPE: Definition
SOURCE PLAN: chapter13-finite-partition
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped ENNReal

noncomputable section



def def_13_1_conditionalMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (_hA : MeasurableSet A)
    (_hA0 : P A ≠ 0) (_hA_top : P A ≠ ⊤) : Measure Ω :=
  (P A)⁻¹ • P.restrict A



theorem def_13_1_conditionalMeasure_apply {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A E : Set Ω) (hA : MeasurableSet A)
    (hA0 : P A ≠ 0) (hA_top : P A ≠ ⊤) (hE : MeasurableSet E) :
    def_13_1_conditionalMeasure P A hA hA0 hA_top E = P (A ∩ E) / P A := by
  rw [def_13_1_conditionalMeasure, Measure.smul_apply, Measure.restrict_apply hE]
  rw [Set.inter_comm]
  rw [ENNReal.div_eq_inv_mul]
  simp only [smul_eq_mul]

 
theorem def_13_1_conditionalMeasure_self {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (hA0 : P A ≠ 0) (hA_top : P A ≠ ⊤) :
    def_13_1_conditionalMeasure P A hA hA0 hA_top A = 1 := by
  rw [def_13_1_conditionalMeasure_apply P A A hA hA0 hA_top hA]
  rw [Set.inter_self]
  exact ENNReal.div_self hA0 hA_top



def def_13_1_conditionalEventExpectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (hA0 : P A ≠ 0) (hA_top : P A ≠ ⊤) (X : Ω → ℝ) : ℝ :=
  ∫ ω, X ω ∂def_13_1_conditionalMeasure P A hA hA0 hA_top

 
def def_13_1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (hA0 : P A ≠ 0) (hA_top : P A ≠ ⊤) (X : Ω → ℝ) : ℝ :=
  def_13_1_conditionalEventExpectation P A hA hA0 hA_top X
