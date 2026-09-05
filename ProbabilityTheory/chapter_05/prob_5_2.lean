/-
TASK ID: prob_5_2
TYPE: Problem
SOURCE PLAN: 18_chap5_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory

theorem prob_5_2 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : Set Ω) (hA : MeasurableSet A) :
    IndepSet (∅ : Set Ω) A P :=
  indepSet_empty_left A
