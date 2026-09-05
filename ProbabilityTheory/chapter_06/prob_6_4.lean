/-
TASK ID: prob_6_4
TYPE: Problem
SOURCE PLAN: 24_chap6_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

theorem prob_6_4 (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ENNReal) (hX_meas : Measurable X) (hX_fin : ∫⁻ ω, X ω ∂P < ⊤) :
    P {ω | X ω = ⊤} = 0 := by
  convert MeasureTheory.measure_eq_zero_iff_ae_notMem.2 _
  · infer_instance
  · convert MeasureTheory.ae_lt_top hX_meas (ne_of_lt hX_fin) using 1
    aesop
