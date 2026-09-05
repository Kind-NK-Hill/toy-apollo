/-
TASK ID: thm_5_8
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import ProbabilityTheory.chapter_03.def_3_8







open Filter
open scoped ENNReal Topology



theorem thm_5_8 {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (A : ℕ → Set Ω)
    (h_series : (∑' n, P (A n)) ≠ ∞) :
    P (limsup A atTop) = 0 := by
  simpa using MeasureTheory.measure_limsup_atTop_eq_zero (μ := P) (s := A) h_series
