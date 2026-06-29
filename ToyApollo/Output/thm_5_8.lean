/-
TASK ID: thm_5_8
TYPE: Theorem_with_Proof
SOURCE PLAN: 16_chap5_borel_cantelli
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_3_8

-- WRITE FINAL LEAN CODE BELOW

open Filter
open scoped ENNReal Topology

theorem thm_5_8 {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (A : ℕ → Set Ω)
    (h_series : (∑' n, P (A n)) ≠ ∞) :
    P (limsup A atTop) = 0 := by
  simpa using MeasureTheory.measure_limsup_atTop_eq_zero (μ := P) (s := A) h_series
