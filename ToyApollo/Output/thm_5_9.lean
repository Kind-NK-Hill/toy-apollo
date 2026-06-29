/-
TASK ID: thm_5_9
TYPE: Theorem_with_Proof
SOURCE PLAN: 16_chap5_borel_cantelli
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_5_6

-- WRITE FINAL LEAN CODE BELOW
open Filter
open scoped ENNReal Topology

theorem thm_5_9 {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (A : ℕ → Set Ω)
    (h_meas : ∀ n, MeasurableSet (A n))
    (h_indep : ProbabilityTheory.iIndepSet A P)
    (h_series : (∑' n, P (A n)) = ∞) :
    P (limsup A atTop) = 1 := by
  simpa using ProbabilityTheory.measure_limsup_eq_one (μ := P) h_meas h_indep h_series
