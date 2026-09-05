/-
TASK ID: thm_5_10
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.BorelCantelli








-- WRITE FINAL LEAN CODE BELOW
open Filter
open scoped ENNReal Topology



theorem thm_5_10 {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (A : ℕ → Set Ω)
    (h_meas : ∀ n, MeasurableSet (A n))
    (h_indep : ProbabilityTheory.iIndepSet A P) :
    P (limsup A atTop) = if (∑' n, P (A n)) = ∞ then 1 else 0 := by
  by_cases h_series : (∑' n, P (A n)) = ∞
  · simp [h_series, ProbabilityTheory.measure_limsup_eq_one (μ := P) h_meas h_indep h_series]
  · simp [h_series, MeasureTheory.measure_limsup_atTop_eq_zero (μ := P) (s := A) h_series]
