/-
TASK ID: prob_11_1
TYPE: Problem
SOURCE PLAN: chapter11-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_11_3

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

theorem prob_11_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : Ω → ℝ} {r s : ℕ}
    (hrs : r < s) (hs : MemLp X (s : ENNReal) P) :
    MemLp X (r : ENNReal) P := by
  exact hs.mono_exponent (by exact_mod_cast le_of_lt hrs)

theorem prob_11_1_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : Ω → ℝ} {r s : ℕ}
    (hrs : r ≤ s) (hs : MemLp X (s : ENNReal) P) :
    MemLp X (r : ENNReal) P := by
  exact hs.mono_exponent (by exact_mod_cast hrs)
