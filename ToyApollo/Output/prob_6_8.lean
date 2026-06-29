/-
TASK ID: prob_6_8
TYPE: Problem
SOURCE PLAN: 24_chap6_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

theorem prob_6_8 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ENNReal)
    (hX : Measurable X) (hint : ∫⁻ ω, X ω ∂μ = 1) : IsProbabilityMeasure (μ.withDensity X) := by
  constructor
  aesop
