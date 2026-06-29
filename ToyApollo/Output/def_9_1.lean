/-
TASK ID: def_9_1
TYPE: Definition
SOURCE PLAN: chapter9-moments-mgf
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory

noncomputable abbrev rthMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (r : ℕ) : ℝ :=
  moment X r μ

noncomputable abbrev rthCentralMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (r : ℕ) : ℝ :=
  centralMoment X r μ

noncomputable abbrev variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : ℝ :=
  rthCentralMoment μ X 2

noncomputable abbrev standardDeviation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : ℝ :=
  Real.sqrt (variance μ X)

noncomputable abbrev skewness {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : ℝ :=
  rthCentralMoment μ X 3 / standardDeviation μ X ^ 3

noncomputable abbrev kurtosis {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : ℝ :=
  rthCentralMoment μ X 4 / standardDeviation μ X ^ 4

noncomputable def def_9_1 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (r : ℕ) : ℝ × ℝ :=
  (rthMoment μ X r, rthCentralMoment μ X r)
