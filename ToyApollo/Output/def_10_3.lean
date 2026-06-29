/-
TASK ID: def_10_3
TYPE: Definition
SOURCE PLAN: chapter10-mean
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory

noncomputable def meanDeviationMoment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (r : ℝ) (n : ℕ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (|Xn n ω - X ω| ^ r) ∂μ

noncomputable def ConvergesInRthMean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (r : ℝ) : Prop :=
  1 ≤ r ∧ Tendsto (fun n : ℕ => meanDeviationMoment μ Xn X r n) atTop (nhds 0)

noncomputable def ConvergesInMean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  ConvergesInRthMean μ Xn X 1

noncomputable def ConvergesInMeanSquare {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  ConvergesInRthMean μ Xn X 2

noncomputable def def_10_3 :=
  (@ConvergesInRthMean, @ConvergesInMean, @ConvergesInMeanSquare)
