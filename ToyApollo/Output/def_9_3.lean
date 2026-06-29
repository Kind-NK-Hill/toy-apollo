/-
TASK ID: def_9_3
TYPE: Definition
SOURCE PLAN: chapter9-characteristic-functions
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_6_6

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped BigOperators

noncomputable abbrev characteristicFunction {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (t : ℝ) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ)) ∂μ

noncomputable abbrev densityCharacteristicFunction
    (f : ℝ → ℝ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) * (f x : ℂ)

noncomputable abbrev discreteCharacteristicFunction
    {ι : Type*} (x : ι → ℝ) (p : ι → ℝ) (t : ℝ) : ℂ :=
  ∑' n : ι, Complex.exp (Complex.I * (x n : ℂ) * (t : ℂ)) * (p n : ℂ)

noncomputable def def_9_3 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : ℝ → ℂ :=
  characteristicFunction μ X
