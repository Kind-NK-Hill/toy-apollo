/-
TASK ID: def_6_3
TYPE: Definition
SOURCE PLAN: 20_chap6_nonnegative_functions
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

def simpleApproximationSet (X : Ω → ENNReal) : Set (SimpleFunc Ω ENNReal) :=
  {f | ∀ ω, f ω ≤ X ω}

noncomputable def def_6_3 (μ : Measure Ω) (X : Ω → ENNReal) : ENNReal :=
  ∫⁻ ω, X ω ∂μ
