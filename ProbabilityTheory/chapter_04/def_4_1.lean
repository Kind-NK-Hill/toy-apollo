/-
TASK ID: def_4_1
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic





open MeasureTheory Set



def IsRealMeasurable {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) : Prop :=
  ∀ B : Set ℝ, MeasurableSet B → MeasurableSet (X ⁻¹' B)



example {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) :
    IsRealMeasurable X ↔ Measurable X :=
  Iff.rfl
