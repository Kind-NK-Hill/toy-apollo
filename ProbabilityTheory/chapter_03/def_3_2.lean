/-
TASK ID: def_3_2
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_03.def_3_1
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory ENNReal



def IsExtension {X : Type*} (F₀ : Set (Set X)) (μ₀ : Set X → ℝ≥0∞)
    (μ : @Measure X (MeasurableSpace.generateFrom F₀)) : Prop :=
  ∀ E ∈ F₀, μ E = μ₀ E
