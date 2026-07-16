/-
TASK ID: def_3_2
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.def_3_1
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory ENNReal

def IsExtension {X : Type*}
    (F₀ : FieldOfSets X) (pm : Premeasure F₀)
    (μ : @Measure X (MeasurableSpace.generateFrom F₀.carrier)) : Prop :=
  ∀ (E : Set X) (hE : E ∈ F₀.carrier), μ E = pm.μ₀ ⟨E, hE⟩

def def_3_2 {X : Type*}
    (F₀ : FieldOfSets X) (pm : Premeasure F₀)
    (μ : @Measure X (MeasurableSpace.generateFrom F₀.carrier)) : Prop :=
  IsExtension F₀ pm μ
