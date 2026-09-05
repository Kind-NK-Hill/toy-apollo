/-
TASK ID: def_8_3
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef








open Set

 
def MeasurableRectangle
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (E₁ : Set α) (E₂ : Set β) : Set (α × β) :=
  E₁ ×ˢ E₂

 
def MeasurableRectangles
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] : Set (Set (α × β)) :=
  {s | ∃ E₁ : Set α, ∃ E₂ : Set β, MeasurableSet E₁ ∧ MeasurableSet E₂ ∧
      s = MeasurableRectangle E₁ E₂}



@[reducible]
def ProductSigmaField
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] : MeasurableSpace (α × β) :=
  inferInstance

 
theorem measurableRectangle_measurable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {E₁ : Set α} {E₂ : Set β}
    (hE₁ : MeasurableSet E₁) (hE₂ : MeasurableSet E₂) :
    MeasurableSet (MeasurableRectangle E₁ E₂) := by
  exact hE₁.prod hE₂

 
@[reducible]
def def_8_3
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] : MeasurableSpace (α × β) :=
  ProductSigmaField
