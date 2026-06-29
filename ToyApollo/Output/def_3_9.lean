/-
TASK ID: def_3_9
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.Measure.NullMeasurable

open MeasureTheory Set

def IsNullSet {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (N : Set Ω) : Prop :=
  ∃ E, MeasurableSet E ∧ N ⊆ E ∧ μ E = 0

def IsCompleteSpace {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) : Prop :=
  ∀ N, IsNullSet μ N → MeasurableSet N
