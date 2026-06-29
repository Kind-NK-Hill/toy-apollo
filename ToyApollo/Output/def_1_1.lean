/-
TASK ID: def_1_1
TYPE: Definition
SOURCE PLAN: 37_chap1_mixed_singular
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

open MeasureTheory Set

def IsSingularRealRandomVariable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) :
    Prop :=
  ∃ S : Set ℝ, volume S = 0 ∧ P (X ⁻¹' S) = 1

def IsSingularRandomVector {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ S : Set (EuclideanSpace ℝ (Fin n)), volume S = 0 ∧ P (X ⁻¹' S) = 1

def def_1_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) : Prop :=
  IsSingularRealRandomVariable P X
