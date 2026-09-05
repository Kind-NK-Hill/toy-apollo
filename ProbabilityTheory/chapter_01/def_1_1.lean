/-
TASK ID: def_1_1
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace







open MeasureTheory Set



def IsSingularRealRandomVariable {Ω : Type*}
  [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) :
    Prop :=
  ∃ S : Set ℝ, volume S = 0 ∧ P (X ⁻¹' S) = 1




def IsSingularRandomVector {Ω : Type*}
  [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ S : Set (EuclideanSpace ℝ (Fin n)), volume S = 0 ∧ P (X ⁻¹' S) = 1



def def_1_1 {Ω : Type*}
  [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) : Prop :=
  IsSingularRealRandomVariable P X
