/-
TASK ID: def_4_2
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic

open Set



def IsMeasurable {Ω Ω' : Type*} (F : MeasurableSpace Ω) (G : MeasurableSpace Ω')
    (f : Ω → Ω') : Prop :=
  ∀ B : Set Ω', @MeasurableSet Ω' G B → @MeasurableSet Ω F (f ⁻¹' B)
