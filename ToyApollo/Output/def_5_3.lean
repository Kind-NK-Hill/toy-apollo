/-
TASK ID: def_5_3
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

def def_5_3 {Ω β : Type _} [MeasurableSpace Ω] [MeasurableSpace β] (X : Ω → β) :
    MeasurableSpace Ω :=
  MeasurableSpace.comap X inferInstance
