/-
TASK ID: thm_4_1
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_4_2

theorem thm_4_1 {Ω : Type _} [MeasurableSpace Ω] (A : Set Ω) :
    Measurable (Set.indicator A (fun _ => (1 : ℝ))) ↔ MeasurableSet A := by
      constructor <;> intro h;
      · convert h ( MeasurableSingletonClass.measurableSet_singleton 1 ) using 1 ; aesop;
      · exact Measurable.indicator measurable_const h
