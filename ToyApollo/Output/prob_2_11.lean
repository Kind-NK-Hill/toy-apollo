/-
TASK ID: prob_2_11
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.def_2_8

theorem prob_2_11 : MeasurableSet (cantorSet : Set ℝ) :=
  isClosed_cantorSet.measurableSet
