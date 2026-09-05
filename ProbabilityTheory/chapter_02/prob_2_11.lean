/-
TASK ID: prob_2_11
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_02.def_2_8
import Mathlib.Topology.Instances.CantorSet



theorem prob_2_11 : MeasurableSet (cantorSet : Set ℝ) :=
  isClosed_cantorSet.measurableSet
