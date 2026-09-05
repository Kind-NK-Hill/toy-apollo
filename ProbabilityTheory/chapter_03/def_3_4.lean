/-
TASK ID: def_3_4
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Probability.CDF





open MeasureTheory Set



noncomputable def distributionFunction (P : Measure ℝ) [IsProbabilityMeasure P]
    (x : ℝ) : ℝ :=
  (P (Iic x)).toReal
