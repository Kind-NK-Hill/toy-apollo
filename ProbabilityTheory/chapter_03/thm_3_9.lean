/-
TASK ID: thm_3_9
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Data.Real.Basic




open MeasureTheory Set



theorem thm_3_9 (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
  (h : ∀ x : ℝ, P (Iic x) = Q (Iic x)) :
  P = Q := by
    apply_rules [ MeasureTheory.Measure.ext_of_Iic, h ]
