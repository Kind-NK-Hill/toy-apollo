/-
TASK ID: prob_3_5
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

open MeasureTheory Set



theorem prob_3_5 (F : StieltjesFunction ℝ) (h : F.measure Set.univ = 1) :
    Set.Countable {x | ¬ContinuousAt F x} := by
      apply_rules [ Monotone.countable_not_continuousAt, F.mono ]
