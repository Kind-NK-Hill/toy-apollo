/-
TASK ID: prob_12_1
TYPE: Problem
SOURCE PLAN: chapter12-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_12_2
import ToyApollo.Output.thm_12_1

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped InnerProductSpace

theorem prob_12_1 {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (u v : E) :
    ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := 𝕜), norm_sub_sq (𝕜 := 𝕜)]
  ring

theorem prob_12_1_l2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (u v : Ω →₂[P] ℝ) :
    ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 :=
  prob_12_1 (𝕜 := ℝ) u v
