/-
TASK ID: def_12_5
TYPE: Definition
SOURCE PLAN: chapter12-closed-subspace-projection
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_12_4

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

def def_12_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (W : ClosedSubmodule ℝ (Ω →₂[P] ℝ)) (Y : Ω →₂[P] ℝ) : W :=
  Classical.choose (thm_12_4 P W Y)

theorem def_12_5_minimizes {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (W : ClosedSubmodule ℝ (Ω →₂[P] ℝ)) (Y : Ω →₂[P] ℝ) :
    ‖Y - (def_12_5 P W Y : Ω →₂[P] ℝ)‖ =
      ⨅ Z : W, ‖Y - (Z : Ω →₂[P] ℝ)‖ :=
  (Classical.choose_spec (thm_12_4 P W Y)).1

theorem def_12_5_unique {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (W : ClosedSubmodule ℝ (Ω →₂[P] ℝ)) (Y : Ω →₂[P] ℝ)
    (X : W)
    (hX : ‖Y - (X : Ω →₂[P] ℝ)‖ =
      ⨅ Z : W, ‖Y - (Z : Ω →₂[P] ℝ)‖) :
    X = def_12_5 P W Y :=
  (Classical.choose_spec (thm_12_4 P W Y)).2 X hX
