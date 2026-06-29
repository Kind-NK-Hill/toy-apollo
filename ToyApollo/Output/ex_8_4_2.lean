/-
TASK ID: ex_8_4_2
TYPE: Example_Proof
SOURCE PLAN: 34_chap8_total_variation_distance
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.ch8_bernoulli_bool_core

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set
open Ch8BernoulliBoolCore

noncomputable def ex842TotalVariationDistance
    {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) : ℝ :=
  sSup {d : ℝ | ∃ A : Set Ω, MeasurableSet A ∧ d = |P.real A - Q.real A|}

theorem ex_8_4_2 (p q : NNReal) (hp : p ≤ 1) (hq : q ≤ 1) :
    ex842TotalVariationDistance (bernoulliMeasure p hp) (bernoulliMeasure q hq)
      = |(p : ℝ) - q| := by
  simpa [ex842TotalVariationDistance, totalVariationDistance] using
    boolBernoulli_totalVariationDistance_eq_abs p q hp hq
