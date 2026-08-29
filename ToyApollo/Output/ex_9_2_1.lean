/-
TASK ID: ex_9_2_1
TYPE: Example_Proof
SOURCE PLAN: chapter9-characteristic-functions
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_9_3

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable abbrev bernoulliValue : Bool → ℝ :=
  fun b => if b then 1 else 0

noncomputable abbrev bernoulliPMF (p : ℝ) : Bool → ℝ :=
  fun b => if b then p else 1 - p

noncomputable abbrev bernoulliCharacteristicFunction (p t : ℝ) : ℂ :=
  1 - (p : ℂ) + (p : ℂ) * Complex.exp (Complex.I * (t : ℂ))

theorem bernoulliCharacteristicFunction_finite_sum (p t : ℝ) :
    (∑ b : Bool,
        Complex.exp (Complex.I * (bernoulliValue b : ℂ) * (t : ℂ)) *
          (bernoulliPMF p b : ℂ)) =
      bernoulliCharacteristicFunction p t := by
  simp [bernoulliValue, bernoulliPMF, bernoulliCharacteristicFunction]
  ring

theorem ex_9_2_1 (p : Set.Icc (0 : ℝ) 1) (t : ℝ) :
    characteristicFunction (bernoulliMeasure (1 : ℝ) 0 p) t =
      bernoulliCharacteristicFunction (p : ℝ) t := by
  rw [characteristicFunction, charFun_apply_real, integral_bernoulliMeasure]
  simp [bernoulliCharacteristicFunction]
  ring
