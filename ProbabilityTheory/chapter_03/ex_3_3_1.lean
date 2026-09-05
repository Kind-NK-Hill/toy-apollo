/-
TASK ID: ex_3_3_1
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Group.Pointwise
import Mathlib.Tactic

open MeasureTheory Set Measure

 
theorem stieltjes_id_measure_eq_volume :
    StieltjesFunction.id.measure = (volume : Measure ℝ) := by
  simpa using
    (Real.volume_eq_stieltjes_id : (volume : Measure ℝ) = StieltjesFunction.id.measure).symm

 
theorem stieltjes_id_measure_Icc (a b : ℝ) :
    StieltjesFunction.id.measure (Icc a b) = ENNReal.ofReal (b - a) := by
  rw [stieltjes_id_measure_eq_volume]
  simp

 
theorem lebesgue_measure_Icc (a b : ℝ) :
    volume (Icc a b) = ENNReal.ofReal (b - a) := by
  simp



theorem lebesgue_measure_translation_invariant (S : Set ℝ) (hS : MeasurableSet S) (c : ℝ) :
    volume ((fun x => x + c) '' S) = volume S := by
  let f := fun x : ℝ => x + c
  let g := fun x : ℝ => x - c
  have hf : Function.LeftInverse g f := fun x => add_sub_cancel_right x c
  have hg : Function.RightInverse g f := fun x => sub_add_cancel x c
  rw [Set.image_eq_preimage_of_inverse hf hg]
  rw [← Measure.map_apply (measurable_sub_const c) hS]
  simp_rw [sub_eq_add_neg]
  rw [map_add_right_eq_self volume (-c)]
