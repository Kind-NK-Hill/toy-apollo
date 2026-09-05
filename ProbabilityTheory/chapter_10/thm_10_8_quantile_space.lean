/-
TASK ID: thm_10_8_quantile_space
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

open MeasureTheory Set

noncomputable section



def thm_10_8_unitIntervalMeasure : Measure ℝ :=
  volume.restrict (Ioc (0 : ℝ) 1)

theorem thm_10_8_unitIntervalMeasure_univ :
    thm_10_8_unitIntervalMeasure univ = 1 := by
  rw [thm_10_8_unitIntervalMeasure, Measure.restrict_apply MeasurableSet.univ]
  simp [Real.volume_Ioc]

instance thm_10_8_unitIntervalMeasure_isProbabilityMeasure :
    IsProbabilityMeasure thm_10_8_unitIntervalMeasure :=
  ⟨thm_10_8_unitIntervalMeasure_univ⟩

 
theorem thm_10_8_unitIntervalMeasure_Ioc :
    thm_10_8_unitIntervalMeasure (Ioc (0 : ℝ) 1) = 1 := by
  rw [thm_10_8_unitIntervalMeasure, Measure.restrict_apply measurableSet_Ioc]
  simp [Real.volume_Ioc]
