import Mathlib

open MeasureTheory Set

noncomputable section

/-- The real-line version of the textbook common probability space `[0,1]`
used in the Skorokhod quantile construction.  The carrier is still `Real`, with
Lebesgue measure restricted to `(0,1]`, matching the current
`SkorokhodRepresentation` witness shape. -/
def thm_10_8_unitIntervalMeasure : Measure ℝ :=
  volume.restrict (Ioc (0 : ℝ) 1)

theorem thm_10_8_unitIntervalMeasure_univ :
    thm_10_8_unitIntervalMeasure univ = 1 := by
  rw [thm_10_8_unitIntervalMeasure, Measure.restrict_apply MeasurableSet.univ]
  simp [Real.volume_Ioc]

instance thm_10_8_unitIntervalMeasure_isProbabilityMeasure :
    IsProbabilityMeasure thm_10_8_unitIntervalMeasure :=
  ⟨thm_10_8_unitIntervalMeasure_univ⟩

/-- The unit interval has full mass under the Skorokhod witness measure. -/
theorem thm_10_8_unitIntervalMeasure_Ioc :
    thm_10_8_unitIntervalMeasure (Ioc (0 : ℝ) 1) = 1 := by
  rw [thm_10_8_unitIntervalMeasure, Measure.restrict_apply measurableSet_Ioc]
  simp [Real.volume_Ioc]
