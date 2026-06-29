/-
TASK ID: prob_1_10
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

open MeasureTheory Set

theorem prob_1_10
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsupp : μ (Iio 0) = 0)
    (hboundary :
      Filter.Tendsto (fun x : ℝ => x * (1 - (μ (Iic x)).toReal)) Filter.atTop
        (nhds 0)) :
    ∫ x, x ∂μ = ∫ t in Ioi 0, (μ (Ioi t)).toReal := by
  convert MeasureTheory.integral_eq_lintegral_of_nonneg_ae _ _ using 1;
  · convert MeasureTheory.integral_eq_lintegral_of_nonneg_ae _ _ using 1;
    · rw [ MeasureTheory.lintegral_eq_lintegral_meas_lt ];
      · simp +decide [ Set.Ioi_def ];
      · filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hsupp ] with x hx using le_of_not_gt hx;
      · exact measurable_id.aemeasurable;
    · exact Filter.Eventually.of_forall fun x => ENNReal.toReal_nonneg;
    · refine' Measurable.aestronglyMeasurable _;
      refine' Measurable.ennreal_toReal _;
      convert ( Antitone.measurable ( show Antitone fun t => μ ( Set.Ioi t ) from fun x y hxy => MeasureTheory.measure_mono <| Set.Ioi_subset_Ioi hxy ) ) using 1;
  · filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hsupp ] with x hx using le_of_not_gt hx;
  · exact measurable_id.aestronglyMeasurable
