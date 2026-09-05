/-
TASK ID: ex_3_2_1
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_03.def_3_5
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Order.Basic
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic




open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

 
def example_1_identity : StieltjesMeasureFunction where
  toFun := id
  non_decreasing := monotone_id
  right_continuous _ := continuous_id.continuousWithinAt

 
noncomputable def example_2_step (x₀ : ℝ) : StieltjesMeasureFunction where
  toFun := fun x => if x₀ ≤ x then 1 else 0
  non_decreasing := fun x y hxy => by
    simp only
    split_ifs with hx hy hx_not
    · exact le_refl 1
    · exact (hy (hx.trans hxy)).elim
    · exact zero_le_one
    · exact le_refl 0
  right_continuous x := by
    by_cases h : x₀ ≤ x
    · -- neighborhood where value is 1
      refine ContinuousWithinAt.congr_of_eventuallyEq (f := fun _ => 1) 
        continuousWithinAt_const ?_ ?_
      · filter_upwards [self_mem_nhdsWithin (s := Ici x)] with y hy
        simp only [h.trans hy, ↓reduceIte]
      · simp only [h, ↓reduceIte]
    · -- neighborhood where value is 0
      refine ContinuousWithinAt.congr_of_eventuallyEq (f := fun _ => 0) 
        continuousWithinAt_const ?_ ?_
      · have h_lt : x < x₀ := not_le.mp h
        filter_upwards [inter_mem_nhdsWithin (Ici x) (Iio_mem_nhds h_lt)] with y hy
        simp only [not_le.mpr (mem_Iio.mp hy.2), ↓reduceIte]
      · simp only [h, ↓reduceIte]

 
noncomputable def example_3_cdf (P : Measure ℝ) [IsProbabilityMeasure P] : 
    StieltjesMeasureFunction where
  toFun := cdf P
  non_decreasing := (cdf P).mono'
  right_continuous x := (cdf P).right_continuous' x
