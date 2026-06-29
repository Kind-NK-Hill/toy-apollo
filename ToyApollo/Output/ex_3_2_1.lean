import ToyApollo.Output.def_3_5
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Order.Basic
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Example 3.2.1: Examples of Stieltjes Measure Functions

We formalize three examples:
1. Identity function.
2. Unit step function.
3. Probability distribution function.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

/-- 1. Identity function F(x) = x. -/
def example_1_identity : StieltjesMeasureFunction where
  toFun := id
  non_decreasing := monotone_id
  right_continuous _ := continuous_id.continuousWithinAt

/-- 2. Step function F(x) = 1 if x ≥ x₀ else 0. -/
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

/-- 3. CDF of a probability measure P. -/
noncomputable def example_3_cdf (P : Measure ℝ) [IsProbabilityMeasure P] : 
    StieltjesMeasureFunction where
  toFun := cdf P
  non_decreasing := (cdf P).mono'
  right_continuous x := (cdf P).right_continuous' x