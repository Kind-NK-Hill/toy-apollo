import ToyApollo.Output.ex_3_3_1
import ToyApollo.Output.ex_3_3_4
import Mathlib

open MeasureTheory Measure Set Function
open scoped ENNReal BigOperators

/-- The discrete distribution with masses `p i` concentrated at the points `x i`. -/
noncomputable def discrete_distribution (p : ℕ → ℝ≥0∞) (x : ℕ → ℝ) : Measure ℝ :=
  Measure.sum fun j => p j • Measure.dirac (x j)

/-- The weighted Dirac sum assigns the expected mass to each support point. -/
theorem measure_at_singleton_eq_p {p : ℕ → ℝ≥0∞} {x : ℕ → ℝ}
    (h_inj : Injective x) (i : ℕ) :
    discrete_distribution p x ({x i} : Set ℝ) = p i := by
  classical
  have hs : MeasurableSet ({x i} : Set ℝ) := measurableSet_singleton (x i)
  rw [discrete_distribution, Measure.sum_apply _ hs, tsum_eq_single i]
  · simp
  · intro j hj
    have hx_ne : x j ∉ ({x i} : Set ℝ) := by
      simp [h_inj.ne hj]
    simp [hx_ne]

/-- If the masses sum to `1`, the discrete distribution is a probability measure. -/
theorem discrete_distribution_univ (p : ℕ → ℝ≥0∞) (x : ℕ → ℝ)
    (h_norm : ∑' j, p j = 1) :
    discrete_distribution p x univ = 1 := by
  rw [discrete_distribution, Measure.sum_apply _ MeasurableSet.univ]
  simp [h_norm]

/-- All of the mass is concentrated on the countable support `range x`. -/
theorem discrete_distribution_range_eq_one (p : ℕ → ℝ≥0∞) (x : ℕ → ℝ)
    (h_norm : ∑' j, p j = 1) :
    discrete_distribution p x (Set.range x) = 1 := by
  have hs : MeasurableSet (Set.range x) := (Set.countable_range x).measurableSet
  rw [discrete_distribution, Measure.sum_apply _ hs]
  simp [h_norm]

/-- The countable support of the discrete distribution has Lebesgue measure zero. -/
theorem lebesgue_measure_range_eq_zero (x : ℕ → ℝ) :
    volume (Set.range x) = 0 := by
  exact (Set.countable_range x).measure_zero volume

/--
Example 3.3.5: the discrete distribution is a probability measure concentrated on the support
`{x_1, x_2, x_3, ...}`.
-/
theorem ex_3_3_5 (p : ℕ → ℝ≥0∞) (x : ℕ → ℝ) (h_norm : ∑' j, p j = 1) :
    discrete_distribution p x (Set.range x) = 1 :=
  discrete_distribution_range_eq_one p x h_norm
