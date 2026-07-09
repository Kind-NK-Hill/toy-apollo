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

/-- Off-support singleton mass is zero: the second case of the source's displayed
formula `P({x}) = p_i` if `x = x_i`, `0` otherwise.  Together with
`measure_at_singleton_eq_p` this lands the full source case distinction. -/
theorem measure_at_singleton_eq_zero {p : ℕ → ℝ≥0∞} {x : ℕ → ℝ} {y : ℝ}
    (hy : y ∉ Set.range x) :
    discrete_distribution p x ({y} : Set ℝ) = 0 := by
  classical
  have hs : MeasurableSet ({y} : Set ℝ) := measurableSet_singleton y
  rw [discrete_distribution, Measure.sum_apply _ hs]
  have hz : ∀ j, (p j • Measure.dirac (x j)) ({y} : Set ℝ) = 0 := by
    intro j
    have hxj : (x j) ∉ ({y} : Set ℝ) := fun h => hy ⟨j, h⟩
    rw [Measure.smul_apply, Measure.dirac_apply' _ hs, Set.indicator_of_notMem hxj, smul_zero]
  simp [hz]

/-- The countable support of the discrete distribution has Lebesgue measure zero. -/
theorem lebesgue_measure_range_eq_zero (x : ℕ → ℝ) :
    volume (Set.range x) = 0 := by
  exact (Set.countable_range x).measure_zero volume

/-- If the masses sum to `1`, the discrete distribution is a probability measure. -/
instance discrete_distribution_isProbabilityMeasure
    {p : ℕ → ℝ≥0∞} {x : ℕ → ℝ} [Fact (∑' j, p j = 1)] :
    IsProbabilityMeasure (discrete_distribution p x) :=
  ⟨discrete_distribution_univ p x (Fact.out)⟩

/-! ### Source Stieltjes construction

The source Example 3.3.5 does not construct the measure directly: it "defines a
Stieltjes measure function `F` that is flat except at the points `x_i`, with a
vertical jump of size `p_i` at `x_i`", and then lets `P` be the Lebesgue–Stieltjes
measure associated with `F`.  For the discrete distribution `P`, that Stieltjes
measure function is exactly its cumulative distribution function `F(t) = P((-∞,t])`,
and the source's "`P` is the Lebesgue–Stieltjes measure of `F`" is the identity
`F.measure = P`.  The declarations below land that construction, prove the
source's jump structure both at the measure level (`F.measure {x_i} = p_i`,
`F.measure {y} = 0` off support) and at the function level (`F` jumps by `p_i`
at `x_i` and has no jump off support). -/

/-- The source Stieltjes measure function `F` of the discrete distribution: its
cumulative distribution function, monotone and right-continuous with a jump of size
`p_i` at each `x_i`. -/
noncomputable def discrete_distribution_stieltjes (p : ℕ → ℝ≥0∞) (x : ℕ → ℝ)
    (h_norm : ∑' j, p j = 1) : StieltjesFunction ℝ :=
  haveI : Fact (∑' j, p j = 1) := ⟨h_norm⟩
  ProbabilityTheory.cdf (discrete_distribution p x)

/-- Source construction step: the Lebesgue–Stieltjes measure associated with the
Stieltjes function `F` is exactly the discrete distribution `P`. -/
theorem discrete_distribution_stieltjes_measure (p : ℕ → ℝ≥0∞) (x : ℕ → ℝ)
    (h_norm : ∑' j, p j = 1) :
    (discrete_distribution_stieltjes p x h_norm).measure = discrete_distribution p x := by
  haveI : Fact (∑' j, p j = 1) := ⟨h_norm⟩
  exact ProbabilityTheory.measure_cdf (discrete_distribution p x)

/-- Source jump structure: `F` has a vertical jump of size `p_i` at each support
point `x_i`, i.e. the Lebesgue–Stieltjes measure of the singleton `{x_i}` is `p_i`. -/
theorem discrete_distribution_stieltjes_jump (p : ℕ → ℝ≥0∞) (x : ℕ → ℝ)
    (h_norm : ∑' j, p j = 1) (h_inj : Function.Injective x) (i : ℕ) :
    (discrete_distribution_stieltjes p x h_norm).measure ({x i} : Set ℝ) = p i := by
  rw [discrete_distribution_stieltjes_measure]
  exact measure_at_singleton_eq_p h_inj i

/-- Source jump structure, off-support case: `F` is flat at points that are not
support points, so its Lebesgue–Stieltjes measure of `{y}` is `0` for `y` outside
the support. -/
theorem discrete_distribution_stieltjes_flat (p : ℕ → ℝ≥0∞) (x : ℕ → ℝ)
    (h_norm : ∑' j, p j = 1) {y : ℝ} (hy : y ∉ Set.range x) :
    (discrete_distribution_stieltjes p x h_norm).measure ({y} : Set ℝ) = 0 := by
  rw [discrete_distribution_stieltjes_measure]
  exact measure_at_singleton_eq_zero hy

/-- Function-level jump structure, literal source phrasing: `F` has "a vertical
jump of size `p_i` at `x_i`" — the gap between `F (x i)` and its left limit is
exactly `(p i).toReal`.  Follows from the singleton mass `p_i` via
`StieltjesFunction.measure_singleton`. -/
theorem discrete_distribution_stieltjes_jump_size (p : ℕ → ℝ≥0∞) (x : ℕ → ℝ)
    (h_norm : ∑' j, p j = 1) (h_inj : Function.Injective x) (i : ℕ) :
    discrete_distribution_stieltjes p x h_norm (x i)
      - leftLim (discrete_distribution_stieltjes p x h_norm) (x i) = (p i).toReal := by
  have hm := (discrete_distribution_stieltjes p x h_norm).measure_singleton (x i)
  rw [discrete_distribution_stieltjes_jump p x h_norm h_inj i] at hm
  have h0 : 0 ≤ discrete_distribution_stieltjes p x h_norm (x i)
      - leftLim (discrete_distribution_stieltjes p x h_norm) (x i) :=
    sub_nonneg.2 ((discrete_distribution_stieltjes p x h_norm).mono.leftLim_le le_rfl)
  rw [hm, ENNReal.toReal_ofReal h0]

/-- Function-level flatness, literal source phrasing: `F` is "flat except at the
points `x_i`" — at any `y` outside the support `F` has no jump, its left limit
equals its value. -/
theorem discrete_distribution_stieltjes_flat_eq (p : ℕ → ℝ≥0∞) (x : ℕ → ℝ)
    (h_norm : ∑' j, p j = 1) {y : ℝ} (hy : y ∉ Set.range x) :
    leftLim (discrete_distribution_stieltjes p x h_norm) y
      = discrete_distribution_stieltjes p x h_norm y := by
  have hm := (discrete_distribution_stieltjes p x h_norm).measure_singleton y
  rw [discrete_distribution_stieltjes_flat p x h_norm hy] at hm
  have hle : discrete_distribution_stieltjes p x h_norm y
      - leftLim (discrete_distribution_stieltjes p x h_norm) y ≤ 0 :=
    ENNReal.ofReal_eq_zero.1 hm.symm
  have h0 : 0 ≤ discrete_distribution_stieltjes p x h_norm y
      - leftLim (discrete_distribution_stieltjes p x h_norm) y :=
    sub_nonneg.2 ((discrete_distribution_stieltjes p x h_norm).mono.leftLim_le le_rfl)
  linarith

/--
Example 3.3.5 (full source statement).  With distinct support points `x_i` and
masses summing to `1`, the discrete distribution `P` is the Lebesgue–Stieltjes
measure of a Stieltjes function `F` (its CDF) that jumps by `p_i` at each `x_i`
and is flat elsewhere; the singleton masses are `P({x_i}) = p_i` on support and
`P({y}) = 0` off support; `P` is concentrated on the countable support
`A = {x_1, x_2, …}` with `P(A) = 1`, while `A` has Lebesgue measure `0`.
-/
theorem ex_3_3_5 (p : ℕ → ℝ≥0∞) (x : ℕ → ℝ)
    (h_inj : Function.Injective x) (h_norm : ∑' j, p j = 1) :
    (discrete_distribution_stieltjes p x h_norm).measure = discrete_distribution p x ∧
      (∀ i, discrete_distribution p x ({x i} : Set ℝ) = p i) ∧
      (∀ y ∉ Set.range x, discrete_distribution p x ({y} : Set ℝ) = 0) ∧
      discrete_distribution p x (Set.range x) = 1 ∧
      volume (Set.range x) = 0 :=
  ⟨discrete_distribution_stieltjes_measure p x h_norm,
    fun i => measure_at_singleton_eq_p h_inj i,
    fun _ hy => measure_at_singleton_eq_zero hy,
    discrete_distribution_range_eq_one p x h_norm,
    lebesgue_measure_range_eq_zero x⟩
