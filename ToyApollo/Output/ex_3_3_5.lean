/-
TASK ID: ex_3_3_5
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.ex_3_3_1
import ToyApollo.Output.ex_3_3_4
import Mathlib

open MeasureTheory Measure Set Function
open scoped ENNReal BigOperators

noncomputable def discrete_distribution (p : ℕ → ℝ≥0∞) (x : ℕ → ℝ) : Measure ℝ :=
  Measure.sum fun j => p j • Measure.dirac (x j)

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

theorem discrete_distribution_univ (p : ℕ → ℝ≥0∞) (x : ℕ → ℝ)
    (h_norm : ∑' j, p j = 1) :
    discrete_distribution p x univ = 1 := by
  rw [discrete_distribution, Measure.sum_apply _ MeasurableSet.univ]
  simp [h_norm]

theorem discrete_distribution_range_eq_one (p : ℕ → ℝ≥0∞) (x : ℕ → ℝ)
    (h_norm : ∑' j, p j = 1) :
    discrete_distribution p x (Set.range x) = 1 := by
  have hs : MeasurableSet (Set.range x) := (Set.countable_range x).measurableSet
  rw [discrete_distribution, Measure.sum_apply _ hs]
  simp [h_norm]

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

theorem lebesgue_measure_range_eq_zero (x : ℕ → ℝ) :
    volume (Set.range x) = 0 := by
  exact (Set.countable_range x).measure_zero volume

instance discrete_distribution_isProbabilityMeasure
    {p : ℕ → ℝ≥0∞} {x : ℕ → ℝ} [Fact (∑' j, p j = 1)] :
    IsProbabilityMeasure (discrete_distribution p x) :=
  ⟨discrete_distribution_univ p x (Fact.out)⟩

noncomputable def discrete_distribution_stieltjes (p : ℕ → ℝ≥0∞) (x : ℕ → ℝ)
    (h_norm : ∑' j, p j = 1) : StieltjesFunction ℝ :=
  haveI : Fact (∑' j, p j = 1) := ⟨h_norm⟩
  ProbabilityTheory.cdf (discrete_distribution p x)

theorem discrete_distribution_stieltjes_measure (p : ℕ → ℝ≥0∞) (x : ℕ → ℝ)
    (h_norm : ∑' j, p j = 1) :
    (discrete_distribution_stieltjes p x h_norm).measure = discrete_distribution p x := by
  haveI : Fact (∑' j, p j = 1) := ⟨h_norm⟩
  exact ProbabilityTheory.measure_cdf (discrete_distribution p x)

theorem discrete_distribution_stieltjes_jump (p : ℕ → ℝ≥0∞) (x : ℕ → ℝ)
    (h_norm : ∑' j, p j = 1) (h_inj : Function.Injective x) (i : ℕ) :
    (discrete_distribution_stieltjes p x h_norm).measure ({x i} : Set ℝ) = p i := by
  rw [discrete_distribution_stieltjes_measure]
  exact measure_at_singleton_eq_p h_inj i

theorem discrete_distribution_stieltjes_flat (p : ℕ → ℝ≥0∞) (x : ℕ → ℝ)
    (h_norm : ∑' j, p j = 1) {y : ℝ} (hy : y ∉ Set.range x) :
    (discrete_distribution_stieltjes p x h_norm).measure ({y} : Set ℝ) = 0 := by
  rw [discrete_distribution_stieltjes_measure]
  exact measure_at_singleton_eq_zero hy

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
