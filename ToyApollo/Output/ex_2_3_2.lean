import Mathlib
import ToyApollo.Output.def_2_5

open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- The full sigma-field on `ℕ`, matching the power set in the textbook example. -/
abbrev discreteSigmaField : MeasurableSpace ℕ := ⊤

/-- The measure `P(E) = ∑_{i∈E} p_i` realized as a sum of weighted Dirac masses. -/
def weightedDiscreteMeasure (p : ℕ → ℝ) : @Measure ℕ discreteSigmaField := by
  letI : MeasurableSpace ℕ := discreteSigmaField
  exact Measure.sum (fun n : ℕ => ENNReal.ofReal (p n) • Measure.dirac n)

/-- On any event `E`, the weighted discrete measure is the expected restricted series. -/
theorem weightedDiscreteMeasure_apply (p : ℕ → ℝ) (E : Set ℕ) :
    weightedDiscreteMeasure p E = ∑' n : ℕ, E.indicator (fun n => ENNReal.ofReal (p n)) n := by
  letI : MeasurableSpace ℕ := discreteSigmaField
  have hE : MeasurableSet E := by simp [discreteSigmaField]
  rw [weightedDiscreteMeasure]
  simp [Measure.sum_apply, Measure.smul_apply, hE]
  refine tsum_congr ?_
  intro n
  by_cases hn : n ∈ E
  · simp [Set.indicator, hn]
  · simp [Set.indicator, hn]

/-- If the weights are nonnegative and sum to `1`, the whole-space mass is `1`. -/
theorem weightedDiscreteMeasure_univ (p : ℕ → ℝ) (hp_nonneg : ∀ n, 0 ≤ p n)
    (hp_sum : Summable p) (hp_norm : ∑' n, p n = 1) :
    weightedDiscreteMeasure p Set.univ = 1 := by
  rw [weightedDiscreteMeasure_apply]
  have htsum : ∑' n : ℕ, ENNReal.ofReal (p n) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hp_nonneg hp_sum, hp_norm, ENNReal.ofReal_one]
  simpa using htsum

/-- Exported declaration for Example 2.3.2. -/
def ex_2_3_2 (p : ℕ → ℝ) : @Measure ℕ discreteSigmaField :=
  weightedDiscreteMeasure p

/-- The weighted Dirac-series construction yields a probability measure when the source weights sum to `1`. -/
theorem ex_2_3_2_isProbabilityMeasure (p : ℕ → ℝ) (hp_nonneg : ∀ n, 0 ≤ p n)
    (hp_sum : Summable p) (hp_norm : ∑' n, p n = 1) :
    IsProbabilityMeasure (ex_2_3_2 p) := by
  letI : MeasurableSpace ℕ := discreteSigmaField
  exact ⟨by simpa [ex_2_3_2] using weightedDiscreteMeasure_univ p hp_nonneg hp_sum hp_norm⟩
