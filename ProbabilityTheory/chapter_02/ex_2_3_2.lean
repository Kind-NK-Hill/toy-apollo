/-
TASK ID: ex_2_3_2
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_02.def_2_5

open MeasureTheory Set
open scoped BigOperators

noncomputable section

 
abbrev discreteSigmaField : MeasurableSpace ℕ := ⊤

 
def weightedDiscreteMeasure (p : ℕ → ℝ) : @Measure ℕ discreteSigmaField := by
  letI : MeasurableSpace ℕ := discreteSigmaField
  exact Measure.sum (fun n : ℕ => ENNReal.ofReal (p n) • Measure.dirac n)

 
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

 
theorem weightedDiscreteMeasure_univ (p : ℕ → ℝ) (hp_nonneg : ∀ n, 0 ≤ p n)
    (hp_sum : Summable p) (hp_norm : ∑' n, p n = 1) :
    weightedDiscreteMeasure p Set.univ = 1 := by
  rw [weightedDiscreteMeasure_apply]
  have htsum : ∑' n : ℕ, ENNReal.ofReal (p n) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hp_nonneg hp_sum, hp_norm, ENNReal.ofReal_one]
  simpa using htsum

 
def ex_2_3_2 (p : ℕ → ℝ) : @Measure ℕ discreteSigmaField :=
  weightedDiscreteMeasure p

 
theorem ex_2_3_2_isProbabilityMeasure (p : ℕ → ℝ) (hp_nonneg : ∀ n, 0 ≤ p n)
    (hp_sum : Summable p) (hp_norm : ∑' n, p n = 1) :
    IsProbabilityMeasure (ex_2_3_2 p) := by
  letI : MeasurableSpace ℕ := discreteSigmaField
  exact ⟨by simpa [ex_2_3_2] using weightedDiscreteMeasure_univ p hp_nonneg hp_sum hp_norm⟩
