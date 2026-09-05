/-
TASK ID: thm_10_6
TYPE: Theorem_Statement
SOURCE PLAN: chapter10-distribution-total-variation
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_10.def_10_4
import ProbabilityTheory.chapter_10.def_10_5
import ProbabilityTheory.chapter_14.thm_14_4




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

noncomputable section



theorem thm_10_6_atom_zero_of_cdf_continuous
    (μ : ProbabilityMeasure ℝ) {x : ℝ}
    (hcont : ContinuousAt (fun y : ℝ => measureCdf μ y) x) :
    (μ : Measure ℝ) {x} = 0 :=
  measure_singleton_eq_zero_of_measureCdf_continuousAt μ hcont



theorem thm_10_6_weak_to_distribution_bridge
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ)
    (hWeak : def_14_1 Pseq P) :
    MeasuresConvergeInDistribution Pseq P := by
  exact (def_14_1_iff_tendsto).1 hWeak



theorem thm_10_6_weakConvergence
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ)
    (hTV :
      MeasuresConvergeInTotalVariation
        (fun n : ℕ => (Pseq n : Measure ℝ)) (P : Measure ℝ)) :
    def_14_1 Pseq P := by
  rw [MeasuresConvergeInTotalVariation] at hTV
  rcases hTV with ⟨hPn, hP, hlim⟩
  letI (n : ℕ) : IsProbabilityMeasure (Pseq n : Measure ℝ) := hPn n
  letI : IsProbabilityMeasure (P : Measure ℝ) := hP
  have hTV14 : thm_14_4_totalVariationConvergence Pseq P := by
    simpa [thm_14_4_totalVariationConvergence] using hlim
  exact thm_14_4 Pseq P hTV14



theorem thm_10_6
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ)
    (hTV :
      MeasuresConvergeInTotalVariation
        (fun n : ℕ => (Pseq n : Measure ℝ)) (P : Measure ℝ)) :
    MeasuresConvergeInDistribution Pseq P :=
  thm_10_6_weak_to_distribution_bridge Pseq P
    (thm_10_6_weakConvergence Pseq P hTV)
