/-
TASK ID: thm_10_6
TYPE: Theorem_Statement
SOURCE PLAN: chapter10-distribution-total-variation
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_10_4
import ToyApollo.Output.def_10_5
import ToyApollo.Output.thm_14_4

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

noncomputable section

theorem thm_10_6_atom_zero_of_cdf_continuous
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {x : ℝ}
    (hcont : ContinuousAt (fun y : ℝ => measureCdf μ y) x) :
    μ {x} = 0 := by
  have hcont_cdf : ContinuousAt (fun y : ℝ => cdf μ y) x := by
    simpa [measureCdf, cdf_eq_real] using hcont
  have hleft : Function.leftLim (fun y : ℝ => cdf μ y) x = cdf μ x := by
    exact hcont_cdf.continuousWithinAt.leftLim_eq
  rw [← measure_cdf μ, StieltjesFunction.measure_singleton]
  simp [hleft]

theorem thm_10_6_weak_to_distribution_bridge
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ)
    (hWeak : def_14_1 Pseq P) :
    MeasuresConvergeInDistribution
      (fun n : ℕ => (Pseq n : Measure ℝ)) (P : Measure ℝ) := by
  have hTend : Tendsto Pseq atTop (𝓝 P) := (def_14_1_iff_tendsto).1 hWeak
  intro x hxcont
  have hAtom : (P : Measure ℝ) {x} = 0 :=
    thm_10_6_atom_zero_of_cdf_continuous (P : Measure ℝ) hxcont
  have hFrontier : (P : Measure ℝ) (frontier (Iic x)) = 0 := by
    simpa [frontier_Iic] using hAtom
  have hENN :
      Tendsto
        (fun n : ℕ => ((Pseq n : ProbabilityMeasure ℝ) : Measure ℝ) (Iic x))
        atTop (𝓝 (((P : ProbabilityMeasure ℝ) : Measure ℝ) (Iic x))) :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hTend hFrontier
  have hReal :
      Tendsto
        (fun n : ℕ =>
          (((Pseq n : ProbabilityMeasure ℝ) : Measure ℝ) (Iic x)).toReal)
        atTop
        (𝓝 ((((P : ProbabilityMeasure ℝ) : Measure ℝ) (Iic x)).toReal)) :=
    (ENNReal.tendsto_toReal
      (measure_ne_top (((P : ProbabilityMeasure ℝ) : Measure ℝ)) (Iic x))).comp hENN
  simpa [MeasuresConvergeInDistribution, CdfConvergesInDistribution,
    measureCdf, measureReal_def] using hReal

theorem thm_10_6_weakConvergence
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ)
    (hTV :
      MeasuresConvergeInTotalVariation
        (fun n : ℕ => (Pseq n : Measure ℝ)) (P : Measure ℝ)) :
    def_14_1 Pseq P := by
  have hTV14 : thm_14_4_totalVariationConvergence Pseq P := by
    simpa [MeasuresConvergeInTotalVariation, thm_14_4_totalVariationConvergence]
      using hTV.2.2
  exact thm_14_4 Pseq P hTV14

theorem thm_10_6
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ)
    (hTV :
      MeasuresConvergeInTotalVariation
        (fun n : ℕ => (Pseq n : Measure ℝ)) (P : Measure ℝ)) :
    MeasuresConvergeInDistribution
      (fun n : ℕ => (Pseq n : Measure ℝ)) (P : Measure ℝ) :=
  thm_10_6_weak_to_distribution_bridge Pseq P
    (thm_10_6_weakConvergence Pseq P hTV)
