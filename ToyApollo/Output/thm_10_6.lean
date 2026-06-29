import Mathlib
import ToyApollo.Output.def_10_4
import ToyApollo.Output.def_10_5
import ToyApollo.Output.thm_14_4

/-
TASK ID: thm_10_6
TYPE: Theorem_Statement
SOURCE PLAN: chapter10-distribution-total-variation
TASK CONTENT:
\begin{thmbox}{10.6}
If a sequence of probability distributions converges in total variation, then it converges in distribution.
\end{thmbox}

We defer the proof to Chap. 14 after the introduction to weak convergence (see Theorem 14.4).
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

noncomputable section

/-- At a continuity point of a real cdf, the corresponding law has no atom.
This is the cdf-side form of the source phrase `P({a}) = 0`, restated here
because this pack's declared Chapter 14 dependency is Theorem 14.4. -/
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

/-- The Chapter 14 weak-convergence-to-cdf bridge, specialized to probability
measures on `ℝ`. -/
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

/-- The deferred Theorem 14.4 step: total variation convergence of probability
measures implies weak convergence. -/
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

/-- Theorem 10.6: if a sequence of probability distributions converges in
total variation, then it converges in distribution.  The proof is the exact
deferred route named in the textbook: Theorem 14.4 gives weak convergence, and
the Chapter 14 weak/distribution bridge translates that conclusion back to the
Chapter 10 cdf definition. -/
theorem thm_10_6
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ)
    (hTV :
      MeasuresConvergeInTotalVariation
        (fun n : ℕ => (Pseq n : Measure ℝ)) (P : Measure ℝ)) :
    MeasuresConvergeInDistribution
      (fun n : ℕ => (Pseq n : Measure ℝ)) (P : Measure ℝ) :=
  thm_10_6_weak_to_distribution_bridge Pseq P
    (thm_10_6_weakConvergence Pseq P hTV)
