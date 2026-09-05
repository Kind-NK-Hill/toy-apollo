/-
TASK ID: prob_10_4
TYPE: Problem
SOURCE PLAN: chapter10-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_10.def_10_2
import ProbabilityTheory.chapter_10.thm_10_12




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology



theorem prob_10_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (Xn : ℕ → Ω → ℝ) (a : ℕ → ℝ) (c : ℝ)
    (hcenter :
      ConvergesInProbability μ (fun n ω => Xn n ω - a n) (fun _ => 0))
    (ha : Tendsto a atTop (nhds c)) :
    ConvergesInProbability μ Xn (fun _ => c) := by
  have hXn : ∀ n : ℕ, Measurable (Xn n) := by
    intro n
    simpa only [sub_add_cancel] using
      (hcenter.1 n).add
        (show Measurable (fun _ : Ω => a n) from measurable_const)
  refine ⟨hXn, measurable_const, ?_⟩
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hcenter_half := hcenter.2.2 (ε / 2) hhalf
  have ha_small : ∀ᶠ n : ℕ in atTop, |a n - c| < ε / 2 := by
    have hball := ha.eventually (Metric.ball_mem_nhds c hhalf)
    filter_upwards [hball] with n hn
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hn
  have hle :
      ∀ᶠ n : ℕ in atTop,
        μ (deviationEvent Xn (fun _ => c) n ε)
          ≤ μ (deviationEvent (fun n ω => Xn n ω - a n) (fun _ => 0) n (ε / 2)) := by
    filter_upwards [ha_small] with n hn
    apply measure_mono
    intro ω hω
    by_contra hnot
    have hcenter_le : |(Xn n ω - a n) - 0| ≤ ε / 2 := le_of_not_gt hnot
    have htri : |Xn n ω - c| ≤ |(Xn n ω - a n) - 0| + |a n - c| := by
      calc
        |Xn n ω - c| = |((Xn n ω - a n) - 0) + (a n - c)| := by ring_nf
        _ ≤ |(Xn n ω - a n) - 0| + |a n - c| := abs_add_le _ _
    have hleε : |Xn n ω - c| ≤ ε := by
      linarith
    exact not_le_of_gt hω hleε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hcenter_half
    (Filter.Eventually.of_forall fun _ => zero_le)
    hle
