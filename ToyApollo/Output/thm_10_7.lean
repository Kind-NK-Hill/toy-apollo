/-
TASK ID: thm_10_7
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter10-distribution-total-variation
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_10_2
import ToyApollo.Output.def_10_4

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology

theorem tendstoInMeasure_of_convergesInProbability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hProb : ConvergesInProbability μ Xn X) :
    TendstoInMeasure μ Xn atTop X := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hprob_half := hProb (ε / 2) hhalf
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hprob_half
    (fun _ => zero_le _) ?_
  intro n
  apply measure_mono
  intro ω hω
  have hnorm : ε ≤ |Xn n ω - X ω| := by
    simpa [Real.norm_eq_abs] using hω
  have hstrict : ε / 2 < |Xn n ω - X ω| := by linarith
  simpa [deviationEvent] using hstrict

theorem thm_10_7 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXn : ∀ n : ℕ, AEMeasurable (Xn n) μ)
    (hProb : ConvergesInProbability μ Xn X) :
    TendstoInDistribution Xn atTop X (fun _ : ℕ => μ) μ :=
  (tendstoInMeasure_of_convergesInProbability μ Xn X hProb).tendstoInDistribution hXn
