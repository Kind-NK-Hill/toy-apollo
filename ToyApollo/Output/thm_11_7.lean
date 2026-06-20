/-
TASK ID: thm_11_7
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter11-strong-law-large-numbers
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.thm_11_7_support

-- WRITE FINAL LEAN CODE BELOW

open Filter
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal Topology

noncomputable section

private theorem thm_11_7_from_tailSummability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (μ : ℝ)
    (hTail : thm_11_7_tailSummabilitySupport P X μ) :
    ConvergesAlmostSurely P (fun n => thm_11_5_sampleMean X n) (fun _ => μ) := by
  refine (thm_10_1 P (fun n => thm_11_5_sampleMean X n) (fun _ : Ω => μ)).2 ?_
  intro ε hε
  have hsum := hTail ε hε
  simpa [deviationInfinitelyOften] using
    (thm_5_8 P
      (fun n : ℕ =>
        almostSureDeviationEvent
          (fun n => thm_11_5_sampleMean X n) (fun _ : Ω => μ) n ε)
      hsum)

theorem thm_11_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (μ : ℝ)
    (hInd : def_5_10_randomVariables P X)
    (hMean : ∀ i : ℕ, P[X i] = μ)
    (hFourth : ∃ c : ℝ, thm_11_7_fourthMomentUniformBound P X μ c) :
    ConvergesAlmostSurely P (fun n => thm_11_5_sampleMean X n) (fun _ => μ) :=
  thm_11_7_from_tailSummability P X μ
    (thm_11_7_tail_summability_from_fourth_moment P X μ hInd hMean hFourth)
