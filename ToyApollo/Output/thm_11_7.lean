/-
TASK ID: thm_11_7
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter11-strong-law-large-numbers
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_5_10
import ToyApollo.Output.def_9_1
import ToyApollo.Output.thm_5_8
import ToyApollo.Output.thm_10_1
import ToyApollo.Output.thm_11_1
import ToyApollo.Output.thm_11_5

-- WRITE FINAL LEAN CODE BELOW

open Filter
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal Topology

noncomputable section

def thm_11_7_fourthMomentUniformBound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (μ c : ℝ) : Prop :=
  0 ≤ c ∧ ∀ i : ℕ, rthMoment P (fun ω => X i ω - μ) 4 ≤ c

noncomputable def thm_11_7_centeredPartialSum {Ω : Type*} (X : ℕ → Ω → ℝ)
    (μ : ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ i : Fin (n + 1), X i.1 ω - μ

def thm_11_7_fourthMomentPartialSumBound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (μ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ n : ℕ,
      Integrable (fun ω => (thm_11_7_centeredPartialSum X μ n ω) ^ 4) P ∧
      (∫ ω, (thm_11_7_centeredPartialSum X μ n ω) ^ 4 ∂P) ≤
        C * ((n : ℝ) + 1) ^ 2

def thm_11_7_tailSummabilitySupport {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (μ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (∑' n : ℕ,
      P (almostSureDeviationEvent
        (fun n => thm_11_5_sampleMean X n) (fun _ : Ω => μ) n ε)) ≠ ∞

private theorem thm_11_7_from_tailSummability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (μ : ℝ)
    (h_tail_summability : thm_11_7_tailSummabilitySupport P X μ) :
    ConvergesAlmostSurely P (fun n => thm_11_5_sampleMean X n) (fun _ => μ) := by
  refine (thm_10_1 P (fun n => thm_11_5_sampleMean X n) (fun _ : Ω => μ)).2 ?_
  intro ε hε
  have hsum := h_tail_summability ε hε
  simpa [deviationInfinitelyOften] using
    (thm_5_8 P
      (fun n : ℕ =>
        almostSureDeviationEvent
          (fun n => thm_11_5_sampleMean X n) (fun _ : Ω => μ) n ε)
      hsum)

theorem thm_11_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (μ : ℝ)
    (_hindep : def_5_10_randomVariables P X)
    (_hmean : ∀ i : ℕ, P[X i] = μ)
    (_hfourth : ∃ c : ℝ, thm_11_7_fourthMomentUniformBound P X μ c)
    (h_tail_summability :
      ∀ ε : ℝ, 0 < ε →
        (∑' n : ℕ,
          P (almostSureDeviationEvent
            (fun n => thm_11_5_sampleMean X n) (fun _ : Ω => μ) n ε)) ≠ ∞) :
    ConvergesAlmostSurely P (fun n => thm_11_5_sampleMean X n) (fun _ => μ) :=
  thm_11_7_from_tailSummability P X μ h_tail_summability
