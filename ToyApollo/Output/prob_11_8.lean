/-
TASK ID: prob_11_8
TYPE: Problem
SOURCE PLAN: chapter11-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_5_10
import ToyApollo.Output.thm_11_2
import ToyApollo.Output.prob_11_7

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory

def prob_11_8_ar1Assumptions {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X N : ℕ → Ω → ℝ) (ρ σ2 : ℝ) : Prop :=
  (∀ ω : Ω, X 0 ω = 0) ∧
    |ρ| < 1 ∧
    0 ≤ σ2 ∧
    (∀ i : ℕ, X (i + 1) = fun ω => ρ * X i ω + N (i + 1) ω) ∧
    (∀ i : ℕ, P[N i] = 0) ∧
    (∀ i : ℕ, _root_.variance P (N i) = σ2) ∧
    def_5_10_randomVariables P N

private axiom prob_11_8_covarianceDecaySupport_internal {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X N : ℕ → Ω → ℝ) (ρ σ2 : ℝ)
    (_hAR : prob_11_8_ar1Assumptions P X N ρ σ2) :
    ∃ K : ℝ, ∃ a : ℕ → ℝ, prob_11_7_covarianceDecayAssumptions P X 0 K a

theorem prob_11_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X N : ℕ → Ω → ℝ) (ρ σ2 : ℝ)
    (hAR : prob_11_8_ar1Assumptions P X N ρ σ2) :
    ConvergesInProbability P (fun n => thm_11_5_sampleMean X n) (fun _ => 0) := by
  rcases prob_11_8_covarianceDecaySupport_internal P X N ρ σ2 hAR with
    ⟨K, a, hDecay⟩
  exact prob_11_7 P X 0 K a hDecay
