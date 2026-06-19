/-
TASK ID: prob_13_10
TYPE: Problem
SOURCE PLAN: chapter13-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.prob_13_10_centered_wald_support

open MeasureTheory Filter
open scoped BigOperators ProbabilityTheory Topology

noncomputable section

theorem prob_13_10
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] :
    (∀ (X : ℕ → Ω → ℝ) (T : Ω → ℕ) (μ : ℝ),
      Measurable T →
      Integrable (fun ω => (T ω : ℝ)) P →
      Integrable (X 1) P →
      (∫ ω, X 1 ω ∂P = μ) →
      (∀ k : ℕ, ProbabilityTheory.IdentDistrib (X k) (X 1) P P) →
      ProbabilityTheory.IndepFun T (fun ω => fun n : ℕ => X n ω) P →
      prob_13_10_waldIdentity
        (∫ ω, prob_13_10_stoppedSum X T ω ∂P)
        μ
        (∫ ω, (T ω : ℝ) ∂P)) ∧
    (∀ (𝓕n : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ)
        (T : Ω → ℕ) (c : ℝ) (hM : def_13_7 P 𝓕n X),
      def_13_8 𝓕n (fun ω => (T ω : WithTop ℕ)) →
      (∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n))) →
      prob_13_10_relaxed_conditional_increment_bound P 𝓕n X c →
      Integrable (fun ω => (T ω : ℝ)) P →
      ∫ ω, thm_13_18_stoppedValueReal X
          (fun ω => (T ω : WithTop ℕ)) ω ∂P =
        ∫ ω, X 0 ω ∂P) ∧
    (∀ (X : ℕ → Ω → ℝ) (T : Ω → ℕ) (μ : ℝ),
      (∀ k : ℕ, StronglyMeasurable (X k)) →
      Integrable (X 1) P →
      (∫ ω, X 1 ω ∂P = μ) →
      prob_13_10_iid_sequence P X →
      def_13_8
        (prob_13_10_oneIndexedNaturalFiltration
          (prob_13_10_centeredIncrements X μ))
        (fun ω => (T ω : WithTop ℕ)) →
      Integrable (fun ω => (T ω : ℝ)) P →
      prob_13_10_waldIdentity
        (∫ ω, prob_13_10_stoppedSum X T ω ∂P)
        μ
        (∫ ω, (T ω : ℝ) ∂P)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X T μ hTMeas hTIntegrable hX1Integrable hMeanOne hIdent hSeqInd
    exact prob_13_10_independent_count_wald_source
      (P := P) (X := X) (T := T) (μ := μ)
      hTMeas hTIntegrable hX1Integrable hMeanOne hIdent hSeqInd
  · intro 𝓕n X T c hM hT hSigmaFinite hBound hTIntegrable
    exact prob_13_10_relaxed_increment_optional_stopping
      (P := P) (𝓕n := 𝓕n) (X := X) (T := T) (c := c)
      hM hT hSigmaFinite hBound hTIntegrable
  · intro X T μ hXStrong hX1Integrable hMeanOne hIID hT hTIntegrable
    exact prob_13_10_stopping_time_wald
      (P := P) (X := X) (T := T) (μ := μ)
      hXStrong hX1Integrable hMeanOne hIID hT hTIntegrable
