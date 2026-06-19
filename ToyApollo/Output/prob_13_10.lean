import ToyApollo.Output.prob_13_10_centered_wald_support

/-
TASK ID: prob_13_10
TYPE: Problem
SOURCE PLAN: chapter13-problems
TASK CONTENT:
\textbf{13.10.} Let X n's be iid. random variables with finite mean \mu = E[X1]:

(a) Let T be an integer-valued random variable independent of (X n)n\geq1, and

assume T has finite expectation. Prove Wald's identity

E[X1 +X 2 +\cdot\cdot\cdot+ XT ]= \mu\cdot E [T] .

(b) Prove that Condition (iii) in Theorem 13.18 can be relaxed to E [T] < \infty and

E[\vertXn -X n- 1\vert\vert \mathcal{F}n]\leq c for all n .

(c) Let T be a stopping time for the filtration \mathcal{F}n \coloneqq\sigma(X 1,...,X n),f o r n \geq 1.

Apply part (b) to prove that Wald's identity holds if E [\vertX1\vert] < \infty and E [T] <

\infty .
-/

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
