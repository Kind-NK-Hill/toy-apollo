import Mathlib

open MeasureTheory Filter Topology

/-!
TASK ID: prob_7_7
TYPE: Problem
SOURCE PLAN: 30_chap7_problems
TASK CONTENT:
\textbf{7.7.} Let $f_1,f_2,f_3,\dots$ be measurable functions defined on a measure space $(\Omega,\mathcal{F},\mu)$. Assume that $\sum_{k=1}^{\infty} \int |f_k|\, d\mu$ is finite.
\begin{enumerate}[label=(\alph*)]
    \item Show that $\sum_{k=1}^{\infty} f_k(\omega)$ converges to a finite limit $\mu$-almost everywhere.
    \item Use part (a) to derive the following result:
    \[
    \int \left(\sum_{k=1}^{\infty} f_k\right)\, d\mu
    =
    \sum_{k=1}^{\infty} \int f_k\, d\mu.
    \]
\end{enumerate}
-/

/-- Lean encoding of the textbook hypothesis `∑_k ∫ |f_k| dμ < ∞`. -/
def HasFiniteAbsIntegralSeries {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ℕ → Ω → ℝ) : Prop :=
  ∃ s : ENNReal, s ≠ ⊤ ∧ HasSum (fun k => ∫⁻ ω, ‖f k ω‖₊ ∂μ) s

theorem prob_7_7 {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : ℕ → Ω → ℝ)
    (hf : ∀ k, Measurable (f k)) (h : HasFiniteAbsIntegralSeries μ f) :
    (∀ᵐ ω ∂μ, ∃ L : ℝ, Tendsto (fun n ↦ ∑ k ∈ Finset.range n, f k ω) atTop (𝓝 L)) ∧
    ∫ ω, (∑' k, f k ω) ∂μ = ∑' k, ∫ ω, f k ω ∂μ := by
  rcases h with ⟨s, hs_top, hsum⟩
  have h : ∑' k, ∫⁻ ω, ‖f k ω‖₊ ∂μ ≠ ⊤ := by
    rw [hsum.tsum_eq]
    exact hs_top
  constructor
  · have h_summable : ∀ᵐ ω ∂μ, Summable (fun k => ‖f k ω‖₊) := by
      have h_summable : ∀ᵐ ω ∂μ, ∑' k, ‖f k ω‖ₑ < ⊤ := by
        convert ae_lt_top' _ _
        · fun_prop
        · rw [MeasureTheory.lintegral_tsum]
          · convert h using 1
          · exact fun k => (hf k |> Measurable.aemeasurable).enorm
      filter_upwards [h_summable] with ω hω
      convert ENNReal.summable_toNNReal_of_tsum_ne_top hω.ne using 1
    filter_upwards [h_summable] with ω hω
    exact
      ⟨_,
        Summable.hasSum
          (show Summable fun k => f k ω from
            .of_norm <| by simpa [← NNReal.summable_coe] using hω)
        |> HasSum.tendsto_sum_nat⟩
  · rw [MeasureTheory.integral_tsum]
    · exact fun k => (hf k |> Measurable.aestronglyMeasurable)
    · convert h using 1
