import Mathlib
import ToyApollo.Output.prob_10_3
import ToyApollo.Output.thm_10_7
import ToyApollo.Output.thm_10_12
import ToyApollo.Output.def_10_4

/-
TASK ID: prob_10_10
TYPE: Problem
SOURCE PLAN: chapter10-problems
TASK CONTENT:
\textbf{10.10.} (Slutsky Theorem) Suppose $X_n\xrightarrow{D}X$ and $Y_n\xrightarrow{D}c$ for some constant $c$. Assume that $X_n$ and $Y_n$ are defined on the same probability space for each $n$. Prove:
\begin{enumerate}
\item $X_n+Y_n\xrightarrow{D}X+c$.
\item $X_nY_n\xrightarrow{D}cX$.
\end{enumerate}
Hint: Use Exercise 10.3 and proceed as in the proof of Theorem 10.7.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology

noncomputable section

/-- Additive Slutsky stability in Mathlib's weak-convergence interface. -/
theorem prob_10_10_add_distribution_stability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn Yn : ℕ → Ω → ℝ) (X : Ω → ℝ) (c : ℝ)
    (hX_dist : TendstoInDistribution Xn atTop X (fun _ : ℕ => μ) μ)
    (hY_prob : TendstoInMeasure μ Yn atTop (fun _ : Ω => c))
    (hY_meas : ∀ n : ℕ, AEMeasurable (Yn n) μ) :
    TendstoInDistribution (fun n ω => Xn n ω + Yn n ω) atTop
      (fun ω => X ω + c) (fun _ : ℕ => μ) μ :=
  hX_dist.add_of_tendstoInMeasure_const hY_prob hY_meas

/-- Multiplicative Slutsky stability in Mathlib's weak-convergence interface. -/
theorem prob_10_10_mul_distribution_stability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn Yn : ℕ → Ω → ℝ) (X : Ω → ℝ) (c : ℝ)
    (hX_dist : TendstoInDistribution Xn atTop X (fun _ : ℕ => μ) μ)
    (hY_prob : TendstoInMeasure μ Yn atTop (fun _ : Ω => c))
    (hY_meas : ∀ n : ℕ, AEMeasurable (Yn n) μ) :
    TendstoInDistribution (fun n ω => Xn n ω * Yn n ω) atTop
      (fun ω => c * X ω) (fun _ : ℕ => μ) μ := by
  have h :=
    hX_dist.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : ℝ × ℝ => p.1 * p.2) (by fun_prop) hY_prob hY_meas
  simpa [mul_comm] using h

/-- Problem 10.10, Slutsky's theorem in Mathlib's weak-convergence interface.
It converts the degenerate second limit to local probability convergence via
Problem 10.3 before applying Mathlib's Slutsky stability lemmas. -/
theorem prob_10_10_of_tendstoInDistribution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Xn Yn : ℕ → Ω → ℝ) (X : Ω → ℝ) (c : ℝ)
    (hX_dist : TendstoInDistribution Xn atTop X (fun _ : ℕ => μ) μ)
    (hY_dist :
      TendstoInDistribution Yn atTop (fun _ : Ω => c) (fun _ : ℕ => μ) μ) :
    TendstoInDistribution (fun n ω => Xn n ω + Yn n ω) atTop
        (fun ω => X ω + c) (fun _ : ℕ => μ) μ ∧
      TendstoInDistribution (fun n ω => Xn n ω * Yn n ω) atTop
        (fun ω => c * X ω) (fun _ : ℕ => μ) μ := by
  have h_const : μ {ω : Ω | (fun _ : Ω => c) ω = c} = 1 := by
    simp [IsProbabilityMeasure.measure_univ (μ := μ)]
  have hY_prob_local : ConvergesInProbability μ Yn (fun _ : Ω => c) :=
    prob_10_3_of_tendstoInDistribution μ Yn (fun _ : Ω => c) c
      (by fun_prop) hY_dist h_const
  have hY_prob : TendstoInMeasure μ Yn atTop (fun _ : Ω => c) :=
    tendstoInMeasure_of_convergesInProbability μ Yn (fun _ : Ω => c) hY_prob_local
  exact ⟨
    prob_10_10_add_distribution_stability μ Xn Yn X c hX_dist hY_prob
      hY_dist.forall_aemeasurable,
    prob_10_10_mul_distribution_stability μ Xn Yn X c hX_dist hY_prob
      hY_dist.forall_aemeasurable⟩

/-- Problem 10.10, Slutsky's theorem.  The statement uses Mathlib's
random-variable distribution-convergence interface, which carries the
measurability data implicit in the textbook phrase "random variables". -/
theorem prob_10_10 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Xn Yn : ℕ → Ω → ℝ) (X : Ω → ℝ) (c : ℝ)
    (hX_dist : TendstoInDistribution Xn atTop X (fun _ : ℕ => μ) μ)
    (hY_dist :
      TendstoInDistribution Yn atTop (fun _ : Ω => c) (fun _ : ℕ => μ) μ) :
    TendstoInDistribution (fun n ω => Xn n ω + Yn n ω) atTop
        (fun ω => X ω + c) (fun _ : ℕ => μ) μ ∧
      TendstoInDistribution (fun n ω => Xn n ω * Yn n ω) atTop
        (fun ω => c * X ω) (fun _ : ℕ => μ) μ :=
  prob_10_10_of_tendstoInDistribution μ Xn Yn X c hX_dist hY_dist
