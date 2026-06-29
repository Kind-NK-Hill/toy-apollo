import Mathlib

/-
TASK ID: thm_10_3
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter10-almost-sure-probability
TASK CONTENT:
\begin{thmbox}{10.3 (Markov Inequality)}
If $X$ is a nonnegative random variable with finite expectation, then for any $\epsilon>0$, we have
\[
P(X\geq \epsilon)\leq \frac{\mathbb{E}[X]}{\epsilon}.
\]
\end{thmbox}

\textit{Proof}
The indicator function $\mathbf{1}_{[\epsilon,\infty)}(x)$ is less than or equal to the linear function $g(x)=x/\epsilon$ for all $x\geq 0$. By the monotonic property of integral, we obtain
\[
P(X\geq \epsilon)=\mathbb{E}[\mathbf{1}_{[\epsilon,\infty)}(X)]
\leq \mathbb{E}[X/\epsilon].
\]
By linearity of expectation, we obtain $\mathbb{E}[X/\epsilon]=\mathbb{E}[X]/\epsilon$, and thus proving the Markov inequality.
\hfill $\square$
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

/-- Markov inequality for a nonnegative integrable real-valued random variable. -/
theorem thm_10_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ)
    (h_nonneg : 0 ≤ᵐ[P] X) (h_int : Integrable X P) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω : Ω | ε ≤ X ω} ≤ (∫ ω, X ω ∂P) / ε := by
  have hmul := MeasureTheory.mul_meas_ge_le_integral_of_nonneg h_nonneg h_int ε
  rw [le_div_iff₀ hε]
  simpa [mul_comm] using hmul
