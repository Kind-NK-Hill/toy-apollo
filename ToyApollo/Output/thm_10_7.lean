import Mathlib
import ToyApollo.Output.def_10_2
import ToyApollo.Output.def_10_4

/-
TASK ID: thm_10_7
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter10-distribution-total-variation
TASK CONTENT:
\begin{thmbox}{10.7}
Suppose $X_n$, for $n\geq 1$, is a sequence of random variables converging to $X$ in probability. Then $X_n$ converges to $X$ in distribution.
\end{thmbox}

\textit{Proof}
Let $F_n(x)$ be the cumulative distribution function of $X_n$, for $n\geq 1$, and let $F(x)$ be the cumulative distribution function of $X$. Suppose that for each $\delta>0$, we have
\[
\lim_{n\to\infty}P(\lvert X_n-X\rvert\geq\delta)=0.
\]
We want to prove
\[
\lim_{n\to\infty}P(X_n\leq a)=P(X\leq a),
\]
for each $a$ such that $F(x)$ is continuous at $x=a$.

Suppose $\delta>0$ and a constant $a$ is given. The key of the proof is the following inequalities:
\[
P(X_n\leq a)\leq P(X\leq a+\delta)+P(\lvert X_n-X\rvert>\delta),
\tag{10.2}
\]
\[
P(X\leq a-\delta)\leq P(X_n\leq a)+P(\lvert X_n-X\rvert>\delta).
\tag{10.3}
\]
To see the first inequality, note that if $X_n\leq a$ and the difference between $X_n$ and $X$ is less than or equal to $\delta$, then we must have $X\leq a+\delta$. This yields (10.2). The second inequality (10.3) can be derived similarly.

Taking $n$ approaching infinity and using the assumption that $X_n$ converges to $X$ in probability, we have
\[
\limsup_{n\to\infty}P(X_n\leq a)\leq P(X\leq a+\delta)
\]
and
\[
P(X\leq a-\delta)\leq \liminf_{n\to\infty}P(X_n\leq a)
\]
for each $\delta>0$. By taking $\delta\to 0$, we get
\[
P(X<a)\leq \liminf_{n\to\infty}P(X_n\leq a)
\leq \limsup_{n\to\infty}P(X_n\leq a)
\leq P(X\leq a).
\]
If $F(x)$ is continuous at $x=a$, then all of the inequalities above are equality, and hence
\[
\lim_{n\to\infty}P(X_n\leq a)=P(X\leq a).
\]
\hfill $\square$
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology

/-- Local Definition 10.2 convergence in probability implies Mathlib convergence in measure. -/
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

/--
Theorem 10.7 in Mathlib's convergence-in-distribution interface: convergence
in probability implies weak convergence of the laws.
-/
theorem thm_10_7 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXn : ∀ n : ℕ, AEMeasurable (Xn n) μ)
    (hProb : ConvergesInProbability μ Xn X) :
    TendstoInDistribution Xn atTop X (fun _ : ℕ => μ) μ :=
  (tendstoInMeasure_of_convergesInProbability μ Xn X hProb).tendstoInDistribution hXn
