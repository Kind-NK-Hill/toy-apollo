import Mathlib

/-
TASK ID: def_10_4
TYPE: Definition
SOURCE PLAN: chapter10-distribution-total-variation
TASK CONTENT:
\begin{defbox}{10.4 (Convergence in Distribution)}
Let $(F_n)_{n=1}^{\infty}$ be a sequence of cumulative distribution functions, and let $F$ be another cumulative distribution function. We say that $(F_n)_{n=1}^{\infty}$ converges in distribution, or in law, if
\[
\lim_{n\to\infty}F_n(x)=F(x)
\]
at every continuity point of $F(x)$. We use the notation
\[
F_n\xrightarrow{D}F
\qquad\text{or}\qquad
F_n\xrightarrow{L}F
\]
for convergence in distribution.

Given a sequence of probability measures $\mu_n$'s and another probability measure $\mu$, all defined on the real number line, we say that $(\mu_n)_{n=1}^{\infty}$ converges to $\mu$ in distribution if the corresponding Stieltjes measure functions
\[
F_n(x)=\mu_n((-\infty,x])
\qquad\text{and}\qquad
F(x)=\mu((-\infty,x])
\]
converge in distribution.

A sequence of random variables $X_n$'s, for $n=1,2,3,\ldots$, is said to be converging to a random variable $X$ in distribution, or in law, if the cumulative distribution functions of the $X_n$'s converge to the cumulative distribution function of $X$ in distribution.
\end{defbox}
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set

/-- Convergence in distribution for cumulative distribution functions: pointwise
convergence at every continuity point of the limiting cdf. -/
def CdfConvergesInDistribution (Fn : ℕ → ℝ → ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, ContinuousAt F x → Tendsto (fun n : ℕ => Fn n x) atTop (nhds (F x))

/-- The cdf associated to a probability measure on the real line, written as
`μ ((-∞, x])`. -/
noncomputable def measureCdf (μ : Measure ℝ) (x : ℝ) : ℝ :=
  μ.real (Iic x)

/-- Convergence in distribution for probability measures on `ℝ`, via their cdfs. -/
noncomputable def MeasuresConvergeInDistribution (μn : ℕ → Measure ℝ) (μ : Measure ℝ) :
    Prop :=
  CdfConvergesInDistribution (fun n x => measureCdf (μn n) x) (measureCdf μ)

/-- Convergence in distribution for real-valued random variables, via the cdfs of
their image measures. -/
noncomputable def RandomVariablesConvergeInDistribution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  MeasuresConvergeInDistribution (fun n => Measure.map (Xn n) μ) (Measure.map X μ)

/-- Exported definition for Definition 10.4. -/
noncomputable def def_10_4 :=
  (@CdfConvergesInDistribution, @MeasuresConvergeInDistribution,
    @RandomVariablesConvergeInDistribution)
