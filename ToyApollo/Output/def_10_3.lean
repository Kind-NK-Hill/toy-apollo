import Mathlib

/-
TASK ID: def_10_3
TYPE: Definition
SOURCE PLAN: chapter10-mean
TASK CONTENT:
\begin{defbox}{10.3}
For $r\geq 1$, $(X_n)_{n\geq 1}$ is said to converge to $X$ in the $r$-th mean (or in the $L^r$ norm) if
\[
\mathbb{E}[\lvert X_n-X\rvert^r]\to 0
\]
as $n\to\infty$.

When $r=1$, we say that $X_n$ converges to $X$ in the mean. When $r=2$, we say that $X_n$ converges to $X$ in mean square or in quadratic mean. Other notation for mean square convergence includes
\[
X_n\xrightarrow{\mathrm{m.s.}}X
\qquad\text{and}\qquad
\operatorname{l.i.m.} X_n=X.
\]
\end{defbox}
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory

/-- The nonnegative moment of the deviation `|X_n - X|^r`. -/
noncomputable def meanDeviationMoment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (r : ℝ) (n : ℕ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (|Xn n ω - X ω| ^ r) ∂μ

/-- Convergence in the `r`-th mean, also called convergence in the `L^r` norm in
the textbook. -/
noncomputable def ConvergesInRthMean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (r : ℝ) : Prop :=
  1 ≤ r ∧ Tendsto (fun n : ℕ => meanDeviationMoment μ Xn X r n) atTop (nhds 0)

/-- Convergence in the mean, the case `r = 1`. -/
noncomputable def ConvergesInMean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  ConvergesInRthMean μ Xn X 1

/-- Mean-square, or quadratic-mean, convergence: the case `r = 2`. -/
noncomputable def ConvergesInMeanSquare {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  ConvergesInRthMean μ Xn X 2

/-- Exported definition for Definition 10.3. -/
noncomputable def def_10_3 :=
  (@ConvergesInRthMean, @ConvergesInMean, @ConvergesInMeanSquare)
