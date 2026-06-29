import Mathlib

/-
TASK ID: def_9_1
TYPE: Definition
SOURCE PLAN: chapter9-moments-mgf
TASK CONTENT:
\begin{defbox}{9.1}
For an integer $r \geq 1$, the $r$-th moment of $X$ is defined as the expectation $\mathbb{E}[X^r]$. The $r$-th central moment is defined by $\mathbb{E}[(X-\mathbb{E}[X])^r]$. In particular, the second central moment is commonly called the variance of $X$; the square root of variance is called the standard deviation.

The third central moment measures the asymmetry of the probability distribution. The skewness of a random variable is defined as the third central moment normalized by the cube of the standard deviation $\sigma$,
\[
\frac{\mathbb{E}[(X-\mathbb{E}[X])^3]}{\sigma^3}.
\]
The analogous quantity of order $4$ is called the kurtosis,
\[
\frac{\mathbb{E}[(X-\mathbb{E}[X])^4]}{\sigma^4}.
\]
It measures the tailedness of the probability distribution.
\end{defbox}
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory

noncomputable abbrev rthMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (r : ℕ) : ℝ :=
  moment X r μ

noncomputable abbrev rthCentralMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (r : ℕ) : ℝ :=
  centralMoment X r μ

noncomputable abbrev variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : ℝ :=
  rthCentralMoment μ X 2

noncomputable abbrev standardDeviation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : ℝ :=
  Real.sqrt (variance μ X)

noncomputable abbrev skewness {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : ℝ :=
  rthCentralMoment μ X 3 / standardDeviation μ X ^ 3

noncomputable abbrev kurtosis {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : ℝ :=
  rthCentralMoment μ X 4 / standardDeviation μ X ^ 4

noncomputable def def_9_1 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (r : ℕ) : ℝ × ℝ :=
  (rthMoment μ X r, rthCentralMoment μ X r)
