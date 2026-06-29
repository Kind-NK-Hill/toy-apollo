import Mathlib
import ToyApollo.Output.def_9_1

/-
TASK ID: def_9_2
TYPE: Definition
SOURCE PLAN: chapter9-moments-mgf
TASK CONTENT:
To compute the higher-order moments, we can use the moment generating function.

\begin{defbox}{9.2}
Let $X$ be a real-valued random variable defined on a probability space $(\Omega,\mathcal{F},P)$. The moment generating function (mgf) of $X$ is defined as
\[
M_X(t) \coloneqq \mathbb{E}[e^{tX}] =
\int_{\Omega} e^{tX(\omega)}\,dP(\omega),
\]
where $t \in \mathbb{R}$. We say that $X$ has a moment generating function if there exists $\delta > 0$ such that $M_X(t)$ is finite for all $t$ in the interval $(-\delta,\delta)$.

Since $X$ is real-valued, the function $e^{tX}$ is nonnegative, and hence the expectation $\mathbb{E}[e^{tX}]$ is well-defined. However, the expected value may be infinity. It is essential to have $M_X(t)$ defined and finite in a non-empty interval $(-\delta,\delta)$ that contains $0$ in the interior. This ensures that we can differentiate $M_X(t)$ with respect to $t$ at $t=0$.
\end{defbox}
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def momentGeneratingFunction {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (_hX : AEMeasurable X μ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (Real.exp (t * X ω)) ∂μ

def HasMomentGeneratingFunction {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : AEMeasurable X μ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    ∀ t : ℝ, |t| < δ →
      momentGeneratingFunction μ X hX t < ⊤

def HasFiniteMomentGeneratingFunctionAt {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : AEMeasurable X μ) (t : ℝ) : Prop :=
  momentGeneratingFunction μ X hX t < ⊤

theorem momentGeneratingFunction_eq_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : AEMeasurable X μ) (t : ℝ) :
    momentGeneratingFunction μ X hX t =
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * X ω)) ∂μ := by
  rfl

noncomputable def def_9_2 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : AEMeasurable X μ) : ℝ → ℝ≥0∞ :=
  momentGeneratingFunction μ X hX
