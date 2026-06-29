import Mathlib
import ToyApollo.Output.thm_7_10

/-
TASK ID: def_7_2
TYPE: Definition
SOURCE PLAN: 28_chap7_pushforward_change_of_variable
TASK CONTENT:
\begin{defbox}{7.2}
The measure $X_{\#}\mu$ defined in Theorem 7.10 is called the \textit{push-forward measure} defined by $X$. It is also called the \textit{image} of $\mu$ or the \textit{measure induced by $X$}. When $\mu$ is a probability measure, the induced measure $X_{\#}\mu$ is also a probability measure and is called the \textit{distribution} of $X$.

Other notation for the push-forward measure include $X_{*}\mu$, $\mu^X$, $\mu_X$, and $\mu\circ X^{-1}$.
\end{defbox}
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory

/-- Textbook push-forward measure `Xₐ μ`, defined via Theorem 7.10. -/
noncomputable def PushForwardMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) : Measure ℝ :=
  pushForwardRealMeasure μ X

/-- Synonym used in the textbook: the image of `μ` under `X`. -/
noncomputable def ImageMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) : Measure ℝ :=
  PushForwardMeasure μ X

/-- Synonym used in the textbook: the measure induced by `X`. -/
noncomputable def InducedMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) : Measure ℝ :=
  PushForwardMeasure μ X

/-- When `μ` is a probability measure, the push-forward is the distribution of `X`. -/
noncomputable def RandomVariableDistribution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (X : Ω → ℝ) : Measure ℝ :=
  PushForwardMeasure μ X

/-- The push-forward of a probability measure is again a probability measure. -/
theorem distribution_isProbabilityMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X) :
    IsProbabilityMeasure (RandomVariableDistribution μ X) := by
  simpa [RandomVariableDistribution, PushForwardMeasure, pushForwardRealMeasure] using
    (Measure.isProbabilityMeasure_map hX.aemeasurable)

/-- Exported definition for Definition 7.2. -/
noncomputable def def_7_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) : Measure ℝ :=
  PushForwardMeasure μ X
