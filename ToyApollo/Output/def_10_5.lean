import Mathlib
import ToyApollo.Output.def_8_5
import ToyApollo.Output.def_10_4

/-
TASK ID: def_10_5
TYPE: Definition
SOURCE PLAN: chapter10-distribution-total-variation
TASK CONTENT:
\begin{defbox}{10.5 (Convergence in Total Variation)}
A sequence of probability measures $(P_n)_{n=1}^{\infty}$ defined on a common measurable space is said to converge in total variation to a probability measure $P$ if
\[
d_{\mathrm{TV}}(P_n,P)\to 0
\]
as $n\to\infty$.

A sequence of random variables $(X_n)_{n\geq 1}$ is said to be convergent in total variation if the corresponding image measures on the measure space $(\mathbb{R},\mathcal{B}(\mathbb{R}))$ converge in total variation.
\end{defbox}
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory

/-- Convergence in total variation for probability measures on a common
measurable space. -/
noncomputable def MeasuresConvergeInTotalVariation {Ω : Type*} [MeasurableSpace Ω]
    (Pn : ℕ → Measure Ω) (P : Measure Ω) : Prop :=
  (∀ n : ℕ, IsProbabilityMeasure (Pn n)) ∧
    IsProbabilityMeasure P ∧
      Tendsto (fun n : ℕ => totalVariationDistance (Pn n) P) atTop (nhds 0)

/-- Convergence in total variation for real-valued random variables, via their
image measures on `ℝ`, with the source probability and measurability guards
kept in the public interface. -/
noncomputable def RandomVariablesConvergeInTotalVariation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  IsProbabilityMeasure μ ∧
    (∀ n : ℕ, Measurable (Xn n)) ∧
      Measurable X ∧
        MeasuresConvergeInTotalVariation
          (fun n => Measure.map (Xn n) μ) (Measure.map X μ)

/-- Exported definition for Definition 10.5. -/
noncomputable def def_10_5 :=
  (@MeasuresConvergeInTotalVariation, @RandomVariablesConvergeInTotalVariation)
