import Mathlib
import ToyApollo.Output.def_14_1

/-
TASK ID: def_14_2
TYPE: Definition
SOURCE PLAN: chapter14-weak-convergence
TASK CONTENT:
\begin{defbox}{14.2}
\end{defbox}

Suppose X1, X2, X3 ... , is a sequence of random variables, and X is a random

variable. We say that .(Xn)\infty

n=1 converges weakly to X if the image measures of

Xn's converge weakly to the image measure of X, ie.,

limn\to\infty E[h(Xn)]= E[h(X)]

for all continuous and bounded functions h.

The next theorem establishes the equivalence of weak convergence and conver-

gence in distribution. Weak convergence is an elegant definition, and it is more

convenient for proofs. However, checking the condition for weak convergence can

be challenging, as it involves considering infinitely many potential test functions. In

contrast, the definition of convergence in distribution is often more practical to use

in calculations.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology

noncomputable section

/-- Definition 14.2: a sequence of real random variables converges weakly to
`X` when the induced image measures converge weakly, equivalently when every
bounded continuous test has convergent expectations. -/
def def_14_2
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X) : Prop :=
  def_14_1_randomVariableWeakConvergence μ Xseq X hXseq hX

/-- The image-measure formulation of Definition 14.2, using the law helpers
from Definition 14.1. -/
def def_14_2_lawWeakConvergence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X) : Prop :=
  def_14_1 (def_14_1_laws μ Xseq hXseq) (def_14_1_law μ X hX)

/-- The expectation formulation displayed in the text after Definition 14.2. -/
theorem def_14_2_iff_expectations
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Xseq : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X) :
    def_14_2 μ Xseq X hXseq hX ↔
      ∀ h : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun n : ℕ => ∫ ω, h (Xseq n ω) ∂μ) atTop
          (𝓝 (∫ ω, h (X ω) ∂μ)) := by
  exact def_14_1_randomVariableWeakConvergence_iff_expectations μ hXseq hX

/-- Definition 14.2 also matches Mathlib's convergence-in-distribution
interface when all variables live on the same probability space. -/
def def_14_2_mathlibConvergence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  TendstoInDistribution Xseq atTop X (fun _ : ℕ => μ) μ

/-- The Mathlib object contains the same law-level convergence statement used
by Definition 14.2.  This theorem is a reusable projection of the packaged
structure. -/
theorem def_14_2_mathlibConvergence_tendsto_laws
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Xseq : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (h : def_14_2_mathlibConvergence μ Xseq X) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n : ℕ =>
        ⟨Measure.map (Xseq n) μ, Measure.isProbabilityMeasure_map
          (h.forall_aemeasurable n)⟩)
      atTop
      (𝓝 ⟨Measure.map X μ, Measure.isProbabilityMeasure_map h.aemeasurable_limit⟩) :=
  h.tendsto
