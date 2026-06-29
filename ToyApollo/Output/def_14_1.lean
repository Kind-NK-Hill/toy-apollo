import Mathlib
import ToyApollo.Output.thm_7_11

/-
TASK ID: def_14_1
TYPE: Definition
SOURCE PLAN: chapter14-weak-convergence
TASK CONTENT:
\begin{defbox}{14.1}
\end{defbox}

Let. Pn,f o rn \geq 1, be probability measures and P be another probability measure

defined on sample space RI f

limn\to\infty

\int

R

h(x) dPn(x) =

\int

R

h(x) dP(x)

for all bounded and continuous function h(x), then we say that Pn converges

weakly to P The notation for weak convergence is

Pn

W

\to P or Pn P.

We often apply this definition with the probability measures are the push-forward

measures of some random variables. By using the change-of-variable formula

(Theorem 7.11), we can formulate weak convergence for a sequence of random

variables as follows.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology

noncomputable section

/-- Definition 14.1 at the measure level: `P_n` converges weakly to `P` when
the integrals of every bounded continuous real test function converge. -/
def def_14_1_weakConvergence
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ) : Prop :=
  ∀ h : BoundedContinuousFunction ℝ ℝ,
    Tendsto (fun n : ℕ => ∫ x, h x ∂(Pseq n : Measure ℝ)) atTop
      (𝓝 (∫ x, h x ∂(P : Measure ℝ)))

/-- The notation-bearing definition exported for downstream tasks. -/
def def_14_1
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ) : Prop :=
  def_14_1_weakConvergence Pseq P

/-- Mathlib's topology on probability measures is exactly the weak topology
described in Definition 14.1. -/
theorem def_14_1_iff_tendsto
    {Pseq : ℕ → ProbabilityMeasure ℝ} {P : ProbabilityMeasure ℝ} :
    def_14_1 Pseq P ↔ Tendsto Pseq atTop (𝓝 P) := by
  simpa [def_14_1, def_14_1_weakConvergence] using
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto
      (F := atTop) (μs := Pseq) (μ := P)).symm

/-- The law of a real random variable as a probability measure on `ℝ`. -/
def def_14_1_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) : ProbabilityMeasure ℝ :=
  ⟨Measure.map X μ, Measure.isProbabilityMeasure_map hX.aemeasurable⟩

/-- The sequence of laws induced by a sequence of real random variables. -/
def def_14_1_laws {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ n : ℕ, Measurable (X n)) :
    ℕ → ProbabilityMeasure ℝ :=
  fun n => def_14_1_law μ (X n) (hX n)

/-- The change-of-variable formula from Theorem 7.11 specialized to bounded
continuous test functions. -/
theorem def_14_1_changeOfVariables_boundedContinuous
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → ℝ} (hX : Measurable X)
    (h : BoundedContinuousFunction ℝ ℝ) :
    ∫ ω, h (X ω) ∂μ = ∫ x, h x ∂Measure.map X μ := by
  exact (thm_7_11 μ hX (map_continuous h).measurable).2

/-- Definition 14.1 in the random-variable form announced after the definition:
the push-forward laws of `X_n` converge weakly to the push-forward law of `X`. -/
def def_14_1_randomVariableWeakConvergence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X) : Prop :=
  ∀ h : BoundedContinuousFunction ℝ ℝ,
    Tendsto (fun n : ℕ => ∫ x, h x ∂Measure.map (Xseq n) μ) atTop
      (𝓝 (∫ x, h x ∂Measure.map X μ))

/-- The random-variable formulation is exactly convergence of expectations of
all bounded continuous test functions, by the change-of-variable formula. -/
theorem def_14_1_randomVariableWeakConvergence_iff_expectations
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Xseq : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X) :
    def_14_1_randomVariableWeakConvergence μ Xseq X hXseq hX ↔
      ∀ h : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun n : ℕ => ∫ ω, h (Xseq n ω) ∂μ) atTop
          (𝓝 (∫ ω, h (X ω) ∂μ)) := by
  constructor
  · intro hWeak h
    have hLaw := hWeak h
    convert hLaw using 1
    · ext n
      exact def_14_1_changeOfVariables_boundedContinuous μ (hXseq n) h
    · exact congrArg (fun y : ℝ => 𝓝 y)
        (def_14_1_changeOfVariables_boundedContinuous μ hX h)
  · intro hExp
    intro h
    have hOriginal := hExp h
    convert hOriginal using 1
    · ext n
      exact (def_14_1_changeOfVariables_boundedContinuous μ (hXseq n) h).symm
    · exact congrArg (fun y : ℝ => 𝓝 y)
        (def_14_1_changeOfVariables_boundedContinuous μ hX h).symm
