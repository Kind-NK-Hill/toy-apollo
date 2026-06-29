import Mathlib

/-
TASK ID: def_13_1
TYPE: Definition
SOURCE PLAN: chapter13-finite-partition
TASK CONTENT:
\begin{defbox}{13.1}
\end{defbox}

Let A be an event in \mathcal{F}withP(A) /=0. We define a probability measure \muA by

\muA(E) \coloneqq P(A \cap E)

P(A) .

The expectation conditioned on the event A is defined by the integral with respect

to the measure \muA,

E[X\vertA] \coloneqq

\int

\Omega

Xd\mu A.

It is easy to verify that \muA is a probability measure on \mathcal{F}with\muA(A) = 1In the

calculations of E[X] and E[X\vertA], we have the same function X mapping from \Omega

to the real numbers. The difference is in the change of measure from P to. \muA.

The next theorem gives the relationship between the two expectation operators.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The conditional probability measure `μ_A`, guarded by the event measurability
and nonzero finite denominator required by the source definition. -/
def def_13_1_conditionalMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (_hA : MeasurableSet A)
    (_hA0 : P A ≠ 0) (_hA_top : P A ≠ ⊤) : Measure Ω :=
  (P A)⁻¹ • P.restrict A

/-- On measurable events this measure has the textbook value
`μ_A(E) = P(A ∩ E) / P(A)`. -/
theorem def_13_1_conditionalMeasure_apply {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A E : Set Ω) (hA : MeasurableSet A)
    (hA0 : P A ≠ 0) (hA_top : P A ≠ ⊤) (hE : MeasurableSet E) :
    def_13_1_conditionalMeasure P A hA hA0 hA_top E = P (A ∩ E) / P A := by
  rw [def_13_1_conditionalMeasure, Measure.smul_apply, Measure.restrict_apply hE]
  rw [Set.inter_comm]
  rw [ENNReal.div_eq_inv_mul]
  simp only [smul_eq_mul]

/-- The conditioned event has conditional probability one when `0 < P(A) < ∞`. -/
theorem def_13_1_conditionalMeasure_self {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (hA0 : P A ≠ 0) (hA_top : P A ≠ ⊤) :
    def_13_1_conditionalMeasure P A hA hA0 hA_top A = 1 := by
  rw [def_13_1_conditionalMeasure_apply P A A hA hA0 hA_top hA]
  rw [Set.inter_self]
  exact ENNReal.div_self hA0 hA_top

/-- Conditional expectation given an event is the integral with respect to the
conditional probability measure `μ_A`. -/
def def_13_1_conditionalEventExpectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (hA0 : P A ≠ 0) (hA_top : P A ≠ ⊤) (X : Ω → ℝ) : ℝ :=
  ∫ ω, X ω ∂def_13_1_conditionalMeasure P A hA hA0 hA_top

/-- Exported Definition 13.1: expectation conditioned on an event `A`. -/
def def_13_1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (hA0 : P A ≠ 0) (hA_top : P A ≠ ⊤) (X : Ω → ℝ) : ℝ :=
  def_13_1_conditionalEventExpectation P A hA hA0 hA_top X
