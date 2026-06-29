import Mathlib
import ToyApollo.Output.def_13_1

/-
TASK ID: thm_13_1
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-finite-partition
TASK CONTENT:
\begin{thmbox}{13.1}
\end{thmbox}

For a random variable X inL1(P) ,

E[X\vertA]= 1

P(A)

\int

A

XdP.

\textit{Proof} Suppose X is an indicator function . 1B for someB \in\mathcal{F}Then we have

E[1B\vertA] \coloneqq

\int

\Omega

1B d\muA = \muA(B) \coloneqq P(A \cap B)

P(A) .

On the other hand,

P(A)

\int

A

1B dP = 1

P(A)

\int

\Omega

1A 1B dP = 1

P(A)

\int

\Omega

1A\capB dP = P(A \cap B)

P(A) .

Therefore, the equality in the theorem holds for \mathcal{F}-measurable indicator functions.

By linearity, we can extend it to all \mathcal{F}-measurable simple functions.

The remaining tasks are to extend this to nonnegative functions and real-valued

functions. By the monotone convergence theorem, we can extend it to all non-

negative \mathcal{F}-measurable functions. Finally, by decomposing real-valued functions

into positive and negative parts, we can extend it to all \mathcal{F}-measurable real-valued

functions. The rest of the proof is mechanical and is omitted. \hfill $\square$

We next extend the definition of conditional expectation to conditional expecta-

tion given a finite partition, as we would like to have the flexibility to condition on

different sets A.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

noncomputable section

/-- The indicator-function starting point of the textbook proof. With the
formula-level Definition 13.1, it is the same normalized set integral specialized
to an indicator. -/
theorem thm_13_1_indicator_formula {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A B : Set Ω) (hA : MeasurableSet A)
    (hA0 : P A ≠ 0) (hA_top : P A ≠ ⊤) :
    def_13_1 P A hA hA0 hA_top (B.indicator fun _ => (1 : ℝ)) =
      (∫ ω in A, B.indicator (fun _ => (1 : ℝ)) ω ∂P) / (P A).toReal := by
  unfold def_13_1 def_13_1_conditionalEventExpectation def_13_1_conditionalMeasure
  rw [integral_smul_measure]
  simp [smul_eq_mul, one_div, div_eq_inv_mul]

/-- Linearity reduces the simple-function stage to the same normalized
set-integral formula. The general monotone-convergence extension is already
represented by the exported definition for all real-valued functions. -/
theorem thm_13_1_simple_formula {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (hA0 : P A ≠ 0) (hA_top : P A ≠ ⊤) (X : Ω → ℝ) :
    def_13_1 P A hA hA0 hA_top X = (∫ ω in A, X ω ∂P) / (P A).toReal := by
  unfold def_13_1 def_13_1_conditionalEventExpectation def_13_1_conditionalMeasure
  rw [integral_smul_measure]
  simp [smul_eq_mul, one_div, div_eq_inv_mul]

/-- Theorem 13.1: conditional expectation given an event is the normalized
integral of `X` over that event. -/
theorem thm_13_1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (hA0 : P A ≠ 0) (hA_top : P A ≠ ⊤) (X : Ω → ℝ) :
    def_13_1 P A hA hA0 hA_top X =
      (1 / (P A).toReal) * ∫ ω in A, X ω ∂P := by
  unfold def_13_1 def_13_1_conditionalEventExpectation def_13_1_conditionalMeasure
  rw [integral_smul_measure]
  simp [smul_eq_mul, one_div, div_eq_inv_mul]
