import Mathlib
import ToyApollo.Output.def_13_3

/-
TASK ID: ex_13_2_1
TYPE: Example_Proof
SOURCE PLAN: chapter13-sub-sigma-algebra
TASK CONTENT:
\textbf{Example 13.2.1 (Conditioning on the Smallest\sigma-Algebra)} \\

Take \mathcal{G}={ \emptyset,\Omega }A \mathcal{G}-measurable random variable X is a constant function. That is, there is a

constant c such thatX() = c for all. \in \Omega We want to determine the value of cI n (13.3),i fw e

takeB = \Omega ,we get

\int

\Omega

E[X\vert{\emptyset,\Omega }]dP = E[X].

On the other hand, since E[X\vert\mathcal{G}]() is equal to the constant c for all. ,we have

\int

\Omega

E[X\vert{\emptyset,\Omega }]dP =

\int

\Omega

cdP = c.

Therefore, the value of c is equal to E[X]The conditional expectation E[X\vert{\emptyset,\Omega }] is a constant

function with valueE[X].
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

noncomputable section

/-- The smallest sigma-field is a sub-sigma-field of any ambient sigma-field. -/
theorem ex_13_2_1_bottom_subSigma {Ω : Type*} [𝓕 : MeasurableSpace Ω] :
    IsSubSigmaField (⊥ : SigmaField Ω) 𝓕 := by
  intro A hA
  rcases MeasurableSpace.measurableSet_bot_iff.mp hA with rfl | rfl
  · exact MeasurableSet.empty
  · exact MeasurableSet.univ

/-- The constant predicted by the textbook when conditioning on
`{∅, Ω}`. -/
def ex_13_2_1_trivialConditionalExpectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) : Ω → ℝ :=
  fun _ => ∫ ω, X ω ∂P

/-- Example 13.2.1: conditioning on the smallest sigma-field gives the constant
random variable equal to the expectation of `X`. -/
theorem ex_13_2_1 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Integrable X P) :
    @def_13_3 Ω 𝓕 P (⊥ : SigmaField Ω)
      (@ex_13_2_1_bottom_subSigma Ω 𝓕) X
      (ex_13_2_1_trivialConditionalExpectation P X) := by
  refine ⟨hX, ?_, ?_, ?_⟩
  · unfold ex_13_2_1_trivialConditionalExpectation
    exact integrable_const _
  · unfold ex_13_2_1_trivialConditionalExpectation
    exact measurable_const
  · intro B hB
    rcases MeasurableSpace.measurableSet_bot_iff.mp hB with rfl | rfl
    · simp [ex_13_2_1_trivialConditionalExpectation]
    · simp [ex_13_2_1_trivialConditionalExpectation]
