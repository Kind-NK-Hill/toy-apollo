import Mathlib
import ToyApollo.Output.def_12_2

/-
TASK ID: def_12_4
TYPE: Definition
SOURCE PLAN: chapter12-closed-subspace-projection
TASK CONTENT:
\begin{defbox}{12.4}
\end{defbox}

A subset W ofL2(P) is said to be:

A subspace ifX, Y \in W implies\alphaX + \betaY \in W for all scalars \alpha and. \beta

Closed ifXn \in W ,f o rn = 1, 2, 3,... , andXn

L2

-\to X, then. X \in W

In any finite-dimensional vector space, such as Rn, any subspace is closed. The

assumption of closedness is important when we are dealing with vector space with

infinite dimension.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory
open Filter

noncomputable section

/-- A subset of real `L²(P)` functions, using the local Chapter 12 `L2Function`
predicate. -/
def L2Subset {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : Set (Ω → ℝ)) : Prop :=
  ∀ X, X ∈ W → L2Function P X

/-- Textbook linear-subspace condition for a subset of `L²(P)`: it contains
zero and is closed under all real linear combinations. -/
def L2Subspace {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : Set (Ω → ℝ)) : Prop :=
  L2Subset P W ∧
    (fun _ : Ω => (0 : ℝ)) ∈ W ∧
      ∀ X Y, X ∈ W → Y ∈ W → ∀ α β : ℝ,
        (fun ω => α * X ω + β * Y ω) ∈ W

/-- Convergence in the `L²(P)` norm from Definition 12.2. -/
def L2Tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  ∃ hDiff : ∀ n : ℕ, L2Function P (fun ω => Xn n ω - X ω),
    Tendsto
      (fun n => l2Norm P (fun ω => Xn n ω - X ω) (hDiff n))
      atTop (nhds 0)

/-- Textbook closedness for a subset of `L²(P)`: every `L²`-norm limit of a
sequence from the subset remains in the subset. -/
def L2Closed {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : Set (Ω → ℝ)) : Prop :=
  ∀ Xn X, (∀ n, Xn n ∈ W) → L2Tendsto P Xn X → X ∈ W

/-- Definition 12.4: a closed subspace of `L²(P)` is a linear subspace that is
closed under `L²`-norm limits. -/
def L2ClosedSubspace {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : Set (Ω → ℝ)) : Prop :=
  L2Subspace P W ∧ L2Closed P W

/-- Exported Definition 12.4 interface. -/
def def_12_4 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : Set (Ω → ℝ)) : Prop :=
  L2ClosedSubspace P W

theorem def_12_4_iff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : Set (Ω → ℝ)) :
    def_12_4 P W ↔ L2Subspace P W ∧ L2Closed P W :=
  Iff.rfl

theorem def_12_4_subspace {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {W : Set (Ω → ℝ)}
    (hW : def_12_4 P W) :
    L2Subspace P W :=
  hW.1

theorem def_12_4_closed {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {W : Set (Ω → ℝ)}
    (hW : def_12_4 P W) :
    L2Closed P W :=
  hW.2

/-- The textbook finite-dimensional comparison: in a finite-dimensional normed
real vector space, every linear subspace is closed. -/
theorem finiteDimensional_submodule_isClosed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : Submodule ℝ E) [FiniteDimensional ℝ W] :
    IsClosed (W : Set E) :=
  Submodule.closed_of_finiteDimensional W
