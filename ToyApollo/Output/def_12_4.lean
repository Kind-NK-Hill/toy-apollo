/-
TASK ID: def_12_4
TYPE: Definition
SOURCE PLAN: chapter12-closed-subspace-projection
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_12_2

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory
open Filter

noncomputable section

def L2Subset {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : Set (Ω → ℝ)) : Prop :=
  ∀ X, X ∈ W → L2Function P X

def L2Subspace {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : Set (Ω → ℝ)) : Prop :=
  L2Subset P W ∧
    (fun _ : Ω => (0 : ℝ)) ∈ W ∧
      ∀ X Y, X ∈ W → Y ∈ W → ∀ α β : ℝ,
        (fun ω => α * X ω + β * Y ω) ∈ W

def L2Tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  ∃ hDiff : ∀ n : ℕ, L2Function P (fun ω => Xn n ω - X ω),
    Tendsto
      (fun n => l2Norm P (fun ω => Xn n ω - X ω) (hDiff n))
      atTop (nhds 0)

def L2Closed {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : Set (Ω → ℝ)) : Prop :=
  ∀ Xn X, (∀ n, Xn n ∈ W) → L2Tendsto P Xn X → X ∈ W

def L2ClosedSubspace {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : Set (Ω → ℝ)) : Prop :=
  L2Subspace P W ∧ L2Closed P W

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

theorem finiteDimensional_submodule_isClosed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : Submodule ℝ E) [FiniteDimensional ℝ W] :
    IsClosed (W : Set E) :=
  Submodule.closed_of_finiteDimensional W
