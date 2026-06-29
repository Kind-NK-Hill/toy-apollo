/-
TASK ID: ex_12_2_3
TYPE: Example_Proof
SOURCE PLAN: chapter12-closed-subspace-projection
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_12_4
import ToyApollo.Output.def_12_5

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

open scoped InnerProductSpace BigOperators

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
  [IsProbabilityMeasure P]

def ex_12_2_3_fit (X I : Ω →₂[P] ℝ) (a b : ℝ) : Ω →₂[P] ℝ :=
  a • X + b • I

def ex_12_2_3_W (X I : Ω →₂[P] ℝ) : Submodule ℝ (Ω →₂[P] ℝ) :=
  Submodule.span ℝ ({X, I} : Set (Ω →₂[P] ℝ))

instance ex_12_2_3_W_finiteDimensional (X I : Ω →₂[P] ℝ) :
    FiniteDimensional ℝ (ex_12_2_3_W (P := P) X I) := by
  exact Module.Finite.of_fg
    (Submodule.fg_span
      (show ({X, I} : Set (Ω →₂[P] ℝ)).Finite by simp))

theorem ex_12_2_3_fit_mem (X I : Ω →₂[P] ℝ) (a b : ℝ) :
    ex_12_2_3_fit (P := P) X I a b ∈ ex_12_2_3_W (P := P) X I := by
  unfold ex_12_2_3_fit ex_12_2_3_W
  exact Submodule.add_mem _
    (Submodule.smul_mem _ a (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ b (Submodule.subset_span (by simp)))

theorem ex_12_2_3_W_closed (X I : Ω →₂[P] ℝ) :
    IsClosed ((ex_12_2_3_W (P := P) X I : Submodule ℝ (Ω →₂[P] ℝ)) :
      Set (Ω →₂[P] ℝ)) := by
  exact finiteDimensional_submodule_isClosed (ex_12_2_3_W (P := P) X I)

def ex_12_2_3_closedW (X I : Ω →₂[P] ℝ) : ClosedSubmodule ℝ (Ω →₂[P] ℝ) :=
  ClosedSubmodule.mk (ex_12_2_3_W (P := P) X I)
    (ex_12_2_3_W_closed (P := P) X I)

def ex_12_2_3_meanSquareError (Y X I : Ω →₂[P] ℝ) (a b : ℝ) : ℝ :=
  ‖Y - ex_12_2_3_fit (P := P) X I a b‖ ^ 2

def ex_12_2_3_projection (Y X I : Ω →₂[P] ℝ) :
    ex_12_2_3_closedW (P := P) X I :=
  def_12_5 P (ex_12_2_3_closedW (P := P) X I) Y

theorem ex_12_2_3_projection_minimizes (Y X I : Ω →₂[P] ℝ) :
    ‖Y - (ex_12_2_3_projection (P := P) Y X I : Ω →₂[P] ℝ)‖ =
      ⨅ Z : ex_12_2_3_closedW (P := P) X I,
        ‖Y - (Z : Ω →₂[P] ℝ)‖ := by
  exact def_12_5_minimizes P (ex_12_2_3_closedW (P := P) X I) Y

theorem ex_12_2_3 (Y X I : Ω →₂[P] ℝ) :
    (∀ a b : ℝ,
        ex_12_2_3_fit (P := P) X I a b ∈ ex_12_2_3_W (P := P) X I) ∧
      IsClosed ((ex_12_2_3_W (P := P) X I : Submodule ℝ (Ω →₂[P] ℝ)) :
        Set (Ω →₂[P] ℝ)) ∧
      ‖Y - (ex_12_2_3_projection (P := P) Y X I : Ω →₂[P] ℝ)‖ =
        ⨅ Z : ex_12_2_3_closedW (P := P) X I,
          ‖Y - (Z : Ω →₂[P] ℝ)‖ := by
  exact ⟨fun a b => ex_12_2_3_fit_mem (P := P) X I a b,
    ex_12_2_3_W_closed (P := P) X I,
    ex_12_2_3_projection_minimizes (P := P) Y X I⟩
