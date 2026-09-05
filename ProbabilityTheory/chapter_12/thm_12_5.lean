/-
TASK ID: thm_12_5
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter12-orthogonality-principle
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_12.thm_12_4
import ProbabilityTheory.chapter_12.def_12_5
import ProbabilityTheory.chapter_12.def_12_2




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped InnerProductSpace

noncomputable section



theorem thm_12_5_projection_orthogonal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ClosedSubmodule ℝ (Ω →₂[P] ℝ))
    (Y : Ω →₂[P] ℝ) :
    ∀ X : W,
      ⟪Y - (def_12_5 P W Y : Ω →₂[P] ℝ),
        (X : Ω →₂[P] ℝ)⟫_ℝ = 0 := by
  have hmin := def_12_5_minimizes P W Y
  have horth := (W.norm_eq_iInf_iff_inner_eq_zero (def_12_5 P W Y).2).1 hmin
  intro X
  exact horth X X.2



theorem thm_12_5_orthogonal_unique {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ClosedSubmodule ℝ (Ω →₂[P] ℝ))
    (Y : Ω →₂[P] ℝ) (X : W)
    (horth : ∀ Z : W,
      ⟪Y - (X : Ω →₂[P] ℝ), (Z : Ω →₂[P] ℝ)⟫_ℝ = 0) :
    X = def_12_5 P W Y := by
  have hmin : ‖Y - (X : Ω →₂[P] ℝ)‖ =
      ⨅ Z : W, ‖Y - (Z : Ω →₂[P] ℝ)‖ := by
    refine (W.norm_eq_iInf_iff_inner_eq_zero X.2).2 ?_
    intro Z hZ
    exact horth ⟨Z, hZ⟩
  exact def_12_5_unique P W Y X hmin



theorem thm_12_5 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ClosedSubmodule ℝ (Ω →₂[P] ℝ))
    (Y : Ω →₂[P] ℝ) (X : W) :
    X = def_12_5 P W Y ↔
      ∀ Z : W,
        ⟪Y - (X : Ω →₂[P] ℝ), (Z : Ω →₂[P] ℝ)⟫_ℝ = 0 := by
  constructor
  · intro hX
    subst X
    exact thm_12_5_projection_orthogonal P W Y
  · exact thm_12_5_orthogonal_unique P W Y X
