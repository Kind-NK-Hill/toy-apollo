/-
TASK ID: thm_12_6
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter12-mmse-estimation
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_12_4
import ToyApollo.Output.thm_12_5

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

theorem thm_12_6_comp_measurable {Ω S : Type*} [MeasurableSpace S]
    (X : Ω → S) (g : S → ℝ) (hg : Measurable g) :
    Measurable[(inferInstance : MeasurableSpace S).comap X] (g ∘ X) :=
  hg.comp (comap_measurable X)

theorem thm_12_6_factorization {Ω S : Type*} [MeasurableSpace S]
    (X : Ω → S) (Y : Ω → ℝ)
    (hY : Measurable[(inferInstance : MeasurableSpace S).comap X] Y) :
    ∃ g : S → ℝ, Measurable g ∧ Y = g ∘ X :=
  hY.exists_eq_measurable_comp

theorem thm_12_6 {Ω S : Type*} [MeasurableSpace S]
    (X : Ω → S) (Y : Ω → ℝ) :
    (∃ g : S → ℝ, Measurable g ∧ Y = g ∘ X) ↔
      Measurable[(inferInstance : MeasurableSpace S).comap X] Y := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact thm_12_6_comp_measurable X g hg
  · exact thm_12_6_factorization X Y

theorem thm_12_6_fin {Ω : Type*} (n : ℕ)
    (X : Ω → Fin n → ℝ) (Y : Ω → ℝ) :
    (∃ g : (Fin n → ℝ) → ℝ, Measurable g ∧ Y = g ∘ X) ↔
      Measurable[(inferInstance : MeasurableSpace (Fin n → ℝ)).comap X] Y :=
  thm_12_6 X Y

theorem thm_12_6_mmse_projection_characterization {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ClosedSubmodule ℝ (Ω →₂[P] ℝ)) (Y : Ω →₂[P] ℝ) (Yhat : W) :
    Yhat = def_12_5 P W Y ↔
      ∀ Z : W,
        ⟪Y - (Yhat : Ω →₂[P] ℝ), (Z : Ω →₂[P] ℝ)⟫_ℝ = 0 :=
  thm_12_5 P W Y Yhat
