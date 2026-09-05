/-
TASK ID: thm_12_4
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter12-closed-subspace-projection
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_12.thm_12_3
import ProbabilityTheory.chapter_12.prob_12_1




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped InnerProductSpace

noncomputable section



theorem thm_12_4_parallelogram_input {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (U V : Ω →₂[P] ℝ) :
    ‖U + V‖ ^ 2 + ‖U - V‖ ^ 2 = 2 * ‖U‖ ^ 2 + 2 * ‖V‖ ^ 2 :=
  prob_12_1_l2 P U V



theorem thm_12_4_source_existence {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ClosedSubmodule ℝ (Ω →₂[P] ℝ))
    (Y : Ω →₂[P] ℝ) :
    ∃ X : W, ‖Y - (X : Ω →₂[P] ℝ)‖ =
      ⨅ Z : W, ‖Y - (Z : Ω →₂[P] ℝ)‖ := by
  haveI : CompleteSpace (Ω →₂[P] ℝ) := thm_12_3 P
  have hcomplete : IsComplete (W.toSubmodule : Set (Ω →₂[P] ℝ)) := by
    simpa [ClosedSubmodule.coe_toSubmodule] using W.isClosed.isComplete
  rcases Submodule.exists_norm_eq_iInf_of_complete_subspace
      (K := W.toSubmodule) hcomplete Y with ⟨v, hv, hmin⟩
  refine ⟨⟨v, hv⟩, ?_⟩
  simpa [ClosedSubmodule.coe_toSubmodule] using hmin



theorem thm_12_4_source_uniqueness {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ClosedSubmodule ℝ (Ω →₂[P] ℝ))
    (Y : Ω →₂[P] ℝ) (X₁ X₂ : W)
    (h₁ : ‖Y - (X₁ : Ω →₂[P] ℝ)‖ =
      ⨅ Z : W, ‖Y - (Z : Ω →₂[P] ℝ)‖)
    (h₂ : ‖Y - (X₂ : Ω →₂[P] ℝ)‖ =
      ⨅ Z : W, ‖Y - (Z : Ω →₂[P] ℝ)‖) :
    X₁ = X₂ := by
  have h₁' : ‖Y - (X₁ : Ω →₂[P] ℝ)‖ =
      ⨅ Z : (W.toSubmodule : Set (Ω →₂[P] ℝ)),
        ‖Y - (Z : Ω →₂[P] ℝ)‖ := by
    simpa [ClosedSubmodule.coe_toSubmodule] using h₁
  have h₂' : ‖Y - (X₂ : Ω →₂[P] ℝ)‖ =
      ⨅ Z : (W.toSubmodule : Set (Ω →₂[P] ℝ)),
        ‖Y - (Z : Ω →₂[P] ℝ)‖ := by
    simpa [ClosedSubmodule.coe_toSubmodule] using h₂
  have horth₁ :=
    (Submodule.norm_eq_iInf_iff_real_inner_eq_zero
      (K := W.toSubmodule) (u := Y)
      (v := (X₁ : Ω →₂[P] ℝ)) X₁.2).1 h₁'
  have horth₂ :=
    (Submodule.norm_eq_iInf_iff_real_inner_eq_zero
      (K := W.toSubmodule) (u := Y)
      (v := (X₂ : Ω →₂[P] ℝ)) X₂.2).1 h₂'
  let d : Ω →₂[P] ℝ := (X₂ : Ω →₂[P] ℝ) - (X₁ : Ω →₂[P] ℝ)
  have hdmem : d ∈ W.toSubmodule := by
    exact W.toSubmodule.sub_mem X₂.2 X₁.2
  have hA : inner ℝ (Y - (X₁ : Ω →₂[P] ℝ)) d = 0 := horth₁ d hdmem
  have hB : inner ℝ (Y - (X₂ : Ω →₂[P] ℝ)) d = 0 := horth₂ d hdmem
  have hdiff : inner ℝ d d = 0 := by
    have hsub :
        inner ℝ
          ((Y - (X₁ : Ω →₂[P] ℝ)) - (Y - (X₂ : Ω →₂[P] ℝ))) d = 0 := by
      rw [inner_sub_left, hA, hB, sub_self]
    have hvec :
        (Y - (X₁ : Ω →₂[P] ℝ)) - (Y - (X₂ : Ω →₂[P] ℝ)) = d := by
      simp [d]
    simpa [hvec] using hsub
  have hnormsq : ‖d‖ ^ 2 = 0 := by
    simpa [real_inner_self_eq_norm_sq] using hdiff
  have hnorm : ‖d‖ = 0 := sq_eq_zero_iff.mp hnormsq
  have hd0 : d = 0 := norm_eq_zero.mp hnorm
  apply Subtype.ext
  have hx : (X₂ : Ω →₂[P] ℝ) = (X₁ : Ω →₂[P] ℝ) := by
    have : (X₂ : Ω →₂[P] ℝ) - (X₁ : Ω →₂[P] ℝ) = 0 := by
      simpa [d] using hd0
    exact sub_eq_zero.mp this
  exact hx.symm



theorem thm_12_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (W : ClosedSubmodule ℝ (Ω →₂[P] ℝ)) (Y : Ω →₂[P] ℝ) :
    ∃! X : W, ‖Y - (X : Ω →₂[P] ℝ)‖ =
      ⨅ Z : W, ‖Y - (Z : Ω →₂[P] ℝ)‖ := by
  rcases thm_12_4_source_existence P W Y with ⟨X, hX⟩
  refine ⟨X, hX, ?_⟩
  intro Z hZ
  exact thm_12_4_source_uniqueness P W Y Z X hZ hX
