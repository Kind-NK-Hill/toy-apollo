/-
TASK ID: thm_11_1
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter11-bounds-inequalities
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open scoped InnerProductSpace

theorem thm_11_1 {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (X Y : E) :
    ‖⟪X, Y⟫_𝕜‖ ≤ ‖X‖ * ‖Y‖ := by
  exact norm_inner_le_norm X Y

theorem thm_11_1_equality_iff {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {X Y : E} (hX : X ≠ 0) (hY : Y ≠ 0) :
    ‖⟪X, Y⟫_𝕜‖ = ‖X‖ * ‖Y‖ ↔ ∃ c : 𝕜, c ≠ 0 ∧ Y = c • X := by
  exact norm_inner_eq_norm_iff hX hY

theorem thm_11_1_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X Y : E) : |⟪X, Y⟫_ℝ| ≤ ‖X‖ * ‖Y‖ := by
  exact abs_real_inner_le_norm X Y
