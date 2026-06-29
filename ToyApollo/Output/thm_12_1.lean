/-
TASK ID: thm_12_1
TYPE: Theorem_Statement
SOURCE PLAN: chapter12-l2-norm-inner-product
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_12_2

-- WRITE FINAL LEAN CODE BELOW

open scoped InnerProductSpace

theorem thm_12_1_inner_add_smul {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (X Y1 Y2 : E) (α β : 𝕜) :
    ⟪X, α • Y1 + β • Y2⟫_𝕜 =
      α * ⟪X, Y1⟫_𝕜 + β * ⟪X, Y2⟫_𝕜 := by
  calc
    ⟪X, α • Y1 + β • Y2⟫_𝕜 =
        ⟪X, α • Y1⟫_𝕜 + ⟪X, β • Y2⟫_𝕜 := by
      rw [inner_add_right]
    _ = α * ⟪X, Y1⟫_𝕜 + β * ⟪X, Y2⟫_𝕜 := by
      rw [inner_smul_right, inner_smul_right]

theorem thm_12_1_real_symm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X Y : E) :
    ⟪X, Y⟫_ℝ = ⟪Y, X⟫_ℝ := by
  exact (real_inner_comm X Y).symm

theorem thm_12_1_conj_symm {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (X Y : E) :
    ⟪X, Y⟫_𝕜 = star ⟪Y, X⟫_𝕜 := by
  exact (inner_conj_symm X Y).symm

theorem thm_12_1_norm_smul {𝕜 E : Type*} [Norm 𝕜]
    [NormedAddCommGroup E] [SMul 𝕜 E] [NormSMulClass 𝕜 E]
    (α : 𝕜) (X : E) :
    ‖α • X‖ = ‖α‖ * ‖X‖ := by
  exact norm_smul α X

theorem thm_12_1_triangle {E : Type*} [NormedAddCommGroup E] (X Y : E) :
    ‖X + Y‖ ≤ ‖X‖ + ‖Y‖ := by
  exact norm_add_le X Y

theorem thm_12_1 {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (X Y Y1 Y2 : E) (α β : 𝕜) :
    ⟪X, α • Y1 + β • Y2⟫_𝕜 =
        α * ⟪X, Y1⟫_𝕜 + β * ⟪X, Y2⟫_𝕜 ∧
      ⟪X, Y⟫_𝕜 = star ⟪Y, X⟫_𝕜 ∧
      ‖α • X‖ = ‖α‖ * ‖X‖ ∧
      ‖X + Y‖ ≤ ‖X‖ + ‖Y‖ := by
  exact ⟨thm_12_1_inner_add_smul X Y1 Y2 α β,
    thm_12_1_conj_symm X Y, thm_12_1_norm_smul α X,
    thm_12_1_triangle X Y⟩
