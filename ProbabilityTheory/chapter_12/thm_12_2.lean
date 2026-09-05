/-
TASK ID: thm_12_2
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter12-l2-norm-inner-product
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_11.thm_11_1
import ProbabilityTheory.chapter_12.thm_12_1




-- WRITE FINAL LEAN CODE BELOW

open scoped InnerProductSpace

 
theorem thm_12_2_cauchy_schwarz_input {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (X Y : E) :
    ‖⟪X, Y⟫_𝕜‖ ≤ ‖X‖ * ‖Y‖ :=
  thm_11_1 X Y



theorem thm_12_2_zero_norm_eq_zero {E : Type*} [NormedAddCommGroup E] (X : E) :
    ‖X‖ = 0 ↔ X = 0 :=
  norm_eq_zero



theorem thm_12_2_squared_estimate {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (X Y : E) :
    ‖X + Y‖ ^ 2 ≤ (‖X‖ + ‖Y‖) ^ 2 := by
  have hcs : ‖⟪X, Y⟫_𝕜‖ ≤ ‖X‖ * ‖Y‖ :=
    thm_12_2_cauchy_schwarz_input X Y
  have hre : RCLike.re ⟪X, Y⟫_𝕜 ≤ ‖X‖ * ‖Y‖ :=
    (RCLike.re_le_norm _).trans hcs
  have hsym : RCLike.re ⟪Y, X⟫_𝕜 = RCLike.re ⟪X, Y⟫_𝕜 := by
    have h :=
      congrArg (fun z : 𝕜 => RCLike.re z) (inner_conj_symm X Y)
    change RCLike.re ((starRingEnd 𝕜) ⟪Y, X⟫_𝕜) =
      RCLike.re ⟪X, Y⟫_𝕜 at h
    rw [RCLike.conj_re] at h
    exact h
  calc
    ‖X + Y‖ ^ 2 = RCLike.re ⟪X + Y, X + Y⟫_𝕜 := by
      exact InnerProductSpace.norm_sq_eq_re_inner (𝕜 := 𝕜) (X + Y)
    _ =
        RCLike.re
          (⟪X, X⟫_𝕜 + ⟪X, Y⟫_𝕜 + ⟪Y, X⟫_𝕜 + ⟪Y, Y⟫_𝕜) := by
      rw [inner_add_add_self]
    _ =
        ‖X‖ ^ 2 + RCLike.re ⟪X, Y⟫_𝕜 +
          RCLike.re ⟪Y, X⟫_𝕜 + ‖Y‖ ^ 2 := by
      simp
    _ = ‖X‖ ^ 2 + 2 * RCLike.re ⟪X, Y⟫_𝕜 + ‖Y‖ ^ 2 := by
      rw [hsym]
      ring
    _ ≤ ‖X‖ ^ 2 + 2 * (‖X‖ * ‖Y‖) + ‖Y‖ ^ 2 := by
      nlinarith [hre]
    _ = (‖X‖ + ‖Y‖) ^ 2 := by
      ring



theorem thm_12_2 {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (X Y : E) :
    ‖X + Y‖ ≤ ‖X‖ + ‖Y‖ :=
  (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).1
    (thm_12_2_squared_estimate (𝕜 := 𝕜) X Y)
