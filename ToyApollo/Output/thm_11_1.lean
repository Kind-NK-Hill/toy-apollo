/-
TASK ID: thm_11_1
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter11-bounds-inequalities
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped InnerProductSpace

theorem thm_11_1 {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (X Y : E) :
    ‖⟪X, Y⟫_𝕜‖ ≤ ‖X‖ * ‖Y‖ := by
  exact norm_inner_le_norm X Y

theorem thm_11_1_equality_iff {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {X Y : E} (hX : X ≠ 0) (hY : Y ≠ 0) :
    ‖⟪X, Y⟫_𝕜‖ = ‖X‖ * ‖Y‖ ↔ ∃ c : 𝕜, c ≠ 0 ∧ Y = c • X := by
  exact norm_inner_eq_norm_iff hX hY

theorem thm_11_1_equality_zero {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (Y : E) :
    ‖⟪(0 : E), Y⟫_𝕜‖ = ‖(0 : E)‖ * ‖Y‖ := by
  simp

theorem thm_11_1_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X Y : E) : |⟪X, Y⟫_ℝ| ≤ ‖X‖ * ‖Y‖ := by
  exact abs_real_inner_le_norm X Y

theorem thm_11_1_integrable_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Integrable (fun ω => X ω * Y ω) μ :=
  hX.integrable_mul hY

theorem thm_11_1_quadratic_nonneg {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (t : ℝ) :
    0 ≤ (∫ ω, X ω ^ 2 ∂μ) * (t * t)
        + (2 * ∫ ω, X ω * Y ω ∂μ) * t + (∫ ω, Y ω ^ 2 ∂μ) := by
  have hX2 : Integrable (fun ω => X ω ^ 2) μ :=
    (hX.integrable_mul hX).congr (by filter_upwards with ω; simp [Pi.mul_apply, pow_two])
  have hY2 : Integrable (fun ω => Y ω ^ 2) μ :=
    (hY.integrable_mul hY).congr (by filter_upwards with ω; simp [Pi.mul_apply, pow_two])
  have hXY : Integrable (fun ω => X ω * Y ω) μ := hX.integrable_mul hY
  have hnn : 0 ≤ ∫ ω, (t * X ω + Y ω) ^ 2 ∂μ :=
    integral_nonneg (fun ω => sq_nonneg _)
  have hexp : (∫ ω, (t * X ω + Y ω) ^ 2 ∂μ)
      = (∫ ω, X ω ^ 2 ∂μ) * (t * t)
        + (2 * ∫ ω, X ω * Y ω ∂μ) * t + (∫ ω, Y ω ^ 2 ∂μ) := by
    have hpt : (fun ω => (t * X ω + Y ω) ^ 2)
        = (fun ω => (t * t) * X ω ^ 2 + (2 * t) * (X ω * Y ω) + Y ω ^ 2) := by
      funext ω; ring
    have e1 : Integrable (fun ω => (t * t) * X ω ^ 2) μ := hX2.const_mul _
    have e2 : Integrable (fun ω => (2 * t) * (X ω * Y ω)) μ := hXY.const_mul _
    have e12 : Integrable
        (fun ω => (t * t) * X ω ^ 2 + (2 * t) * (X ω * Y ω)) μ := e1.add e2
    rw [hpt, integral_add e12 hY2, integral_add e1 e2,
      integral_const_mul, integral_const_mul]
    ring
  rw [hexp] at hnn
  exact hnn

theorem thm_11_1_expectation {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    |∫ ω, X ω * Y ω ∂μ|
      ≤ Real.sqrt (∫ ω, X ω ^ 2 ∂μ) * Real.sqrt (∫ ω, Y ω ^ 2 ∂μ) := by
  have ha : 0 ≤ ∫ ω, X ω ^ 2 ∂μ := integral_nonneg (fun ω => sq_nonneg _)
  have hd : discrim (∫ ω, X ω ^ 2 ∂μ) (2 * ∫ ω, X ω * Y ω ∂μ) (∫ ω, Y ω ^ 2 ∂μ) ≤ 0 :=
    discrim_le_zero (thm_11_1_quadratic_nonneg hX hY)
  have hsq : (∫ ω, X ω * Y ω ∂μ) ^ 2
      ≤ (∫ ω, X ω ^ 2 ∂μ) * (∫ ω, Y ω ^ 2 ∂μ) := by
    have hdd : (2 * ∫ ω, X ω * Y ω ∂μ) ^ 2
        - 4 * (∫ ω, X ω ^ 2 ∂μ) * (∫ ω, Y ω ^ 2 ∂μ) ≤ 0 := by
      simpa [discrim] using hd
    nlinarith [hdd]
  rw [← Real.sqrt_mul ha, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hsq
