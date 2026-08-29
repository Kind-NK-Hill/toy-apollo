/-
TASK ID: thm_7_1
TYPE: Theorem_with_Proof
SOURCE PLAN: 25_chap7_ae_equality
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ComplexConjugate

namespace Thm71Support

lemma real_pos_neg_pointwise (x : ℝ) :
    |x| = (x.toNNReal : ℝ) + ((-x).toNNReal : ℝ) := by
  by_cases hx : 0 ≤ x
  · simp [Real.coe_toNNReal x hx, abs_of_nonneg hx, hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    simp [Real.coe_toNNReal (-x) (neg_nonneg.mpr hx'), abs_of_nonpos hx', hx']

lemma real_integral_triangle_spine {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : Integrable f μ) :
    |∫ ω, f ω ∂μ| ≤ ∫ ω, |f ω| ∂μ := by
  let p : Ω → ℝ := fun ω => (Real.toNNReal (f ω) : ℝ)
  let n : Ω → ℝ := fun ω => (Real.toNNReal (-f ω) : ℝ)
  have hp : Integrable p μ := by
    simpa [p] using hf.real_toNNReal
  have hn : Integrable n μ := by
    simpa [n] using hf.neg.real_toNNReal
  have hdecomp :
      ∫ ω, f ω ∂μ = (∫ ω, p ω ∂μ) - ∫ ω, n ω ∂μ := by
    simpa [p, n] using
      (integral_eq_integral_pos_part_sub_integral_neg_part hf)
  have habs_sum :
      ∫ ω, |f ω| ∂μ = (∫ ω, p ω ∂μ) + ∫ ω, n ω ∂μ := by
    calc
      ∫ ω, |f ω| ∂μ = ∫ ω, p ω + n ω ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => by
          exact real_pos_neg_pointwise (f ω)
      _ = (∫ ω, p ω ∂μ) + ∫ ω, n ω ∂μ := integral_add hp hn
  have hp_nonneg : 0 ≤ ∫ ω, p ω ∂μ :=
    integral_nonneg fun ω => by positivity
  have hn_nonneg : 0 ≤ ∫ ω, n ω ∂μ :=
    integral_nonneg fun ω => by positivity
  calc
    |∫ ω, f ω ∂μ| = |(∫ ω, p ω ∂μ) - ∫ ω, n ω ∂μ| := by rw [hdecomp]
    _ ≤ |∫ ω, p ω ∂μ| + |∫ ω, n ω ∂μ| := abs_sub _ _
    _ = (∫ ω, p ω ∂μ) + ∫ ω, n ω ∂μ := by
      rw [abs_of_nonneg hp_nonneg, abs_of_nonneg hn_nonneg]
    _ = ∫ ω, |f ω| ∂μ := habs_sum.symm

lemma unitRotation_norm {𝕜 : Type*} [RCLike 𝕜] (z : 𝕜) (hz : z ≠ 0) :
    ‖(starRingEnd 𝕜 z) / (‖z‖ : 𝕜)‖ = 1 := by
  rw [norm_div, RCLike.norm_conj, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg z), div_self (norm_ne_zero_iff.mpr hz)]

lemma unitRotation_mul {𝕜 : Type*} [RCLike 𝕜] (z : 𝕜) (hz : z ≠ 0) :
    ((starRingEnd 𝕜 z) / (‖z‖ : 𝕜)) * z = (‖z‖ : 𝕜) := by
  calc
    ((starRingEnd 𝕜 z) / (‖z‖ : 𝕜)) * z =
        (starRingEnd 𝕜 z * z) / (‖z‖ : 𝕜) := by ring
    _ = ((‖z‖ : 𝕜) ^ 2) / (‖z‖ : 𝕜) := by rw [RCLike.conj_mul]
    _ = (‖z‖ : 𝕜) := by field_simp [norm_ne_zero_iff.mpr hz]

lemma rclike_integral_triangle_spine {Ω 𝕜 : Type*} [MeasurableSpace Ω]
    [RCLike 𝕜] (μ : Measure Ω) (X : Ω → 𝕜) (hX : Integrable X μ) :
    ‖∫ ω, X ω ∂μ‖ ≤ ∫ ω, ‖X ω‖ ∂μ := by
  let z : 𝕜 := ∫ ω, X ω ∂μ
  change ‖z‖ ≤ ∫ ω, ‖X ω‖ ∂μ
  by_cases hz : z = 0
  · rw [hz, norm_zero]
    exact integral_nonneg fun ω => norm_nonneg (X ω)
  · let α : 𝕜 := (starRingEnd 𝕜 z) / (‖z‖ : 𝕜)
    have hαnorm : ‖α‖ = 1 := unitRotation_norm z hz
    have hαz : α * z = (‖z‖ : 𝕜) := unitRotation_mul z hz
    have hαX : Integrable (fun ω => α * X ω) μ := hX.const_mul α
    have hReInt :
        ∫ ω, RCLike.re (α * X ω) ∂μ = RCLike.re (α * z) := by
      calc
        ∫ ω, RCLike.re (α * X ω) ∂μ =
            RCLike.re (∫ ω, α * X ω ∂μ) := integral_re hαX
        _ = RCLike.re (α * z) := by rw [integral_const_mul]
    have hpoint : ∀ ω, RCLike.re (α * X ω) ≤ ‖X ω‖ := by
      intro ω
      calc
        RCLike.re (α * X ω) ≤ ‖α * X ω‖ := RCLike.re_le_norm _
        _ = ‖α‖ * ‖X ω‖ := norm_mul _ _
        _ = ‖X ω‖ := by rw [hαnorm, one_mul]
    have hmono :
        (∫ ω, RCLike.re (α * X ω) ∂μ) ≤ ∫ ω, ‖X ω‖ ∂μ :=
      integral_mono_ae hαX.re hX.norm (Filter.Eventually.of_forall hpoint)
    calc
      ‖z‖ = RCLike.re (α * z) := by rw [hαz, RCLike.ofReal_re]
      _ = ∫ ω, RCLike.re (α * X ω) ∂μ := hReInt.symm
      _ ≤ ∫ ω, ‖X ω‖ ∂μ := hmono

end Thm71Support

theorem thm_7_1 {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜] (μ : Measure Ω)
    (X : Ω → 𝕜) (_hX : Integrable X μ) :
    ‖∫ ω, X ω ∂μ‖ ≤ ∫ ω, ‖X ω‖ ∂μ := by
  exact Thm71Support.rclike_integral_triangle_spine μ X _hX
