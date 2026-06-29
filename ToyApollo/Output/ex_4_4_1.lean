import Mathlib

open Set

/-- The radius cdf for a point uniformly distributed in the complex unit disc. -/
noncomputable def unitDiscRadiusCdf (r : ℝ) : ℝ :=
  if r < 0 then 0 else if r ≤ 1 then r ^ 2 else 1

/-- The angle cdf for a uniform argument on `[0, 2π]`. -/
noncomputable def unitDiscAngleCdf (θ : ℝ) : ℝ :=
  if θ < 0 then 0 else if θ ≤ 2 * Real.pi then θ / (2 * Real.pi) else 1

theorem unitDiscRadiusCdf_on_unit_interval {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    unitDiscRadiusCdf r = r ^ 2 := by
  have hr_nonneg : ¬ r < 0 := not_lt.mpr hr.1
  have hr_le_one : r ≤ 1 := hr.2
  simp [unitDiscRadiusCdf, hr_nonneg, hr_le_one]

theorem unitDiscAngleCdf_on_support {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    unitDiscAngleCdf θ = θ / (2 * Real.pi) := by
  have hθ_nonneg : ¬ θ < 0 := not_lt.mpr hθ.1
  have hθ_le : θ ≤ 2 * Real.pi := hθ.2
  simp [unitDiscAngleCdf, hθ_nonneg, hθ_le]

/--
Example 4.4.1: for a uniform point in the unit disc, the radius has cdf `r^2` on `[0,1]` and
the argument is uniform on `[0, 2π]`.
-/
theorem ex_4_4_1 :
    (∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 → unitDiscRadiusCdf r = r ^ 2) ∧
      ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) → unitDiscAngleCdf θ = θ / (2 * Real.pi) := by
  refine ⟨?_, ?_⟩
  · intro r hr
    exact unitDiscRadiusCdf_on_unit_interval hr
  · intro θ hθ
    exact unitDiscAngleCdf_on_support hθ
