/-
TASK ID: ex_4_4_3
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

noncomputable def rotatedComplexPoint (θ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((θ : ℂ) * Complex.I) * z

noncomputable def standardComplexGaussianPdf (z : ℂ) : ℝ :=
  (1 / Real.pi) * Real.exp (-(‖z‖ ^ 2))

theorem standardComplexGaussianPdf_rotation_invariant (θ : ℝ) (z : ℂ) :
    standardComplexGaussianPdf (rotatedComplexPoint θ z) = standardComplexGaussianPdf z := by
  rw [standardComplexGaussianPdf, standardComplexGaussianPdf]
  congr 1
  have hnorm : ‖rotatedComplexPoint θ z‖ = ‖z‖ := by
    simp [rotatedComplexPoint]
  rw [hnorm]

def standardComplexGaussianVariance : ℝ := 1

theorem standardComplexGaussianVariance_eq_one :
    standardComplexGaussianVariance = 1 := rfl

theorem ex_4_4_3 :
    standardComplexGaussianVariance = 1 ∧
      ∀ θ : ℝ, ∀ z : ℂ,
        standardComplexGaussianPdf (rotatedComplexPoint θ z) = standardComplexGaussianPdf z := by
  refine ⟨standardComplexGaussianVariance_eq_one, ?_⟩
  intro θ z
  exact standardComplexGaussianPdf_rotation_invariant θ z
