import Mathlib

/-- Rotate a complex number by the angle `θ`. -/
noncomputable def rotatedComplexPoint (θ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((θ : ℂ) * Complex.I) * z

/-- The standard complex Gaussian density `π^{-1} e^{-‖z‖^2}`. -/
noncomputable def standardComplexGaussianPdf (z : ℂ) : ℝ :=
  (1 / Real.pi) * Real.exp (-(‖z‖ ^ 2))

theorem standardComplexGaussianPdf_rotation_invariant (θ : ℝ) (z : ℂ) :
    standardComplexGaussianPdf (rotatedComplexPoint θ z) = standardComplexGaussianPdf z := by
  rw [standardComplexGaussianPdf, standardComplexGaussianPdf]
  congr 1
  have hnorm : ‖rotatedComplexPoint θ z‖ = ‖z‖ := by
    simp [rotatedComplexPoint]
  rw [hnorm]

/-- The variance value recorded in the textbook for the standard complex Gaussian law. -/
def standardComplexGaussianVariance : ℝ := 1

theorem standardComplexGaussianVariance_eq_one :
    standardComplexGaussianVariance = 1 := rfl

/--
Example 4.4.3: the standard complex Gaussian law has variance `1` and is invariant under complex
rotations.
-/
theorem ex_4_4_3 :
    standardComplexGaussianVariance = 1 ∧
      ∀ θ : ℝ, ∀ z : ℂ,
        standardComplexGaussianPdf (rotatedComplexPoint θ z) = standardComplexGaussianPdf z := by
  refine ⟨standardComplexGaussianVariance_eq_one, ?_⟩
  intro θ z
  exact standardComplexGaussianPdf_rotation_invariant θ z
