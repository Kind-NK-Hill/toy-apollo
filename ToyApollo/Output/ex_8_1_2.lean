/-
TASK ID: ex_8_1_2
TYPE: Example_Proof
SOURCE PLAN: 31_chap8_coupling
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open Set

noncomputable def gaussianAffineTransport (μ₁ μ₂ σ₁ σ₂ : ℝ) : ℝ → ℝ :=
  fun x => (σ₂ / σ₁) * (x - μ₁) + μ₂

noncomputable def boxMullerGaussianX (μ₁ σ₁ : ℝ) : ℝ × ℝ → ℝ :=
  fun p => μ₁ + σ₁ * Real.sqrt (-2 * Real.log p.1) * Real.cos (2 * Real.pi * p.2)

noncomputable def boxMullerGaussianY (μ₂ σ₂ : ℝ) : ℝ × ℝ → ℝ :=
  fun p => μ₂ + σ₂ * Real.sqrt (-2 * Real.log p.1) * Real.sin (2 * Real.pi * p.2)

structure GaussianCouplingExample where
  μ₁ : ℝ
  μ₂ : ℝ
  σ₁ : ℝ
  σ₂ : ℝ
  sigma1_pos : 0 < σ₁
  sigma2_pos : 0 < σ₂
  deterministicTransport : ℝ → ℝ
  deterministicTransport_formula :
    ∀ x : ℝ, deterministicTransport x = gaussianAffineTransport μ₁ μ₂ σ₁ σ₂ x
  unitSquare : Set (ℝ × ℝ)
  unitSquare_eq : unitSquare = Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  coupledX : ℝ × ℝ → ℝ
  coupledY : ℝ × ℝ → ℝ
  coupledX_formula : ∀ p : ℝ × ℝ, coupledX p = boxMullerGaussianX μ₁ σ₁ p
  coupledY_formula : ∀ p : ℝ × ℝ, coupledY p = boxMullerGaussianY μ₂ σ₂ p

noncomputable def ex_8_1_2 (μ₁ μ₂ σ₁ σ₂ : ℝ) (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂) :
    GaussianCouplingExample where
  μ₁ := μ₁
  μ₂ := μ₂
  σ₁ := σ₁
  σ₂ := σ₂
  sigma1_pos := hσ₁
  sigma2_pos := hσ₂
  deterministicTransport := gaussianAffineTransport μ₁ μ₂ σ₁ σ₂
  deterministicTransport_formula := by
    intro x
    rfl
  unitSquare := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  unitSquare_eq := rfl
  coupledX := boxMullerGaussianX μ₁ σ₁
  coupledY := boxMullerGaussianY μ₂ σ₂
  coupledX_formula := by
    intro p
    rfl
  coupledY_formula := by
    intro p
    rfl
