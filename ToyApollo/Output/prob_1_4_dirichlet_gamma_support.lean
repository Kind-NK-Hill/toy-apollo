/-
TASK ID: prob_1_4
TYPE: Problem
SOURCE PLAN: 39_chap1_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Support.DirichletGammaDensity

open MeasureTheory ProbabilityTheory Real BigOperators Finset
open scoped ENNReal BigOperators

theorem prob_1_4
    {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (n : ℕ) (hn : 0 < n) (G : IndependentGammaFamily Ω mu n) :
    HasLaw (fun omega => normalizedGammaVector G omega)
      (DirichletLaw G.shape G.scale) mu ∧
    HasLaw (fun omega => projectedNormalizedGammaVector G omega)
      (ProjectedDirichletLaw G.shape G.scale) mu ∧
    DirichletLaw G.shape G.scale (DirichletFullSimplex n) = 1 := by
  have hXlaw :
      ∀ i, HasLaw (fun omega => G.X omega i) (gammaScaleLaw (G.shape i) G.scale) mu := by
    intro i
    exact ⟨(G.measurable i).aemeasurable, G.gamma_law i⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [normalizedGammaVector] using
      independent_gamma_normalized_hasLaw_dirichlet mu G.shape G.scale
        (fun i omega => G.X omega i) hXlaw G.independent
  · simpa [projectedNormalizedGammaVector, normalizedGammaVector] using
      projected_normalized_hasLaw_projectedDirichlet mu G.shape G.scale
        (fun i omega => G.X omega i) hXlaw G.independent
  · exact DirichletLaw_simplex_probability_one hn G.shape G.shape_pos G.scale_pos

theorem prob_1_4_simplex
    {n : ℕ} (x : Fin (n - 1) → ℝ)
    (hx : ∀ i : Fin (n - 1), 0 ≤ x i)
    (hsum : ∑ i : Fin (n - 1), x i ≤ 1) :
    DirichletSimplex x := by
  refine ⟨hx, ?_⟩
  dsimp [simplexLastCoord]
  linarith
