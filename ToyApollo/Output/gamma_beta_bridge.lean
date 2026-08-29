import Mathlib

open MeasureTheory ProbabilityTheory Real Set

noncomputable section

open scoped BigOperators ENNReal NNReal

/-!
Retired Gamma/Beta density bridge.

Earlier Phase2 candidates used this module as a public axiom bridge. Current
official outputs prove the relevant law/density statements in task-owned or
shared support modules (`prob_1_3`, `ex_1_2_2_dirichlet_gamma_beta`, and
`ToyApollo.Support.DirichletGammaDensity`). This file keeps only historical
source-side definitions and exports no proof landings.
-/

/-- Source-side density for the sum of two independent same-scale Gamma variables. -/
noncomputable def gammaSumConvolutionDensity (α₁ α₂ β : ℝ) : ℝ → ℝ :=
  fun x => ∫ y in Ioo (0 : ℝ) x, gammaPDFReal α₁ β y * gammaPDFReal α₂ β (x - y)

/-- Source-side density for the ratio `X / (X + Y)` obtained from the Gamma joint density
under the change of variables `(u, s) ↦ (u*s, (1-u)*s)`. -/
noncomputable def gammaRatioTransformDensity (α₁ α₂ β : ℝ) : ℝ → ℝ :=
  fun u => ∫ s in Ioi (0 : ℝ),
    s * gammaPDFReal α₁ β (u * s) * gammaPDFReal α₂ β ((1 - u) * s)

/-- Normalizing constant in the Dirichlet density. -/
noncomputable def dirichletBridgeNormalizer {n : ℕ} (αs : Fin n → ℝ) : ℝ :=
  Gamma (∑ i, αs i) / ∏ i, Gamma (αs i)

/-- Last simplex coordinate determined by the first `n - 1` coordinates. -/
noncomputable def dirichletBridgeLastCoord {n : ℕ} (x : Fin (n - 1) → ℝ) : ℝ :=
  1 - ∑ i : Fin (n - 1), x i

/-- Source-side density obtained from normalizing `n` independent Gamma variables with a
common scale/rate parameter and retaining the first `n - 1` simplex coordinates. -/
noncomputable def dirichletGammaNormalizedDensity {n : ℕ} (αs : Fin n → ℝ) (β : ℝ) :
    (Fin (n - 1) → ℝ) → ℝ :=
  fun x =>
    if hn : 0 < n then
      ∫ s in Ioi (0 : ℝ),
        s ^ (n - 1) *
          (∏ i : Fin (n - 1),
            gammaPDFReal (αs ⟨i.val, by omega⟩) β (x i * s)) *
        gammaPDFReal (αs ⟨n - 1, by omega⟩) β
            (dirichletBridgeLastCoord x * s)
    else 0
