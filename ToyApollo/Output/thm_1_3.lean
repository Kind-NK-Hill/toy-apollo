/-
TASK ID: thm_1_3
TYPE: Theorem_with_Proof
SOURCE PLAN: 38_chap1_riemann_stieltjes
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_1_2

-- WRITE FINAL LEAN CODE BELOW

noncomputable section

theorem thm_1_3_tagged_sum_decomposition {a b : ℝ}
    (P : DarbouxRS.Partition a b) (tags : Fin P.n → ℝ) (f α₁ α₂ : ℝ → ℝ) :
    DarbouxRS.taggedSum P tags f (fun x => α₁ x + α₂ x) =
      DarbouxRS.taggedSum P tags f α₁ + DarbouxRS.taggedSum P tags f α₂ := by
  exact DarbouxRS.taggedSum_integrator_add P tags f α₁ α₂

theorem thm_1_3 {f α₁ α₂ : ℝ → ℝ} {a b : ℝ}
    (h₁ : RSIntegrable f α₁ a b)
    (h₂ : RSIntegrable f α₂ a b) :
    ∃ hsum : RSIntegrable f (fun x => α₁ x + α₂ x) a b,
      rsIntegral f (fun x => α₁ x + α₂ x) a b hsum =
        rsIntegral f α₁ a b h₁ + rsIntegral f α₂ a b h₂ := by
  exact ⟨rsIntegrable_integrator_add h₁ h₂, rsIntegral_integrator_add h₁ h₂⟩
