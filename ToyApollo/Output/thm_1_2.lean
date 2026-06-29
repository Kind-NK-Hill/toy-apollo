/-
TASK ID: thm_1_2
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_1_2
import ToyApollo.Output.rs_stieltjes_bridge

open Set

noncomputable section

theorem thm_1_2 {f g α : ℝ → ℝ} {c a b : ℝ} :
    (∀ (hf : RSIntegrable f α a b) (hg : RSIntegrable g α a b),
      ∃ hfg : RSIntegrable (fun x => f x + g x) α a b,
        rsIntegral (fun x => f x + g x) α a b hfg =
          rsIntegral f α a b hf + rsIntegral g α a b hg) ∧
    (∀ (hf : RSIntegrable f α a b),
      ∃ hcf : RSIntegrable (fun x => c * f x) α a b,
        rsIntegral (fun x => c * f x) α a b hcf =
          c * rsIntegral f α a b hf) ∧
    (∀ (hf : RSIntegrable f α a b) (hg : RSIntegrable g α a b),
      (∀ x ∈ Icc a b, f x ≤ g x) →
        rsIntegral f α a b hf ≤ rsIntegral g α a b hg) ∧
    (∀ {d : ℝ}, a < d → d < b →
      ∀ (hleft : RSIntegrable f α a d) (hright : RSIntegrable f α d b),
        ∃ hab : RSIntegrable f α a b,
          rsIntegral f α a b hab =
            rsIntegral f α a d hleft + rsIntegral f α d b hright) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hf hg
    exact ⟨rsIntegrable_add hf hg, rsIntegral_add hf hg⟩
  · intro hf
    exact ⟨rsIntegrable_const_mul (c := c) hf, rsIntegral_const_mul (c := c) hf⟩
  · intro hf hg hfg
    exact rsIntegral_mono hf hg hfg
  · intro d had hdb hleft hright
    exact ⟨rsIntegrable_interval_concat had hdb hleft hright,
      rsIntegral_interval_concat had hdb hleft hright⟩
