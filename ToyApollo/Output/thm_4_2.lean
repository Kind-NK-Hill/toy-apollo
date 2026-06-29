/-
TASK ID: thm_4_2
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Data.Set.Lattice

open Set

universe u v w

variable {Ω : Type u} {Ω' : Type v} {Ω'' : Type w} {I : Type _}
variable (f : Ω → Ω') (g : Ω' → Ω'') (A : Set Ω') (Ai : I → Set Ω') (B : Set Ω'')

theorem preimage_compl_distrib : f ⁻¹' (Aᶜ) = (f ⁻¹' A)ᶜ :=
  -- In Lean 4, x ∈ f ⁻¹' Aᶜ is definitionally (f x ∉ A),
  -- and x ∈ (f ⁻¹' A)ᶜ is also definitionally ¬(f x ∈ A).
  rfl

theorem preimage_iInter_distrib : f ⁻¹' (⋂ i, Ai i) = ⋂ i, f ⁻¹' (Ai i) := by
  ext x
  -- x ∈ f ⁻¹' (⋂ i, Ai i) ↔ f x ∈ ⋂ i, Ai i ↔ ∀ i, f x ∈ Ai i
  -- x ∈ ⋂ i, f ⁻¹' (Ai i) ↔ ∀ i, x ∈ f ⁻¹' (Ai i) ↔ ∀ i, f x ∈ Ai i
  simp only [mem_preimage, mem_iInter]

theorem preimage_iUnion_distrib : f ⁻¹' (⋃ i, Ai i) = ⋃ i, f ⁻¹' (Ai i) := by
  ext x
  -- x ∈ f ⁻¹' (⋃ i, Ai i) ↔ f x ∈ ⋃ i, Ai i ↔ ∃ i, f x ∈ Ai i
  -- x ∈ ⋃ i, f ⁻¹' (Ai i) ↔ ∃ i, x ∈ f ⁻¹' (Ai i) ↔ ∃ i, f x ∈ Ai i
  simp only [mem_preimage, mem_iUnion]

theorem preimage_comp_distrib (h : Ω → Ω'') (hw : h = g ∘ f) :
    h ⁻¹' B = f ⁻¹' (g ⁻¹' B) := by
  rw [hw]
  -- (g ∘ f) ⁻¹' B is definitionally equal to f ⁻¹' (g ⁻¹' B)
  rfl
