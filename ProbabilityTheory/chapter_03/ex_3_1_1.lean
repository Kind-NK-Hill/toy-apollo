/-
TASK ID: ex_3_1_1
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_03.def_3_1
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic




open Set ENNReal Function

 
noncomputable def counting_μ₀ {Ω : Type*} (E : Set Ω) : ℝ≥0∞ :=
  open Classical in ∑' (x : Ω), if x ∈ E then 1 else 0

 
def finiteCofiniteAlgebra : Set (Set ℕ) :=
  { s | s.Finite ∨ sᶜ.Finite }

 
def F_nat : FieldOfSets ℕ where
  carrier := finiteCofiniteAlgebra
  empty_mem := Or.inl finite_empty
  compl_mem s h := by
    cases h with
    | inl hf => apply Or.inr; rwa [compl_compl]
    | inr hcf => exact Or.inl hcf
  union_mem s t hs ht := by
    cases hs with
    | inl hsf =>
      cases ht with
      | inl htf => exact Or.inl (hsf.union htf)
      | inr htc => 
        apply Or.inr
        rw [compl_union]
        exact htc.subset (fun _ h => h.2)
    | inr hsc => 
      apply Or.inr
      rw [compl_union]
      exact hsc.subset (fun _ h => h.1)



theorem counting_premeasure_on_non_sigma_algebra :
    (∃ (μ : Premeasure F_nat), ∀ s, μ.μ₀ s = counting_μ₀ s.val) ∧
    ¬ (∀ (f : ℕ → Set ℕ), (∀ n, f n ∈ F_nat.carrier) → (⋃ n, f n) ∈ F_nat.carrier) := by
  constructor
  · -- Part 1: μ₀ is a valid pre-measure.
    let μ : Premeasure F_nat := {
      μ₀ := fun s => counting_μ₀ s.val,
      map_empty := by
        unfold counting_μ₀
        simp only [mem_empty_iff_false, ↓if_false, tsum_zero],
      sigma_additive := fun A hA hU h_disj => by
        unfold counting_μ₀
        -- Swap the infinite sums (Tonelli for counting measures on ℝ≥0∞).
        rw [ENNReal.tsum_comm]
        congr; ext x
        open Classical in
        by_cases hx : x ∈ ⋃ i, A i
        · rw [if_pos hx]
          -- Since sets are pairwise disjoint, x is in exactly one A k.
          rcases mem_iUnion.mp hx with ⟨k, hk⟩
          rw [tsum_eq_single k]
          · rw [if_pos hk]
          · intro j hj
            have : x ∉ A j := fun h_in => (h_disj hj.symm).le_bot ⟨hk, h_in⟩
            rw [if_neg this]
        · rw [if_neg hx]
          -- x is not in any of the sets A i.
          have h_none : ∀ i, x ∉ A i := fun i h_in => hx (mem_iUnion.mpr ⟨i, h_in⟩)
          simp [h_none]
    }
    exact ⟨μ, fun s => rfl⟩

  · -- Part 2: F_nat is not a σ-algebra.
    let f : ℕ → Set ℕ := fun n => {2 * n}
    intro h_sigma
    -- Each set f(n) = {2n} is in the algebra because singletons are finite.
    have hf : ∀ n, f n ∈ F_nat.carrier := fun n => Or.inl (finite_singleton (2 * n))
    let U := iUnion f
    -- If it were a σ-algebra, the union U must be in the algebra.
    have hU_mem : U ∈ F_nat.carrier := h_sigma f hf
    -- U is the set of even numbers.
    have hU_range : U = range (fun n => 2 * n) := by
      ext x; simp [U, f]
    
    -- Contradiction: the set of even numbers is neither finite nor co-finite.
    rcases hU_mem with h_fin | h_cfin
    · -- Case 1: U is finite. Contradiction.
      have h_inf : U.Infinite := by
        rw [hU_range]
        apply Set.infinite_range_of_injective
        exact fun m n h => Nat.mul_left_cancel (by norm_num : 0 < 2) h
      exact h_inf h_fin
    · -- Case 2: Uᶜ is finite. Contradiction.
      -- Uᶜ contains all odd numbers, hence it's infinite.
      let g : ℕ → ℕ := fun n => 2 * n + 1
      have h_sub : range g ⊆ Uᶜ := by
        rintro x ⟨k, rfl⟩ h_in_U
        rw [hU_range] at h_in_U
        rcases h_in_U with ⟨n, h_eq⟩
        -- Use parity to show 2*n = 2*k + 1 is impossible.
        have h_mod : (2 * n) % 2 = (2 * k + 1) % 2 := congr_arg (· % 2) h_eq
        simp [Nat.mul_mod_left, Nat.add_mod] at h_mod
      have h_g_inf : (range g).Infinite := by
        apply Set.infinite_range_of_injective
        intro m n h
        have h1 : 2 * m + 1 = 2 * n + 1 := h
        have h2 : 2 * m = 2 * n := Nat.add_right_cancel h1
        exact Nat.mul_left_cancel (by norm_num : 0 < 2) h2
      exact h_g_inf (h_cfin.subset h_sub)
