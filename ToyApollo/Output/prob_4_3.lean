import Mathlib

open Set
open MeasureTheory

theorem prob_4_3 :
    ∃ (Ω : Type) (m : MeasurableSpace Ω) (_μ : Measure Ω) (f : Ω → ℝ),
      ¬ @Measurable Ω ℝ m (borel ℝ) f ∧
        @Measurable Ω ℝ m (borel ℝ) (fun ω => |f ω|) := by
  let m : MeasurableSpace Bool :=
    { MeasurableSet' := fun s => s = ∅ ∨ s = univ
      measurableSet_empty := Or.inl rfl
      measurableSet_compl := by
        intro s hs
        rcases hs with rfl | rfl <;> simp
      measurableSet_iUnion := by
        intro g hg
        by_cases h : ∀ n, g n = ∅
        · left
          ext x
          simp [h]
        · push_neg at h
          rcases h with ⟨n, hn⟩
          have h_univ : g n = univ := by
            rcases hg n with h0 | h1
            · exfalso
              simp [h0] at hn
            · exact h1
          right
          ext x
          constructor
          · intro _
            simp
          · intro _
            refine mem_iUnion.2 ?_
            exact ⟨n, by simp [h_univ]⟩ }
  refine ⟨Bool, m, 0, fun b => if b then (1 : ℝ) else -1, ?_⟩
  constructor
  · intro hf
    have hpre :
        (fun b : Bool => if b then (1 : ℝ) else -1) ⁻¹' ({1} : Set ℝ) = ({true} : Set Bool) := by
      ext b
      cases b <;> norm_num
    have hset :
        @MeasurableSet Bool m (((fun b : Bool => if b then (1 : ℝ) else -1) ⁻¹' ({1} : Set ℝ))) :=
      hf (MeasurableSet.singleton 1)
    rw [hpre] at hset
    unfold MeasurableSet at hset
    simp [m] at hset
    have hfalse : (false : Bool) ∈ ({true} : Set Bool) := by
      rw [hset]
      simp
    simp at hfalse
  · have habs : (fun ω : Bool => |(if ω then (1 : ℝ) else -1)|) = fun _ => (1 : ℝ) := by
      funext b
      cases b <;> norm_num
    rw [habs]
    exact measurable_const
