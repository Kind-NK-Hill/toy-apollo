import Mathlib

open MeasureTheory Filter
open scoped Topology

/-- A reusable generator-extension bridge for real-valued vector measures on
`ℝ`: equality on all closed intervals implies equality on all Borel sets.

This is the theorem-level replacement for π-λ/generator extension steps that
are independent of a task-specific density calculation. -/
theorem phase2_vectorMeasure_ext_of_Icc
    (v w : VectorMeasure ℝ ℝ)
    (hIcc : ∀ a b : ℝ, a ≤ b → v (Set.Icc a b) = w (Set.Icc a b)) :
    v = w := by
  classical
  let K : ℕ → Set ℝ := fun n => Set.Icc (-(n : ℝ)) (n : ℝ)
  have hK_mono : Monotone K := by
    intro n m hnm x hx
    dsimp [K] at hx ⊢
    constructor
    · have hnle : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      linarith [hx.1, hnle]
    · have hnle : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      linarith [hx.2, hnle]
  have hK_meas : ∀ n, MeasurableSet (K n) := fun _ => measurableSet_Icc
  have hK_univ : (⋃ n, K n) = (Set.univ : Set ℝ) := by
    ext x
    constructor
    · intro _; trivial
    · intro _
      rcases exists_nat_ge |x| with ⟨n, hn⟩
      refine Set.mem_iUnion.2 ⟨n, ?_⟩
      dsimp [K]
      constructor
      · have hxneg : -((n : ℝ)) ≤ -|x| := by linarith
        exact hxneg.trans (neg_abs_le x)
      · exact (le_abs_self x).trans hn
  have hUniv : v (Set.univ : Set ℝ) = w (Set.univ : Set ℝ) := by
    have hv :=
      VectorMeasure.tendsto_vectorMeasure_iUnion_atTop_nat
        (v := v) hK_mono hK_meas
    have hw :=
      VectorMeasure.tendsto_vectorMeasure_iUnion_atTop_nat
        (v := w) hK_mono hK_meas
    rw [hK_univ] at hv hw
    have hseq : (fun n => v (K n)) = fun n => w (K n) := by
      funext n
      have hn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
      exact hIcc (-(n : ℝ)) (n : ℝ) (by linarith)
    exact tendsto_nhds_unique hv (hseq ▸ hw)
  refine VectorMeasure.ext ?_
  intro S hS
  let C : ∀ s : Set ℝ, MeasurableSet s → Prop := fun s _ => v s = w s
  exact MeasurableSpace.induction_on_inter
    (m := (inferInstance : MeasurableSpace ℝ))
    (C := C)
    (s := {S : Set ℝ | ∃ a b : ℝ, a ≤ b ∧ Set.Icc a b = S})
    (borel_eq_generateFrom_Icc ℝ)
    (isPiSystem_Icc id id)
    (by simp [C])
    (by
      intro t ht
      rcases ht with ⟨a, b, hab, rfl⟩
      exact hIcc a b hab)
    (by
      intro t htm ht
      dsimp [C] at ht ⊢
      rw [VectorMeasure.of_compl (v := v) htm,
        VectorMeasure.of_compl (v := w) htm]
      rw [ht, hUniv])
    (by
      intro f hdisj hfm hf
      dsimp [C] at hf ⊢
      rw [VectorMeasure.of_disjoint_iUnion (v := v) hfm hdisj,
        VectorMeasure.of_disjoint_iUnion (v := w) hfm hdisj]
      exact tsum_congr hf)
    S hS
