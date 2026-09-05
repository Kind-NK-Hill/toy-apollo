/-
TASK ID: ex_3_1_3
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_03.def_3_2
import ProbabilityTheory.chapter_03.ex_3_1_1
import ProbabilityTheory.chapter_03.thm_3_1
import ProbabilityTheory.chapter_03.def_3_3
import ProbabilityTheory.chapter_03.def_3_1
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite




open MeasureTheory Set ENNReal

 
theorem nat_union_singletons_eq_univ : (⋃ (i : ℕ), ({i} : Set ℕ)) = univ := by
  ext x
  simp only [mem_iUnion, mem_singleton_iff, mem_univ, iff_true]
  exact ⟨x, rfl⟩

 
theorem counting_measure_nat_singleton_finite (i : ℕ) : Measure.count ({i} : Set ℕ) < ⊤ := by
  rw [Measure.count_apply (measurableSet_singleton i)]
  simp [encard_singleton, one_lt_top]

 
noncomputable def countingPremeasureNat : Premeasure F_nat where
  μ₀ := fun s => counting_μ₀ s.val
  map_empty := by
    unfold counting_μ₀
    simp only [mem_empty_iff_false, ↓if_false, tsum_zero]
  sigma_additive := by
    intro A hA hU h_disj
    unfold counting_μ₀
    rw [ENNReal.tsum_comm]
    congr
    ext x
    open Classical in
    by_cases hx : x ∈ ⋃ i, A i
    · rw [if_pos hx]
      rcases mem_iUnion.mp hx with ⟨k, hk⟩
      rw [tsum_eq_single k]
      · rw [if_pos hk]
      · intro j hj
        have : x ∉ A j := fun h_in => (h_disj hj.symm).le_bot ⟨hk, h_in⟩
        rw [if_neg this]
    · rw [if_neg hx]
      have h_none : ∀ i, x ∉ A i := fun i h_in => hx (mem_iUnion.mpr ⟨i, h_in⟩)
      simp [h_none]

 
theorem counting_μ₀_eq_count_top (s : Set ℕ) : counting_μ₀ s = (@Measure.count ℕ ⊤) s := by
  rw [Measure.count_apply (α := ℕ) (s := s) (by trivial)]
  calc
    counting_μ₀ s = ∑' x, Set.indicator s (fun _ => (1 : ℝ≥0∞)) x := by
      unfold counting_μ₀
      simp [Set.indicator]
    _ = ∑' _ : s, (1 : ℝ≥0∞) := by
      exact (tsum_subtype s (fun _ => (1 : ℝ≥0∞))).symm
    _ = s.encard := ENNReal.tsum_set_one (s := s)

 
theorem countingPremeasureNat_sigmaFinite : IsSigmaFinite countingPremeasureNat := by
  refine ⟨fun i => ({i} : Set ℕ), fun i => Or.inl (finite_singleton i), ?_, ?_⟩
  · simpa using nat_union_singletons_eq_univ
  · intro i
    change counting_μ₀ ({i} : Set ℕ) < ⊤
    rw [counting_μ₀_eq_count_top]
    rw [Measure.count_apply (α := ℕ) (s := ({i} : Set ℕ)) (by trivial)]
    simp [encard_singleton, one_lt_top]

 
theorem generateFrom_F_nat_eq_top :
    MeasurableSpace.generateFrom F_nat.carrier = (⊤ : MeasurableSpace ℕ) := by
  let m : MeasurableSpace ℕ := MeasurableSpace.generateFrom F_nat.carrier
  letI : @MeasurableSingletonClass ℕ m := ⟨fun n => by
    exact MeasurableSpace.measurableSet_generateFrom (by exact Or.inl (finite_singleton n))⟩
  ext s
  constructor
  · intro _
    trivial
  · intro _
    change @MeasurableSet ℕ m s
    exact s.to_countable.measurableSet



theorem counting_measure_extends_example_3_1_1 :
    IsSigmaFinite countingPremeasureNat ∧
      MeasurableSpace.generateFrom F_nat.carrier = (⊤ : MeasurableSpace ℕ) ∧
      ∀ s : Set ℕ, (@Measure.count ℕ ⊤) s = counting_μ₀ s := by
  refine ⟨countingPremeasureNat_sigmaFinite, generateFrom_F_nat_eq_top, ?_⟩
  intro s
  rw [counting_μ₀_eq_count_top]

 
instance : SigmaFinite (Measure.count : Measure ℕ) where
  out' := ⟨{
    set := fun i => ({i} : Set ℕ),
    set_mem := fun i => mem_univ ({i} : Set ℕ),
    finite := fun i => counting_measure_nat_singleton_finite i,
    spanning := nat_union_singletons_eq_univ
  }⟩
