/-
TASK ID: prob_2_4
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_02.def_2_5
import ProbabilityTheory.chapter_02.thm_2_3
import ProbabilityTheory.chapter_02.thm_2_4

open MeasureTheory Set Finset



theorem prob_2_4_finset_union_bound {α : Type _} [MeasurableSpace α]
    (μ : Measure α) {ι : Type _} (s : Finset ι) (A : ι → Set α)
    (hA : ∀ i, MeasurableSet (A i)) :
    μ (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, μ (A i) := by
  classical
  refine Finset.induction_on s ?empty ?insert
  · simp
  · intro a s has ih
    have hunion : (⋃ i ∈ insert a s, A i) = A a ∪ ⋃ i ∈ s, A i := by
      ext x
      simp
    have h_tail : MeasurableSet (⋃ i ∈ s, A i) :=
      Finset.measurableSet_biUnion s (fun i _hi => hA i)
    calc
      μ (⋃ i ∈ insert a s, A i) = μ (A a ∪ ⋃ i ∈ s, A i) := by rw [hunion]
      _ ≤ μ (A a) + μ (⋃ i ∈ s, A i) :=
        thm_2_3 μ (A := A a) (B := ⋃ i ∈ s, A i) (hA a) h_tail
      _ ≤ μ (A a) + ∑ i ∈ s, μ (A i) := add_le_add le_rfl ih
      _ = ∑ i ∈ insert a s, μ (A i) := by
        simp [has]

theorem prob_2_4 {α : Type _} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    (∀ (n : ℕ) (A : Fin n → Set α), (∀ i, MeasurableSet (A i)) → μ (⋃ i, A i) ≤ ∑ i, μ (A i)) ∧
    (∀ (A : ℕ → Set α), (∀ i, MeasurableSet (A i)) → μ (⋃ i, A i) ≤ ∑' i, μ (A i)) := by
  refine ⟨?finite, ?countable⟩
  · intro n A hA
    simpa using
      (prob_2_4_finset_union_bound μ (Finset.univ : Finset (Fin n)) A hA)
  · intro A hAmeas
    let U : ℕ → Set α := fun n => ⋃ i ∈ Finset.range (n + 1), A i
    have hUinc : SetSeqIncreasing U := by
      change Monotone U
      intro m n hmn
      intro x hx
      rcases mem_iUnion.mp hx with ⟨i, hi⟩
      rcases mem_iUnion.mp hi with ⟨hi_range, hxi⟩
      refine mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨?_, hxi⟩⟩
      exact Finset.mem_range.mpr (by
        have hi : i < m + 1 := Finset.mem_range.mp hi_range
        omega)
    have hUmeas : ∀ n, MeasurableSet (U n) := by
      intro n
      exact Finset.measurableSet_biUnion (Finset.range (n + 1)) (fun i _hi => hAmeas i)
    have hUnion : (⋃ n, U n) = ⋃ i, A i := by
      ext x
      constructor
      · intro hx
        rcases mem_iUnion.mp hx with ⟨n, hn⟩
        rcases mem_iUnion.mp hn with ⟨i, hi⟩
        rcases mem_iUnion.mp hi with ⟨_hi_range, hxi⟩
        exact mem_iUnion.mpr ⟨i, hxi⟩
      · intro hx
        rcases mem_iUnion.mp hx with ⟨i, hxi⟩
        refine mem_iUnion.mpr ⟨i, ?_⟩
        refine mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨?_, hxi⟩⟩
        simp
    have hfinite_bound :
        ∀ n, μ (U n) ≤ ∑ i ∈ Finset.range (n + 1), μ (A i) := by
      intro n
      exact prob_2_4_finset_union_bound μ (Finset.range (n + 1)) A hAmeas
    have hpartial_le_tsum : ∀ n, μ (U n) ≤ ∑' i, μ (A i) := by
      intro n
      exact (hfinite_bound n).trans (ENNReal.sum_le_tsum (Finset.range (n + 1)))
    calc
      μ (⋃ i, A i) = μ (⋃ n, U n) := by rw [hUnion]
      _ = ⨆ n, μ (U n) := thm_2_4 μ U hUinc hUmeas
      _ ≤ ∑' i, μ (A i) := iSup_le hpartial_le_tsum
