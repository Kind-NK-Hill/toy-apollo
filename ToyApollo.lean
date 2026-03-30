import Mathlib.Tactic
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Rat.Denumerable
import Mathlib.Logic.Denumerable

noncomputable section

open Classical Rat Set ENNReal

def I : Set ℝ := Icc 0 1

def IsVitaliMeasure (m : Set ℝ → ENNReal) : Prop :=
  (∀ A, ¬(A ⊆ I) → m A = 0) ∧
  (m ∅ = 0) ∧
  (∀ A B, A ⊆ I → B ⊆ I → A ⊆ B → m A ≤ m B) ∧
  (∀ f : ℕ → Set ℝ, (∀ n, f n ⊆ I) → Pairwise (fun i j => Disjoint (f i) (f j)) → m (⋃ n, f n) = ∑' n, m (f n)) ∧
  (∀ A, A ⊆ I → ∀ d : ℝ, m ((fun x => Int.fract (x + d)) '' A) = m A) ∧
  (∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 → m (Icc a b) = ENNReal.ofReal (b - a))

variable (VitaliSet : Set ℝ)
variable (VitaliSeq : ℕ → Set ℝ)
variable (vitali_covers_Ico : Ico 0 1 ⊆ ⋃ n, VitaliSeq n)
variable (vitali_seq_disjoint : Pairwise (fun i j => Disjoint (VitaliSeq i) (VitaliSeq j)))
variable (measure_vitali_invariant : ∀ (m : Set ℝ → ENNReal), IsVitaliMeasure m → ∀ n, m (VitaliSeq n) = m VitaliSet)
variable (sum_vitali_eq_union : ∀ (m : Set ℝ → ENNReal), IsVitaliMeasure m → (∑' n, m (VitaliSeq n)) = m (⋃ n, VitaliSeq n))
variable (measure_Ico_one : ∀ (m : Set ℝ → ENNReal), IsVitaliMeasure m → m (Ico 0 1) = 1)
variable (union_subset_I : ∀ n, VitaliSeq n ⊆ I)

theorem not_exists_vitali_measure : ¬ ∃ m, IsVitaliMeasure m := by
  intro ⟨m, hm⟩
  rcases hm with ⟨h_out, h_empty, h_mono, h_add, h_inv, h_rect⟩
  let h_meas : IsVitaliMeasure m := ⟨h_out, h_empty, h_mono, h_add, h_inv, h_rect⟩
  let c := m VitaliSet
  have h_seq_c : ∀ n, m (VitaliSeq n) = c := measure_vitali_invariant m h_meas
  have h_union_eq : m (⋃ n, VitaliSeq n) = ∑' n, c := by
    rw [sum_vitali_eq_union m h_meas]
    congr; ext n; exact h_seq_c n
  have h_I_unit : m I = 1 := by
    specialize h_rect 0 1 (le_refl 0) zero_le_one (le_refl 1)
    simp [I] at *
    exact h_rect
  have h_union_le_1 : m (⋃ n, VitaliSeq n) ≤ 1 := by
    rw [← h_I_unit]
    refine h_mono (⋃ n, VitaliSeq n) I (iUnion_subset union_subset_I) (Subset.refl I) (iUnion_subset union_subset_I)
  have h_1_le_union : 1 ≤ m (⋃ n, VitaliSeq n) := by
    rw [← measure_Ico_one m h_meas]
    refine h_mono (Ico 0 1) (⋃ n, VitaliSeq n) Ico_subset_Icc_self (iUnion_subset union_subset_I) vitali_covers_Ico
  have h_sum_eq_1 : ∑' (n : ℕ), c = 1 := le_antisymm (h_union_eq.symm.trans_le h_union_le_1) (h_1_le_union.trans_eq h_union_eq)
  by_cases hc : c = 0
  · rw [hc] at h_sum_eq_1
    simp at h_sum_eq_1
  · have : ∑' (n : ℕ), c = ⊤ := ENNReal.tsum_const_eq_top_of_pos (pos_iff_ne_zero.mpr hc)
    rw [this] at h_sum_eq_1
    simp at h_sum_eq_1