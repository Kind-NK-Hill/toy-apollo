/-
TASK ID: ex_4_3_2
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_04.def_4_3_limsup_liminf

open Filter
open scoped Topology

private theorem ex_4_3_2_seqLimsup_eq_filter_limsup (u : ℕ → EReal) :
    seqLimsup u = Filter.limsup u Filter.atTop := by
  simpa [seqLimsup, tailSup, Nat.add_comm] using
    (Filter.limsup_eq_iInf_iSup_of_nat' (u := u)).symm

private theorem ex_4_3_2_seqLiminf_eq_filter_liminf (u : ℕ → EReal) :
    seqLiminf u = Filter.liminf u Filter.atTop := by
  simpa [seqLiminf, tailInf, Nat.add_comm] using
    (Filter.liminf_eq_iSup_iInf_of_nat' (u := u)).symm




 
noncomputable def ex_4_3_2_seq (n : ℕ) : ℝ :=
  if Even n then 1 + 1 / ((n : ℝ) + 1) else -1 - 1 / ((n : ℝ) + 1)

 
noncomputable def ex_4_3_2_seqEReal (n : ℕ) : EReal :=
  (ex_4_3_2_seq n : EReal)

theorem ex_4_3_2_seq_even (n : ℕ) :
    ex_4_3_2_seq (2 * n) = 1 + 1 / (((2 * n : ℕ) : ℝ) + 1) := by
  have h : Even (2 * n) := by
    exact even_two.mul_right n
  simp [ex_4_3_2_seq, h]

theorem ex_4_3_2_seq_odd (n : ℕ) :
    ex_4_3_2_seq (2 * n + 1) = (-1 : ℝ) - 1 / (((2 * n + 1 : ℕ) : ℝ) + 1) := by
  have hEven : Even (2 * n) := by
    exact even_two.mul_right n
  have hOdd : ¬ Even (2 * n + 1) := by
    intro h1
    exact (Nat.even_add_one.mp h1) hEven
  simp [ex_4_3_2_seq, hOdd]

theorem ex_4_3_2_one_lt_even (n : ℕ) :
    (1 : ℝ) < ex_4_3_2_seq (2 * n) := by
  rw [ex_4_3_2_seq_even]
  have hpos : (0 : ℝ) < 1 / (((2 * n : ℕ) : ℝ) + 1) := by positivity
  linarith

theorem ex_4_3_2_odd_lt_neg_one (n : ℕ) :
    ex_4_3_2_seq (2 * n + 1) < (-1 : ℝ) := by
  rw [ex_4_3_2_seq_odd]
  have hpos : (0 : ℝ) < 1 / (((2 * n + 1 : ℕ) : ℝ) + 1) := by positivity
  linarith

theorem tendsto_two_mul_atTop : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
  refine tendsto_atTop_mono (fun n => ?_) tendsto_id
  simpa using Nat.le_mul_of_pos_left n (by norm_num : 0 < 2)

theorem tendsto_two_mul_add_one_atTop :
    Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop := by
  exact tendsto_add_atTop_nat 1 |>.comp tendsto_two_mul_atTop

 
theorem ex_4_3_2_positive_subsequence_tendsto :
    Tendsto (fun n : ℕ => ex_4_3_2_seq (2 * n)) atTop (𝓝 (1 : ℝ)) := by
  have hzero :
      Tendsto (fun n : ℕ => (1 : ℝ) / (((2 * n : ℕ) : ℝ) + 1)) atTop (𝓝 0) := by
    have hbase :
        Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    exact hbase.comp tendsto_two_mul_atTop
  simpa [ex_4_3_2_seq_even] using tendsto_const_nhds.add hzero

 
theorem ex_4_3_2_negative_subsequence_tendsto :
    Tendsto (fun n : ℕ => ex_4_3_2_seq (2 * n + 1)) atTop (𝓝 (-1 : ℝ)) := by
  have hzero :
      Tendsto (fun n : ℕ => (1 : ℝ) / (((2 * n + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) := by
    have hbase :
        Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    exact hbase.comp tendsto_two_mul_add_one_atTop
  simpa [ex_4_3_2_seq_odd, sub_eq_add_neg] using tendsto_const_nhds.sub hzero

 
theorem ex_4_3_2_not_tendsto_one :
    ¬ Tendsto ex_4_3_2_seq atTop (𝓝 (1 : ℝ)) := by
  intro h
  have hsub := h.comp tendsto_two_mul_add_one_atTop
  have hneg := tendsto_nhds_unique hsub ex_4_3_2_negative_subsequence_tendsto
  norm_num at hneg

 
theorem ex_4_3_2_not_tendsto_neg_one :
    ¬ Tendsto ex_4_3_2_seq atTop (𝓝 (-1 : ℝ)) := by
  intro h
  have hsub := h.comp tendsto_two_mul_atTop
  have hpos := tendsto_nhds_unique hsub ex_4_3_2_positive_subsequence_tendsto
  norm_num at hpos

 
theorem ex_4_3_2_not_tendsto (l : ℝ) :
    ¬ Tendsto ex_4_3_2_seq atTop (𝓝 l) := by
  intro h
  have hpos := tendsto_nhds_unique
    (h.comp tendsto_two_mul_atTop) ex_4_3_2_positive_subsequence_tendsto
  have hneg := tendsto_nhds_unique
    (h.comp tendsto_two_mul_add_one_atTop) ex_4_3_2_negative_subsequence_tendsto
  linarith

 
theorem ex_4_3_2_not_convergent :
    ¬ ∃ l : ℝ, Tendsto ex_4_3_2_seq atTop (𝓝 l) := by
  rintro ⟨l, hl⟩
  exact ex_4_3_2_not_tendsto l hl

theorem ex_4_3_2_eventually_lt_of_one_lt {r : ℝ} (hr : 1 < r) :
    ∀ᶠ n : ℕ in atTop, ex_4_3_2_seq n < r := by
  have hzero :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hε : (0 : ℝ) < r - 1 := sub_pos.2 hr
  have hsmall : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / ((n : ℝ) + 1) < r - 1 :=
    (tendsto_order.1 hzero).2 (r - 1) hε
  filter_upwards [hsmall] with n hn
  by_cases hEven : Even n
  · have hbranch : (1 : ℝ) + 1 / ((n : ℝ) + 1) < r := by linarith
    simpa [ex_4_3_2_seq, hEven] using hbranch
  · have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hbranch : (-1 : ℝ) - 1 / ((n : ℝ) + 1) < r := by linarith
    simpa [ex_4_3_2_seq, hEven] using hbranch

theorem ex_4_3_2_eventually_gt_of_lt_neg_one {r : ℝ} (hr : r < -1) :
    ∀ᶠ n : ℕ in atTop, r < ex_4_3_2_seq n := by
  have hzero :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hε : (0 : ℝ) < -1 - r := sub_pos.2 hr
  have hsmall : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / ((n : ℝ) + 1) < -1 - r :=
    (tendsto_order.1 hzero).2 (-1 - r) hε
  filter_upwards [hsmall] with n hn
  by_cases hEven : Even n
  · have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hbranch : r < (1 : ℝ) + 1 / ((n : ℝ) + 1) := by linarith
    simpa [ex_4_3_2_seq, hEven] using hbranch
  · have hbranch : r < (-1 : ℝ) - 1 / ((n : ℝ) + 1) := by linarith
    simpa [ex_4_3_2_seq, hEven] using hbranch

theorem ex_4_3_2_frequently_one_le :
    ∃ᶠ n : ℕ in atTop, (1 : EReal) ≤ ex_4_3_2_seqEReal n := by
  rw [frequently_atTop]
  intro a
  refine ⟨2 * a, by omega, ?_⟩
  have hreal : (1 : ℝ) ≤ ex_4_3_2_seq (2 * a) :=
    le_of_lt (ex_4_3_2_one_lt_even a)
  simpa [ex_4_3_2_seqEReal] using (EReal.coe_le_coe_iff.2 hreal)

theorem ex_4_3_2_frequently_le_neg_one :
    ∃ᶠ n : ℕ in atTop, ex_4_3_2_seqEReal n ≤ (-1 : EReal) := by
  rw [frequently_atTop]
  intro a
  refine ⟨2 * a + 1, by omega, ?_⟩
  have hreal : ex_4_3_2_seq (2 * a + 1) ≤ (-1 : ℝ) :=
    le_of_lt (ex_4_3_2_odd_lt_neg_one a)
  simpa [ex_4_3_2_seqEReal] using (EReal.coe_le_coe_iff.2 hreal)

 
theorem ex_4_3_2_seqLimsup_value :
    seqLimsup ex_4_3_2_seqEReal = (1 : EReal) := by
  rw [ex_4_3_2_seqLimsup_eq_filter_limsup]
  apply le_antisymm
  · rw [limsup_le_iff]
    intro y hy
    obtain ⟨r, h1rE, hry⟩ := (EReal.lt_iff_exists_real_btwn).1 hy
    have h1r : (1 : ℝ) < r := EReal.coe_lt_coe_iff.1 (by simpa using h1rE)
    filter_upwards [ex_4_3_2_eventually_lt_of_one_lt h1r] with n hn
    exact lt_trans (EReal.coe_lt_coe_iff.2 hn) hry
  · exact le_limsup_of_frequently_le ex_4_3_2_frequently_one_le

 
theorem ex_4_3_2_seqLiminf_value :
    seqLiminf ex_4_3_2_seqEReal = (-1 : EReal) := by
  rw [ex_4_3_2_seqLiminf_eq_filter_liminf]
  apply le_antisymm
  · exact liminf_le_of_frequently_le ex_4_3_2_frequently_le_neg_one
  · rw [le_liminf_iff]
    intro y hy
    obtain ⟨r, hyr, hrnegE⟩ := (EReal.lt_iff_exists_real_btwn).1 hy
    have hrneg : r < (-1 : ℝ) := EReal.coe_lt_coe_iff.1 (by simpa using hrnegE)
    filter_upwards [ex_4_3_2_eventually_gt_of_lt_neg_one hrneg] with n hn
    exact lt_trans hyr (EReal.coe_lt_coe_iff.2 hn)

 
theorem ex_4_3_2 :
    Tendsto (fun n : ℕ => ex_4_3_2_seq (2 * n)) atTop (𝓝 (1 : ℝ)) ∧
      Tendsto (fun n : ℕ => ex_4_3_2_seq (2 * n + 1)) atTop (𝓝 (-1 : ℝ)) ∧
      (¬ ∃ l : ℝ, Tendsto ex_4_3_2_seq atTop (𝓝 l)) ∧
      seqLimsup ex_4_3_2_seqEReal = (1 : EReal) ∧
      seqLiminf ex_4_3_2_seqEReal = (-1 : EReal) := by
  exact ⟨ex_4_3_2_positive_subsequence_tendsto,
    ex_4_3_2_negative_subsequence_tendsto,
    ex_4_3_2_not_convergent,
    ex_4_3_2_seqLimsup_value,
    ex_4_3_2_seqLiminf_value⟩
