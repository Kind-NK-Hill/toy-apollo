/-
TASK ID: prob_8_1
TYPE: Problem
SOURCE PLAN: 35_chap8_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib




open scoped Topology

noncomputable section

 
def prob_8_1_f (i j : ℕ) : ℝ :=
  if i = j then (i : ℝ) else if j = i + 1 then (-(i : ℝ)) else 0

lemma prob_8_1_inner_sum_eq_zero (i : ℕ) :
    ∑' (j : ℕ), prob_8_1_f i j = 0 := by
  unfold prob_8_1_f
  rw [tsum_eq_sum]
  any_goals exact {i, i + 1}
  · rw [Finset.sum_pair] <;> norm_num
  · aesop

lemma prob_8_1_col_sum_pos (j : ℕ) (hj : 0 < j) :
    ∑' (i : ℕ), prob_8_1_f i j = 1 := by
  unfold prob_8_1_f
  rw [tsum_eq_sum]
  any_goals exact {j, j - 1}
  · rcases j with (_ | _ | j) <;> norm_num at *
  · grind

lemma prob_8_1_iterated_sum_eq_zero :
    ∑' (i : ℕ), ∑' (j : ℕ), prob_8_1_f i j = 0 := by
  simp [prob_8_1_inner_sum_eq_zero]

lemma prob_8_1_not_summable :
    ¬ Summable (fun (j : ℕ) => ∑' (i : ℕ), prob_8_1_f i j) := by
  exact fun h =>
    absurd h.tendsto_atTop_zero (by
      erw [Filter.tendsto_congr'
        (by
          filter_upwards [Filter.eventually_ge_atTop 1] with j hj
          rw [prob_8_1_col_sum_pos j hj])]
      norm_num)

theorem prob_8_1 :
    (let f := fun (i j : ℕ) =>
      (if i = j then (i : ℝ) else if j = i + 1 then (-(i : ℝ)) else 0)
    (∑' (i : ℕ), ∑' (j : ℕ), f i j) = 0 ∧
      ¬ (Summable fun (j : ℕ) => ∑' (i : ℕ), f i j)) := by
  refine ⟨?_, ?_⟩
  · convert prob_8_1_iterated_sum_eq_zero using 2 <;> simp [prob_8_1_f]
  · convert prob_8_1_not_summable using 2 <;> simp [prob_8_1_f]

end
