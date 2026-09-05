/-
TASK ID: prob_8_4
TYPE: Problem
SOURCE PLAN: 35_chap8_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib




-- WRITE FINAL LEAN CODE BELOW

open scoped BigOperators

noncomputable section

 
abbrev Omega := Fin 3

noncomputable def P : Omega → ℝ
  | 0 => 1 / 3
  | 1 => 1 / 3
  | _ => 1 / 3

noncomputable def Q (x : Omega) : ℝ :=
  match x.val with
  | 0 => 1 / 2
  | _ => 1 / 4



def maximalCoupling (x y : Omega) : ℝ :=
  match x.val, y.val with
  | 0, 0 => 1 / 3
  | 1, 0 => 1 / 12
  | 1, 1 => 1 / 4
  | 2, 0 => 1 / 12
  | 2, 2 => 1 / 4
  | _, _ => 0



theorem prob_8_4 :
    ∃ π : Omega → Omega → ℝ,
      (∀ x y, 0 ≤ π x y) ∧
      (∑ x, ∑ y, π x y = 1) ∧
      (∀ x, ∑ y, π x y = P x) ∧
      (∀ y, ∑ x, π x y = Q y) ∧
      (∑ x, π x x = 5 / 6) ∧
      (∀ ρ : Omega → Omega → ℝ,
        (∀ x y, 0 ≤ ρ x y) →
        (∀ x, ∑ y, ρ x y = P x) →
        (∀ y, ∑ x, ρ x y = Q y) →
        ∑ x, ρ x x ≤ 5 / 6) := by
  refine ⟨maximalCoupling, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    fin_cases x <;> fin_cases y <;> norm_num [maximalCoupling]
  · rw [Fin.sum_univ_three]
    repeat rw [Fin.sum_univ_three]
    norm_num [maximalCoupling]
  · intro x
    fin_cases x <;> rw [Fin.sum_univ_three] <;> norm_num [maximalCoupling, P]
  · intro y
    fin_cases y <;> rw [Fin.sum_univ_three] <;> norm_num [maximalCoupling, Q]
  · rw [Fin.sum_univ_three]
    norm_num [maximalCoupling]
  · intro ρ hnonneg hrow hcol
    have h00 : ρ 0 0 ≤ 1 / 3 := by
      have hr := hrow 0
      rw [Fin.sum_univ_three] at hr
      norm_num [P] at hr
      linarith [hnonneg 0 1, hnonneg 0 2]
    have h11 : ρ 1 1 ≤ 1 / 4 := by
      have hc := hcol 1
      rw [Fin.sum_univ_three] at hc
      norm_num [Q] at hc
      linarith [hnonneg 0 1, hnonneg 2 1]
    have h22 : ρ 2 2 ≤ 1 / 4 := by
      have hc := hcol 2
      rw [Fin.sum_univ_three] at hc
      norm_num [Q] at hc
      linarith [hnonneg 0 2, hnonneg 1 2]
    rw [Fin.sum_univ_three]
    linarith
