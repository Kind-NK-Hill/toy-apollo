/-
TASK ID: ex_8_3_4
TYPE: Example_Proof
SOURCE PLAN: 33_chap8_monge_kantorovich
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open scoped BigOperators

noncomputable section

abbrev Ex834Source := Bool

abbrev Ex834Target := Fin 3

def ex834Plan : Ex834Source → Ex834Target → ℝ
  | false, 0 => 1 / 5
  | false, 1 => 1 / 15
  | false, 2 => 1 / 15
  | true, 0 => 0
  | true, 1 => 2 / 15
  | true, 2 => 8 / 15

def ex834TransportCost (c : Ex834Source → Ex834Target → ℝ)
    (T : Ex834Source → Ex834Target → ℝ) : ℝ :=
  ∑ i, ∑ j, c i j * T i j

def IsEx834FeasiblePlan (T : Ex834Source → Ex834Target → ℝ) : Prop :=
  (∀ i j, 0 ≤ T i j) ∧
    (∑ j, T false j = 1 / 3) ∧
    (∑ j, T true j = 2 / 3) ∧
    (∑ i, T i 0 = 1 / 5) ∧
    (∑ i, T i 1 = 1 / 5) ∧
    (∑ i, T i 2 = 3 / 5)

theorem ex_8_3_4 :
    IsEx834FeasiblePlan ex834Plan ∧
      ∀ c : Ex834Source → Ex834Target → ℝ,
        ex834TransportCost c ex834Plan =
          ∑ i, ∑ j, c i j * ex834Plan i j := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j
      fin_cases j <;> cases i <;> norm_num [ex834Plan]
    · rw [Fin.sum_univ_three]
      norm_num [ex834Plan]
    · rw [Fin.sum_univ_three]
      norm_num [ex834Plan]
    · norm_num [ex834Plan, Fintype.sum_bool]
    · norm_num [ex834Plan, Fintype.sum_bool]
    · norm_num [ex834Plan, Fintype.sum_bool]
  · intro c
    rfl
