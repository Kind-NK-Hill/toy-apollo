/-
TASK ID: prob_13_1
TYPE: Problem
SOURCE PLAN: chapter13-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open scoped BigOperators

noncomputable section

inductive Prob131Value
  | one | two | three
  deriving DecidableEq, Fintype

open Prob131Value

def prob_13_1_value : Prob131Value -> ℝ
  | Prob131Value.one => 1
  | Prob131Value.two => 2
  | Prob131Value.three => 3

def prob_13_1_jointPmf : Prob131Value -> Prob131Value -> ℝ
  | Prob131Value.one, Prob131Value.one => 1 / 10
  | Prob131Value.one, Prob131Value.two => 0
  | Prob131Value.one, Prob131Value.three => 1 / 5
  | Prob131Value.two, Prob131Value.one => 0
  | Prob131Value.two, Prob131Value.two => 3 / 10
  | Prob131Value.two, Prob131Value.three => 0
  | Prob131Value.three, Prob131Value.one => 1 / 5
  | Prob131Value.three, Prob131Value.two => 1 / 5
  | Prob131Value.three, Prob131Value.three => 0

def prob_13_1_yMarginal (y : Prob131Value) : ℝ :=
  ∑ x : Prob131Value, prob_13_1_jointPmf x y

def prob_13_1_xMarginal (x : Prob131Value) : ℝ :=
  ∑ y : Prob131Value, prob_13_1_jointPmf x y

def prob_13_1_E_X_given_Y_numerator (y : Prob131Value) : ℝ :=
  ∑ x : Prob131Value, prob_13_1_value x * prob_13_1_jointPmf x y

def prob_13_1_E_Y_given_X_numerator (x : Prob131Value) : ℝ :=
  ∑ y : Prob131Value, prob_13_1_value y * prob_13_1_jointPmf x y

def prob_13_1_E_X_given_Y_value (y : Prob131Value) : ℝ :=
  prob_13_1_E_X_given_Y_numerator y / prob_13_1_yMarginal y

def prob_13_1_E_Y_given_X_value (x : Prob131Value) : ℝ :=
  prob_13_1_E_Y_given_X_numerator x / prob_13_1_xMarginal x

lemma prob_13_1_sum_univ (f : Prob131Value -> ℝ) :
    (∑ v : Prob131Value, f v) =
      f Prob131Value.one + f Prob131Value.two + f Prob131Value.three := by
  have h_univ :
      (Finset.univ : Finset Prob131Value) =
        {Prob131Value.one, Prob131Value.two, Prob131Value.three} := by
    ext v
    fin_cases v <;> simp
  simp [h_univ, add_assoc]

theorem prob_13_1_y_marginals :
    prob_13_1_yMarginal Prob131Value.one = 3 / 10 ∧
      prob_13_1_yMarginal Prob131Value.two = 1 / 2 ∧
      prob_13_1_yMarginal Prob131Value.three = 1 / 5 := by
  norm_num [prob_13_1_yMarginal, prob_13_1_sum_univ, prob_13_1_jointPmf]

theorem prob_13_1_x_marginals :
    prob_13_1_xMarginal Prob131Value.one = 3 / 10 ∧
      prob_13_1_xMarginal Prob131Value.two = 3 / 10 ∧
      prob_13_1_xMarginal Prob131Value.three = 2 / 5 := by
  norm_num [prob_13_1_xMarginal, prob_13_1_sum_univ, prob_13_1_jointPmf]

theorem prob_13_1_E_X_given_Y_numerators :
    prob_13_1_E_X_given_Y_numerator Prob131Value.one = 7 / 10 ∧
      prob_13_1_E_X_given_Y_numerator Prob131Value.two = 6 / 5 ∧
      prob_13_1_E_X_given_Y_numerator Prob131Value.three = 1 / 5 := by
  norm_num [prob_13_1_E_X_given_Y_numerator, prob_13_1_sum_univ,
    prob_13_1_value, prob_13_1_jointPmf]

theorem prob_13_1_E_Y_given_X_numerators :
    prob_13_1_E_Y_given_X_numerator Prob131Value.one = 7 / 10 ∧
      prob_13_1_E_Y_given_X_numerator Prob131Value.two = 3 / 5 ∧
      prob_13_1_E_Y_given_X_numerator Prob131Value.three = 3 / 5 := by
  norm_num [prob_13_1_E_Y_given_X_numerator, prob_13_1_sum_univ,
    prob_13_1_value, prob_13_1_jointPmf]

theorem prob_13_1_E_X_given_Y :
    prob_13_1_E_X_given_Y_value Prob131Value.one = 7 / 3 ∧
      prob_13_1_E_X_given_Y_value Prob131Value.two = 12 / 5 ∧
      prob_13_1_E_X_given_Y_value Prob131Value.three = 1 := by
  norm_num [prob_13_1_E_X_given_Y_value, prob_13_1_yMarginal,
    prob_13_1_E_X_given_Y_numerator, prob_13_1_sum_univ,
    prob_13_1_value, prob_13_1_jointPmf]

theorem prob_13_1_E_Y_given_X :
    prob_13_1_E_Y_given_X_value Prob131Value.one = 7 / 3 ∧
      prob_13_1_E_Y_given_X_value Prob131Value.two = 2 ∧
      prob_13_1_E_Y_given_X_value Prob131Value.three = 3 / 2 := by
  norm_num [prob_13_1_E_Y_given_X_value, prob_13_1_xMarginal,
    prob_13_1_E_Y_given_X_numerator, prob_13_1_sum_univ,
    prob_13_1_value, prob_13_1_jointPmf]

theorem prob_13_1 :
    (prob_13_1_E_X_given_Y_value Prob131Value.one = 7 / 3 ∧
      prob_13_1_E_X_given_Y_value Prob131Value.two = 12 / 5 ∧
      prob_13_1_E_X_given_Y_value Prob131Value.three = 1) ∧
    (prob_13_1_E_Y_given_X_value Prob131Value.one = 7 / 3 ∧
      prob_13_1_E_Y_given_X_value Prob131Value.two = 2 ∧
      prob_13_1_E_Y_given_X_value Prob131Value.three = 3 / 2) := by
  exact ⟨prob_13_1_E_X_given_Y, prob_13_1_E_Y_given_X⟩
