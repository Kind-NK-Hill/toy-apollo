/-
TASK ID: prob_12_4
TYPE: Problem
SOURCE PLAN: chapter12-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_12_5
import ToyApollo.Output.thm_12_6

-- WRITE FINAL LEAN CODE BELOW

noncomputable section

inductive Prob124Omega
  | a | b | c | d | e
  deriving DecidableEq, Fintype

open Prob124Omega

def prob_12_4_X : Prob124Omega → ℝ
  | a => 1
  | b => 2
  | c => 1
  | d => 2
  | e => 3

def prob_12_4_Y : Prob124Omega → ℝ
  | a => 1
  | b => 2
  | c => 3
  | d => 4
  | e => 5

def prob_12_4_estYGivenXValue (x : ℝ) : ℝ :=
  if x = 1 then 2
  else if x = 2 then 3
  else if x = 3 then 5
  else 0

def prob_12_4_estXGivenYValue (y : ℝ) : ℝ :=
  if y = 1 then 1
  else if y = 2 then 2
  else if y = 3 then 1
  else if y = 4 then 2
  else if y = 5 then 3
  else 0

theorem prob_12_4_y_given_x_one :
    prob_12_4_estYGivenXValue 1 =
      (prob_12_4_Y a + prob_12_4_Y c) / 2 := by
  norm_num [prob_12_4_estYGivenXValue, prob_12_4_Y]

theorem prob_12_4_y_given_x_two :
    prob_12_4_estYGivenXValue 2 =
      (prob_12_4_Y b + prob_12_4_Y d) / 2 := by
  norm_num [prob_12_4_estYGivenXValue, prob_12_4_Y]

theorem prob_12_4_y_given_x_three :
    prob_12_4_estYGivenXValue 3 = prob_12_4_Y e := by
  norm_num [prob_12_4_estYGivenXValue, prob_12_4_Y]

theorem prob_12_4_estYGivenX_table (ω : Prob124Omega) :
    prob_12_4_estYGivenXValue (prob_12_4_X ω) =
      match ω with
      | a => 2
      | b => 3
      | c => 2
      | d => 3
      | e => 5 := by
  cases ω <;> norm_num [prob_12_4_estYGivenXValue, prob_12_4_X]

theorem prob_12_4_estXGivenY_table (ω : Prob124Omega) :
    prob_12_4_estXGivenYValue (prob_12_4_Y ω) = prob_12_4_X ω := by
  cases ω <;> norm_num [prob_12_4_estXGivenYValue, prob_12_4_X, prob_12_4_Y]

theorem prob_12_4 :
    (prob_12_4_estYGivenXValue 1 = 2 ∧
      prob_12_4_estYGivenXValue 2 = 3 ∧
      prob_12_4_estYGivenXValue 3 = 5) ∧
    (prob_12_4_estXGivenYValue 1 = 1 ∧
      prob_12_4_estXGivenYValue 2 = 2 ∧
      prob_12_4_estXGivenYValue 3 = 1 ∧
      prob_12_4_estXGivenYValue 4 = 2 ∧
      prob_12_4_estXGivenYValue 5 = 3) := by
  norm_num [prob_12_4_estYGivenXValue, prob_12_4_estXGivenYValue]
