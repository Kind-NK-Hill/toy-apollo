/-
TASK ID: prob_12_4
TYPE: Problem
SOURCE PLAN: chapter12-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_12.thm_12_5
import ProbabilityTheory.chapter_12.thm_12_6




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



def prob_12_4_uniformExpectation (Z : Prob124Omega → ℝ) : ℝ :=
  (Z a + Z b + Z c + Z d + Z e) / 5

 
def prob_12_4_uniformMSE (U V : Prob124Omega → ℝ) : ℝ :=
  prob_12_4_uniformExpectation (fun ω => (U ω - V ω) ^ 2)



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

 
def prob_12_4_estYGivenX : Prob124Omega → ℝ :=
  fun ω => prob_12_4_estYGivenXValue (prob_12_4_X ω)

 
def prob_12_4_estXGivenY : Prob124Omega → ℝ :=
  fun ω => prob_12_4_estXGivenYValue (prob_12_4_Y ω)

 
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



theorem prob_12_4_yGivenX_mse_sub_opt (g : ℝ → ℝ) :
    prob_12_4_uniformMSE prob_12_4_Y (fun ω => g (prob_12_4_X ω)) -
        prob_12_4_uniformMSE prob_12_4_Y prob_12_4_estYGivenX =
      (2 * (g 1 - 2) ^ 2 + 2 * (g 2 - 3) ^ 2 + (g 3 - 5) ^ 2) / 5 := by
  norm_num [prob_12_4_uniformMSE, prob_12_4_uniformExpectation,
    prob_12_4_estYGivenX, prob_12_4_X, prob_12_4_Y,
    prob_12_4_estYGivenXValue]
  ring



theorem prob_12_4_xGivenY_mse_sub_opt (h : ℝ → ℝ) :
    prob_12_4_uniformMSE prob_12_4_X (fun ω => h (prob_12_4_Y ω)) -
        prob_12_4_uniformMSE prob_12_4_X prob_12_4_estXGivenY =
      ((h 1 - 1) ^ 2 + (h 2 - 2) ^ 2 + (h 3 - 1) ^ 2 +
        (h 4 - 2) ^ 2 + (h 5 - 3) ^ 2) / 5 := by
  norm_num [prob_12_4_uniformMSE, prob_12_4_uniformExpectation,
    prob_12_4_estXGivenY, prob_12_4_X, prob_12_4_Y,
    prob_12_4_estXGivenYValue]
  ring

 
theorem prob_12_4_estYGivenX_mse_value :
    prob_12_4_uniformMSE prob_12_4_Y prob_12_4_estYGivenX = (4 : ℝ) / 5 := by
  norm_num [prob_12_4_uniformMSE, prob_12_4_uniformExpectation,
    prob_12_4_estYGivenX, prob_12_4_X, prob_12_4_Y,
    prob_12_4_estYGivenXValue]



theorem prob_12_4_estXGivenY_mse_value :
    prob_12_4_uniformMSE prob_12_4_X prob_12_4_estXGivenY = 0 := by
  norm_num [prob_12_4_uniformMSE, prob_12_4_uniformExpectation,
    prob_12_4_estXGivenY, prob_12_4_X, prob_12_4_Y,
    prob_12_4_estXGivenYValue]



theorem prob_12_4_estYGivenX_optimal (g : ℝ → ℝ) :
    prob_12_4_uniformMSE prob_12_4_Y prob_12_4_estYGivenX ≤
      prob_12_4_uniformMSE prob_12_4_Y (fun ω => g (prob_12_4_X ω)) := by
  have hnonneg :
      0 ≤ (2 * (g 1 - 2) ^ 2 + 2 * (g 2 - 3) ^ 2 + (g 3 - 5) ^ 2) / 5 := by
    positivity
  linarith [prob_12_4_yGivenX_mse_sub_opt g]



theorem prob_12_4_estXGivenY_optimal (h : ℝ → ℝ) :
    prob_12_4_uniformMSE prob_12_4_X prob_12_4_estXGivenY ≤
      prob_12_4_uniformMSE prob_12_4_X (fun ω => h (prob_12_4_Y ω)) := by
  have hnonneg :
      0 ≤ ((h 1 - 1) ^ 2 + (h 2 - 2) ^ 2 + (h 3 - 1) ^ 2 +
        (h 4 - 2) ^ 2 + (h 5 - 3) ^ 2) / 5 := by
    positivity
  linarith [prob_12_4_xGivenY_mse_sub_opt h]



theorem prob_12_4 :
    ((prob_12_4_estYGivenXValue 1 = 2 ∧
        prob_12_4_estYGivenXValue 2 = 3 ∧
        prob_12_4_estYGivenXValue 3 = 5) ∧
      ∀ g : ℝ → ℝ,
        prob_12_4_uniformMSE prob_12_4_Y prob_12_4_estYGivenX ≤
          prob_12_4_uniformMSE prob_12_4_Y (fun ω => g (prob_12_4_X ω))) ∧
    ((prob_12_4_estXGivenYValue 1 = 1 ∧
        prob_12_4_estXGivenYValue 2 = 2 ∧
        prob_12_4_estXGivenYValue 3 = 1 ∧
        prob_12_4_estXGivenYValue 4 = 2 ∧
        prob_12_4_estXGivenYValue 5 = 3) ∧
      ∀ h : ℝ → ℝ,
        prob_12_4_uniformMSE prob_12_4_X prob_12_4_estXGivenY ≤
          prob_12_4_uniformMSE prob_12_4_X (fun ω => h (prob_12_4_Y ω))) := by
  constructor
  · constructor
    · norm_num [prob_12_4_estYGivenXValue]
    · exact prob_12_4_estYGivenX_optimal
  · constructor
    · norm_num [prob_12_4_estXGivenYValue]
    · exact prob_12_4_estXGivenY_optimal
