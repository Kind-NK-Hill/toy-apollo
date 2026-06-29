/-
TASK ID: prob_12_3
TYPE: Problem
SOURCE PLAN: chapter12-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_12_2
import ToyApollo.Output.def_12_5
import ToyApollo.Output.thm_12_5

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

def prob_12_3_exponentialInner (g h : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in Set.Ioi 0, g x * h x * Real.exp (-x)

theorem prob_12_3_exponential_total_mass :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-x) = 1 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := 1) (by norm_num) (by norm_num)
  simpa using h

theorem prob_12_3_exponential_second_moment :
    ∫ x : ℝ in Set.Ioi 0, x ^ 2 * Real.exp (-x) = 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3) (r := 1) (by norm_num) (by norm_num)
  norm_num at h
  exact h

def prob_12_3_projectionConstant : ℝ := 2

theorem prob_12_3_projection_normal_equation :
    prob_12_3_exponentialInner (fun x : ℝ => x ^ 2) (fun _ => 1) =
      prob_12_3_projectionConstant *
        prob_12_3_exponentialInner (fun _ : ℝ => 1) (fun _ => 1) := by
  unfold prob_12_3_exponentialInner prob_12_3_projectionConstant
  simp only [mul_one, one_mul]
  rw [prob_12_3_exponential_second_moment, prob_12_3_exponential_total_mass]
  norm_num

theorem prob_12_3 : prob_12_3_projectionConstant = 2 := rfl
