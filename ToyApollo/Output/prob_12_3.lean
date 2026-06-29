import Mathlib
import ToyApollo.Output.def_12_2
import ToyApollo.Output.def_12_5
import ToyApollo.Output.thm_12_5

/-
TASK ID: prob_12_3
TYPE: Problem
SOURCE PLAN: chapter12-problems
TASK CONTENT:
\textbf{12.3.} Denote the pdf of the exponential distribution with mean 1 by

f( x) =

{

e-x if x> 0

0 otherwise.

Define an inner product \langleg, h\rangle\coloneqq

\int\infty

0 g(x)h(x)f (x) dx for two functions g(x) and

h(x)Compute the projection of the square function g(x) = x2 onto the subspace

that consists of constant functions.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- The weighted inner product in Problem 12.3 for the exponential density of
mean `1`, restricted to the positive real line. -/
def prob_12_3_exponentialInner (g h : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in Set.Ioi 0, g x * h x * Real.exp (-x)

/-- The exponential density in Problem 12.3 has total mass `1` on `(0, ∞)`. -/
theorem prob_12_3_exponential_total_mass :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-x) = 1 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := 1) (by norm_num) (by norm_num)
  simpa using h

/-- The second moment of the mean-one exponential density is `2`. -/
theorem prob_12_3_exponential_second_moment :
    ∫ x : ℝ in Set.Ioi 0, x ^ 2 * Real.exp (-x) = 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3) (r := 1) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- The constant function that solves the projection of `x ↦ x^2` onto the
constant subspace under the Problem 12.3 exponential inner product. -/
def prob_12_3_projectionConstant : ℝ := 2

/-- Problem 12.3: the projection constant `2` satisfies the normal equation for
projection onto the subspace of constant functions. -/
theorem prob_12_3_projection_normal_equation :
    prob_12_3_exponentialInner (fun x : ℝ => x ^ 2) (fun _ => 1) =
      prob_12_3_projectionConstant *
        prob_12_3_exponentialInner (fun _ : ℝ => 1) (fun _ => 1) := by
  unfold prob_12_3_exponentialInner prob_12_3_projectionConstant
  simp only [mul_one, one_mul]
  rw [prob_12_3_exponential_second_moment, prob_12_3_exponential_total_mass]
  norm_num

/-- The numerical answer requested by Problem 12.3. -/
theorem prob_12_3 : prob_12_3_projectionConstant = 2 := rfl
