import Mathlib
import ToyApollo.Output.thm_12_5
import ToyApollo.Output.thm_12_6

/-
TASK ID: prob_12_4
TYPE: Problem
SOURCE PLAN: chapter12-problems
TASK CONTENT:
\textbf{12.4.} Consider a finite sample space \Omega ={ a, b, c, d, e} with a uniform probability

measure. Define two random variables X and Y by

a b c d e

X() 1 2 1 2 3

Y() 1 2 3 4 5

(a) Derive the MMSE estimator of Y as a function of X.

(b) Derive the MMSE estimator of X as a function of Y .
-/

-- WRITE FINAL LEAN CODE BELOW

noncomputable section

/-- The five-point sample space in Problem 12.4. -/
inductive Prob124Omega
  | a | b | c | d | e
  deriving DecidableEq, Fintype

open Prob124Omega

/-- The random variable `X` from the table in Problem 12.4. -/
def prob_12_4_X : Prob124Omega → ℝ
  | a => 1
  | b => 2
  | c => 1
  | d => 2
  | e => 3

/-- The random variable `Y` from the table in Problem 12.4. -/
def prob_12_4_Y : Prob124Omega → ℝ
  | a => 1
  | b => 2
  | c => 3
  | d => 4
  | e => 5

/-- The MMSE estimator of `Y` as a function of `X`, obtained by averaging `Y`
over each fiber of `X` under the uniform law. -/
def prob_12_4_estYGivenXValue (x : ℝ) : ℝ :=
  if x = 1 then 2
  else if x = 2 then 3
  else if x = 3 then 5
  else 0

/-- The MMSE estimator of `X` as a function of `Y`. Since `Y` separates the
five sample points, this is the inverse table value of `X` on the range of `Y`. -/
def prob_12_4_estXGivenYValue (y : ℝ) : ℝ :=
  if y = 1 then 1
  else if y = 2 then 2
  else if y = 3 then 1
  else if y = 4 then 2
  else if y = 5 then 3
  else 0

/-- On the fiber `X = 1`, the conditional mean of `Y` is `(1 + 3) / 2 = 2`. -/
theorem prob_12_4_y_given_x_one :
    prob_12_4_estYGivenXValue 1 =
      (prob_12_4_Y a + prob_12_4_Y c) / 2 := by
  norm_num [prob_12_4_estYGivenXValue, prob_12_4_Y]

/-- On the fiber `X = 2`, the conditional mean of `Y` is `(2 + 4) / 2 = 3`. -/
theorem prob_12_4_y_given_x_two :
    prob_12_4_estYGivenXValue 2 =
      (prob_12_4_Y b + prob_12_4_Y d) / 2 := by
  norm_num [prob_12_4_estYGivenXValue, prob_12_4_Y]

/-- On the singleton fiber `X = 3`, the conditional mean of `Y` is `5`. -/
theorem prob_12_4_y_given_x_three :
    prob_12_4_estYGivenXValue 3 = prob_12_4_Y e := by
  norm_num [prob_12_4_estYGivenXValue, prob_12_4_Y]

/-- The estimator of `Y` as a function of `X`, evaluated on the sample space. -/
theorem prob_12_4_estYGivenX_table (ω : Prob124Omega) :
    prob_12_4_estYGivenXValue (prob_12_4_X ω) =
      match ω with
      | a => 2
      | b => 3
      | c => 2
      | d => 3
      | e => 5 := by
  cases ω <;> norm_num [prob_12_4_estYGivenXValue, prob_12_4_X]

/-- The estimator of `X` as a function of `Y`, evaluated on the sample space. -/
theorem prob_12_4_estXGivenY_table (ω : Prob124Omega) :
    prob_12_4_estXGivenYValue (prob_12_4_Y ω) = prob_12_4_X ω := by
  cases ω <;> norm_num [prob_12_4_estXGivenYValue, prob_12_4_X, prob_12_4_Y]

/-- The explicit finite-table answer to Problem 12.4. Part (a) is
`E[Y | X = 1] = 2`, `E[Y | X = 2] = 3`, and `E[Y | X = 3] = 5`; part (b) is
`E[X | Y = 1] = 1`, `E[X | Y = 2] = 2`, `E[X | Y = 3] = 1`,
`E[X | Y = 4] = 2`, and `E[X | Y = 5] = 3`. -/
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
