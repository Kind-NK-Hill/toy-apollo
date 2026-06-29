import Mathlib

/-
TASK ID: ex_8_1_1
TYPE: Example_Proof
SOURCE PLAN: 31_chap8_coupling
TASK CONTENT:
\textbf{Example 8.1.1 (Simulating a Bernoulli Random Variable by Tossing a Die)} \\
We simulate a Bernoulli distributed random variable $Y$, with distribution $P(Y=0)=2/3$ and $P(Y=1)=1/3$, by tossing a fair die. Suppose $X$ is a random variable that is uniformly distributed on $\{1,2,3,4,5,6\}$. We can define $Y$ to be $0$ if $X=1,2,3,4$ and $Y$ to be $1$ if $X=5,6$. This function provides a deterministic coupling from $X$ to $Y$.

To illustrate the concepts discussed above, we provide an example of two different couplings of Gaussian-distributed random variables below.
-/

-- WRITE FINAL LEAN CODE BELOW

open Finset

/-- The deterministic transport sending the first four die faces to `0` and the last two to `1`. -/
def dieToBernoulli : Fin 6 → Bool :=
  fun i => 4 ≤ i.1

/-- Data package recording the Bernoulli simulation obtained from a fair die. -/
structure BernoulliByDieDeterministicCoupling where
  transport : Fin 6 → Bool
  zeroCount : (Finset.univ.filter fun i => transport i = false).card = 4
  oneCount : (Finset.univ.filter fun i => transport i = true).card = 2
  probZero : ℚ
  probOne : ℚ
  probZero_eq : probZero = 2 / 3
  probOne_eq : probOne = 1 / 3

/-- Example 8.1.1: a Bernoulli random variable with law `(2/3, 1/3)` obtained deterministically
from a fair die by grouping faces `{1,2,3,4}` and `{5,6}`. -/
noncomputable def ex_8_1_1 : BernoulliByDieDeterministicCoupling where
  transport := dieToBernoulli
  zeroCount := by native_decide
  oneCount := by native_decide
  probZero := 2 / 3
  probOne := 1 / 3
  probZero_eq := rfl
  probOne_eq := rfl
