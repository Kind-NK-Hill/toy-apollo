import Mathlib
import ToyApollo.Output.def_9_3

/-
TASK ID: ex_9_2_1
TYPE: Example_Proof
SOURCE PLAN: chapter9-characteristic-functions
TASK CONTENT:
\textbf{Example 9.2.1 (Characteristic Function of Bernoulli Random Variable)} \\
Suppose $X$ follows a Bernoulli distribution with parameter $p$, where $P(X=0)=1-p$ and $P(X=1)=p$. The characteristic function of $X$ is given by
\[
\phi_X(t) = (1-p)e^{i\cdot 0\cdot t}+pe^{it}=1-p+pe^{it}.
\]
-/

-- WRITE FINAL LEAN CODE BELOW

open scoped BigOperators

noncomputable abbrev bernoulliValue : Bool → ℝ :=
  fun b => if b then 1 else 0

noncomputable abbrev bernoulliPMF (p : ℝ) : Bool → ℝ :=
  fun b => if b then p else 1 - p

noncomputable abbrev bernoulliCharacteristicFunction (p t : ℝ) : ℂ :=
  1 - (p : ℂ) + (p : ℂ) * Complex.exp (Complex.I * (t : ℂ))

theorem bernoulliCharacteristicFunction_finite_sum (p t : ℝ) :
    (∑ b : Bool,
        Complex.exp (Complex.I * (bernoulliValue b : ℂ) * (t : ℂ)) *
          (bernoulliPMF p b : ℂ)) =
      bernoulliCharacteristicFunction p t := by
  simp [bernoulliValue, bernoulliPMF, bernoulliCharacteristicFunction]
  ring

theorem ex_9_2_1 (p t : ℝ) :
    discreteCharacteristicFunction bernoulliValue (bernoulliPMF p) t =
      bernoulliCharacteristicFunction p t := by
  rw [discreteCharacteristicFunction]
  rw [tsum_fintype]
  exact bernoulliCharacteristicFunction_finite_sum p t
