import Mathlib
import ToyApollo.Output.ch8_bernoulli_bool_core

/-
TASK ID: ex_8_4_2
TYPE: Example_Proof
SOURCE PLAN: 34_chap8_total_variation_distance
TASK CONTENT:
\textbf{Example 8.4.2 (Total Variation Distance Between Two Bernoulli Distributions)} \\
Let $\Omega=\{H,T\}$ be a sample space with two outcomes. We can define two probability measures $P$ and $Q$ on $\Omega$ by setting $P(\{H\})=p=1-P(\{T\})$ and setting $Q(\{H\})=q=1-Q(\{T\})$, where $0\le p,q\le 1$. If we take $A=\{H\}$ in (8.3), we obtain $|P(\{H\})-Q(\{H\})|=|p-q|$. Likewise, when we take $A=\{T\}$, we obtain $|P(\{T\})-Q(\{T\})|=|p-q|$. The total variation distance is $|p-q|$.

When $p=q$, the two probability measures $P$ and $Q$ are the same, and their total variation distance is 0. Otherwise, the total variation distance is the absolute difference between the two probabilities $p$ and $q$.

When two probability distributions are both of discrete type and both continuous type, we can compute the total variation distance by the formulas in the following theorem.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set
open Ch8BernoulliBoolCore

noncomputable def ex842TotalVariationDistance
    {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) : ℝ :=
  sSup {d : ℝ | ∃ A : Set Ω, MeasurableSet A ∧ d = |P.real A - Q.real A|}

/-- Example 8.4.2: for Bernoulli laws on a two-point space, the total variation distance is the
absolute difference of the success probabilities. -/
theorem ex_8_4_2 (p q : NNReal) (hp : p ≤ 1) (hq : q ≤ 1) :
    ex842TotalVariationDistance (bernoulliMeasure p hp) (bernoulliMeasure q hq)
      = |(p : ℝ) - q| := by
  simpa [ex842TotalVariationDistance, totalVariationDistance] using
    boolBernoulli_totalVariationDistance_eq_abs p q hp hq
