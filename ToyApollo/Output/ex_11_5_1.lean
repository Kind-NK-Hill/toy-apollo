import Mathlib
import ToyApollo.Output.thm_11_5
import ToyApollo.Output.thm_11_8

/-
TASK ID: ex_11_5_1
TYPE: Example_Proof
SOURCE PLAN: chapter11-strong-law-large-numbers
TASK CONTENT:
\textbf{Example 11.5.1 (Estimation of Cumulative Distribution Function)} \\

Consider the problem of estimating the cdf F(x) = Pr (X\leq x) of a random variable X by

generating iid. samples Xn from the cdf F for n\geq 1 We can estimate F(x) by the empirical

distribution

Fn(x)\coloneqq 1

n

n\sum

k=1

1[Xk,\infty )(x).

The indicator function .1[Xk,\infty )(x) is equal to 1 if x\geq X k and is 0 otherwise. The function Fn first

counts the number of samples that is less than or equal to x , and then divides it by n Because it

depends on the random samples, the estimate Fn(x) is a random variable. By the strong law of

large numbers,Fn(x) converges to the correct value F(x) with probability 1.

This result is strengthened in the Glivenko-Cantelli theorem, which states that the convergence is

uniform in x ,

sup

x\inR

\vert Fn(x)- F(x) \vert

as.

-\to 0 .

The Glivenko-Cantelli theorem is informally known as "the fundamental theorem of statistics".
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter
open MeasureTheory
open ProbabilityTheory

noncomputable section

/-- The indicator used to estimate the cdf value `F x`: it is `1` exactly when
the `k`-th sample is at most `x`. -/
def empiricalCDFIndicator {Ω : Type*} (X : ℕ → Ω → ℝ) (x : ℝ) (k : ℕ) : Ω → ℝ :=
  fun ω => if X k ω ≤ x then 1 else 0

/-- The pointwise empirical cdf estimator at `x`, using the existing Chapter 11
sample-average interface. -/
def empiricalCDFAt {Ω : Type*} (X : ℕ → Ω → ℝ) (x : ℝ) (n : ℕ) : Ω → ℝ :=
  thm_11_5_sampleMean (fun k => empiricalCDFIndicator X x k) n

/--
Example 11.5.1: for a fixed point `x`, the empirical cdf estimator converges
almost surely to the true cdf value `F x`.

The assumptions are stated at the indicator level, exactly where the strong law
is applied: the indicators are pairwise independent, identically distributed,
integrable, and have expectation `F x`.
-/
theorem ex_11_5_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (F : ℝ → ℝ) (x : ℝ)
    (hInt : Integrable (empiricalCDFIndicator X x 0) P)
    (hpairwise :
      Pairwise fun i j =>
        empiricalCDFIndicator X x i ⟂ᵢ[P] empiricalCDFIndicator X x j)
    (hident :
      ∀ i, IdentDistrib
        (empiricalCDFIndicator X x i) (empiricalCDFIndicator X x 0) P P)
    (hmean : P[empiricalCDFIndicator X x 0] = F x) :
    ConvergesAlmostSurely P (fun n => empiricalCDFAt X x n) (fun _ => F x) := by
  simpa [empiricalCDFAt] using
    thm_11_8 P (fun k => empiricalCDFIndicator X x k) (F x)
      hInt hpairwise hident hmean
