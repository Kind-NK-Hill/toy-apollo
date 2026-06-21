import ToyApollo.Output.thm_14_7_support

/-
TASK ID: thm_14_7
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter14-central-limit-theorems
TASK CONTENT:
\begin{thmbox}{14.7 (Lindeberg-Levy Central Limit Theorem)}
\end{thmbox}

Let .(Xk)\infty

k=1 be a sequence of iid. random variables with finite mean

E[X1]= \mu and finite variance Var(X1)= \sigma 2. Then

\sumn

k=1 Xk -n\mu

\sigma\sqrt n converges in distribution toN( 0,1).

Sketch of Proof We may assume \mu= 0 by re-defining X1 :=X 1 -\mu Let. Sn \coloneqq

X1 +X 2 +\cdot\cdot\cdot+ Xn.

Step 1. [ 4, Theorem 3.3.20] Since. X1 has variance. \sigma2, the characteristic function

of X1 is

\phiX1 (t)= 1 - \sigma2t2

2 +o(t 2),

where o(t2) refers to a function h(t) such that limt\to 0 h(t)

t2 =0 .

Step 2. Because the random variables Xk's are assumed to be independent, the

characteristic function of Sn

\sigma\sqrt n is

(

1- t2

2n +o

( 1

n

)) n

It can be written as .

(

1+ cn

n

) n

, where cn be the constant defined by

cn

n =- t2

2n +o

( 1

n

)

Step 3. [ 4, Theorem 3.4.2] If c1, c2, c3,.are complex numbers with

limn\to\infty cn =c , then

limn\to\infty (1+ c n/n)n =e c.

Step 4. Because cn \to- t2

2 +o( 1), we get limn\to\infty cn =- t2/2. The charac-

teristic function of Sn

\sigma\sqrt n approaches e-t2/2 as n\to\infty Since e-t2/2 is a continuous

function, by Levy's continuity theorem, Sn

\sigma\sqrt n converges to the distribution whose

characteristic function is e-t2/2.

Step 5. Steps 1-4 hold for any iid. sequence with finite mean and variance.

In particular, it is true if the random variables are iid. standard Gaussian random

variables. We use the fact that the sum of Gaussian random variables are Gaussian.

When Steps 1 and 4 are applied to iid. standard Gaussian random variables, the

random variables Sn

\sigma\sqrt n have standard Gaussian distribution for all n and hence must

converge in distribution to N( 0,1)The characteristic function of N( 0,1) must be

equal to e-t2/2. By the uniqueness of characteristic function, Sn

\sigma\sqrt n converges in

distribution to N( 0,1)\hfill $\square$

Based on the central limit theorem, we have the following approximations of

binomial and Poisson distributions using normal distribution.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

/-- Theorem 14.7 in the existential weak-limit form exported by Lévy's
continuity theorem.  The pointwise characteristic-function convergence is
supplied by the support layer. -/
theorem thm_14_7_weakLimit_by_Levy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (mu sigma : ℝ)
    (hX : ∀ k : ℕ, AEMeasurable (X k) P)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hIdent : ∀ k : ℕ, IdentDistrib (X k) (X 0) P P)
    (hIntegrable : Integrable (X 0) P)
    (hSquareIntegrable : Integrable (fun ω => (X 0 ω) ^ 2) P)
    (hMean : P[X 0] = mu)
    (hVariance : ProbabilityTheory.variance (X 0) P = sigma ^ 2)
    (hsigma : 0 < sigma) :
    thm_14_1_weakLimit (thm_14_7_standardizedSumLaws P X mu sigma hX) := by
  have hChar :=
    thm_14_7_pointwiseCharacteristicConvergence
      P X mu sigma hX hIndep hIdent hIntegrable hSquareIntegrable hMean
      hVariance hsigma
  have hLimit :
      thm_14_1_limitIsCharacteristic thm_14_7_standardNormalCharacteristic := by
    refine ⟨thm_14_7_standardNormalLaw, ?_⟩
    intro t
    exact (thm_14_7_standardNormalLaw_characteristic t).symm
  exact (thm_14_1_weak_iff_characteristic hChar).2 hLimit

/-- Theorem 14.7: for an iid real-valued sequence with finite mean `mu` and
finite positive variance `sigma ^ 2`, the standardized sums converge in
distribution to the standard normal law. -/
theorem thm_14_7
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (mu sigma : ℝ)
    (hX : ∀ k : ℕ, AEMeasurable (X k) P)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hIdent : ∀ k : ℕ, IdentDistrib (X k) (X 0) P P)
    (hIntegrable : Integrable (X 0) P)
    (hSquareIntegrable : Integrable (fun ω => (X 0 ω) ^ 2) P)
    (hMean : P[X 0] = mu)
    (hVariance : ProbabilityTheory.variance (X 0) P = sigma ^ 2)
    (hsigma : 0 < sigma) :
    Tendsto (thm_14_7_standardizedSumLaws P X mu sigma hX)
      atTop (𝓝 thm_14_7_standardNormalLaw) :=
by
  have hChar :=
    thm_14_7_pointwiseCharacteristicConvergence
      P X mu sigma hX hIndep hIdent hIntegrable hSquareIntegrable hMean
      hVariance hsigma
  refine
    (MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun
      (μ := thm_14_7_standardizedSumLaws P X mu sigma hX)
      (μ₀ := thm_14_7_standardNormalLaw)).2 ?_
  intro t
  have hStandard :
      charFun ((thm_14_7_standardNormalLaw : ProbabilityMeasure ℝ) : Measure ℝ) t =
        thm_14_7_standardNormalCharacteristic t := by
    simpa [thm_14_1_characteristicFunction] using
      thm_14_7_standardNormalLaw_characteristic t
  rw [hStandard]
  exact hChar t
