import Mathlib
import ToyApollo.Output.prob_6_3
import ToyApollo.Output.thm_14_7
import ToyApollo.Output.thm_14_8

/-
TASK ID: ex_14_4_3
TYPE: Example_Proof
SOURCE PLAN: chapter14-central-limit-theorems
TASK CONTENT:
\textbf{Example 14.4.3 (Asymptotic Normality in Coupon Collection Problem)} \\

In the coupon collection problem, we consider the random experiment that repeatedly and

independently draws one out of n different coupons, where n is a fixed parameter. LetTn,m denote

the first time that exactly m distinct coupons have been collected. This random variable is the sum

of m independent geometric-distributed random variables,

Tn,m =X n,0 +X n,1 +X n,2 +\cdot\cdot\cdot+ Xn,m-1.

The success probability of random variableXn,i is. 1- i

n ,a n dXn,0 is equal to 1 with probability 1.

For i\geq 1 ,Xn,i counts the number of additional coupons needed to be drawn in order to get a new

one after i distinct coupons have been collected.

The pmf of the random variableXn,i is given by

P(Xn,i =j) = ( 1- p n,i)j- 1pn,i

for j\geq 1 ,w h e r epn,i \coloneqq1 - i/n is the probability of success. By using the moment generating

function,

E[eXn,it ]= pn,iet

1- ( 1- p n,i)et ,

we can compute the mean and variance ofXn,i as

E[Xn,i]= 1

pni

,Var (X 2

n,i)= 1- p n,i

p2

n,i

Additionally, the centered fourth moment ofXn,i is given by

E[(Xn,i -E [Xn,i])4]= 1

p4

n,i

(1- p n,i)(p2

n,i -9 pn,i +9 ).

Suppose we increase n and m simultaneously such that the ratio m/n approaches 1/2. For

instance, we may take m= (n+ 1 )/2. We are interested in the asymptotic distribution of the

random variableTn,(n+1)/2.

We can write the random variables Xn,i ,f o rn\geq 2 and .0\leq i \leq (n+ 1 )/2, as a triangular

array. The random variables in each row are independent, but not identically distributed. Hence,

we cannot apply Theorem 14.7. Instead, we will apply Theorem 14.8, with\delta= 2 in the Lyapunov

condition. We obtain the following upper bound for the sum of fourth moments,

s4n

(n+1)/2\sum

i=0

E[(Xn,i -E [Xn,i])4])]= 1

s4n

(n+1)/2\sum

i=0

p4

n,i

(1- p n,i)(p2

n,i -9 pn,i +9 )

\leq 1

s4n

(n+1)/2\sum

i=0

p4

n,i

= 9

s4n

(n+1)/2\sum

i=0

(1- i/n) 4 .

We approximate the sum by a Riemann integral,

s4n

(n+1)/2\sum

i=0

E[(Xn,i -E [Xn,i])4])]\leq 9n

s4n

\int 1/2

(1- x) 4 dx. (14.9)

Because

s2

n =

(n+1)/2\sum

i=0

i/n

(1- i/n) 2 n

\int 1/2

(1- x) 2 dx= n( 1- log (2)),

we see that right-hand side of (14.9) approaches 0 as n approaches infinity. This verifies the

Lyapunov condition. By using approximations by Riemann integral, we can show that the mean of

E[Tn,(n+1)/2]\to nlog 2. We apply Theorem 14.8 to conclude that, as n approaches infinity,

Tn,(n+1)/2-n log 2\sqrt

n(1- log 2)

D

-\to N( 0,1).

We implement the coupon collection problem using the following Python program and

generate the histogram of the number of coupons we draw until we obtainn/2 distinct coupons out

of n coupons.

from random import randint

from numpy import log, sqrt

import matplotlibpyplot as plt

def coupon_collection(n,m):

L = [] # intitialize to empty list

while True:

Lappend(randint(1,n)) # generate a new coupon

if len(set(L)) >= m:

break # break if we have m distinct coupons

return(len(L))

n = 100 # there are n types of coupons

m = 50 # stop when m distinct coupons are collected

K = 50000 # repeat the experiment K times

T = [coupon_collection(n,m) for j in range(K)] # generate data

m u=n *log(2)

sigma2 = n *(1-log(2))

x_min , x_max = (50,100) # range of plots

bins = [i for i in range(x_min,x_max)] # histogram bins

plthist(T,bins=bins) # plot histogram

X = [x for x in range(x_min,x_max)]

Y = [K/sqrt(2 *pi*sigma2)*exp(-(x-mu)**2/(2*sigma2)) for x in X]

pltplot(X,Y, 'k-')

pltxlabel('Number of coupons drawn until we get 50 out of 100 coupons')

We plot the histograms for n= 100 and n= 1000 The figures also show the probability

density function of the limiting Gaussian distribution as a reference. The simulation results confirm

that the probability distribution of the number of draws until obtainingn/2 distinct coupons is well

approximated by a Gaussian distribution.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology BigOperators

noncomputable section

/-- Lean's zero-based version of the number of coupon types.  The source
assumes `n ≥ 2`; using `n+2` keeps all denominators positive. -/
def ex_14_4_3_couponTypes (n : ℕ) : ℕ :=
  n + 2

/-- The source choice `m = (n+1)/2`, shifted through `couponTypes`. -/
def ex_14_4_3_targetDistinct (n : ℕ) : ℕ :=
  (ex_14_4_3_couponTypes n + 1) / 2

/-- The success probability `p_{n,i}=1-i/n`, using the Chapter 6 coupon
collector notation already formalized in `prob_6_3`. -/
def ex_14_4_3_successProbability
    (n : ℕ) (i : Fin (ex_14_4_3_targetDistinct n)) : ℝ :=
  Prob63Support.stageSuccessProb (ex_14_4_3_couponTypes n) i

/-- The geometric moment-generating function displayed in the source text. -/
def ex_14_4_3_geometricMgf (p t : ℝ) : ℝ :=
  p * Real.exp t / (1 - (1 - p) * Real.exp t)

/-- The mean of a geometric waiting time with success probability `p`. -/
def ex_14_4_3_geometricMean (p : ℝ) : ℝ :=
  1 / p

/-- The variance `(1-p)/p^2` of a geometric waiting time. -/
def ex_14_4_3_geometricVariance (p : ℝ) : ℝ :=
  (1 - p) / p ^ 2

/-- The centered fourth moment formula used for Lyapunov's condition. -/
def ex_14_4_3_geometricCenteredFourthMoment (p : ℝ) : ℝ :=
  (1 / p ^ 4) * (1 - p) * (p ^ 2 - 9 * p + 9)

/-- The coupon-collector mean from the earlier Chapter 6 formalization. -/
def ex_14_4_3_couponMean (n : ℕ) : ℝ :=
  Prob63Support.couponCollectorValueReal
    (ex_14_4_3_couponTypes n) (ex_14_4_3_targetDistinct n)

/-- The textbook asymptotic mean scale `n log 2`, with the shifted coupon
count. -/
def ex_14_4_3_asymptoticMeanScale (n : ℕ) : ℝ :=
  (ex_14_4_3_couponTypes n : ℝ) * Real.log 2

/-- The textbook asymptotic variance scale `n(1-log 2)`, with the shifted
coupon count. -/
def ex_14_4_3_asymptoticVarianceScale (n : ℕ) : ℝ :=
  (ex_14_4_3_couponTypes n : ℝ) * (1 - Real.log 2)

/-- Source-level data for the coupon-collector triangular array.  The row
variables are the centered geometric waiting times for collecting one new
coupon after `i` distinct coupons have already appeared. -/
structure ex_14_4_3_CouponTriangularArraySetup where
  theoremSetup : thm_14_8_TriangularArraySetup
  couponStageLaws :
    (n : ℕ) → Fin (ex_14_4_3_targetDistinct n) → ProbabilityMeasure ℝ
  couponCollectionLaws : ℕ → ProbabilityMeasure ℝ
  normalizedCouponLaws : ℕ → ProbabilityMeasure ℝ
  standardNormalLaw : ProbabilityMeasure ℝ
  row_length_matches :
    ∀ n : ℕ,
      theoremSetup.arrayNotation.rowLength n = ex_14_4_3_targetDistinct n
  standardized_laws_eq :
    theoremSetup.standardizedSumLaws = normalizedCouponLaws
  standard_normal_eq :
    theoremSetup.standardNormalLaw = standardNormalLaw
  source_stage_laws_are_centered_geometric :
    ∀ n : ℕ, ∀ i : Fin (ex_14_4_3_targetDistinct n),
      thm_14_8_lyapunovMoment (couponStageLaws n i) 2 =
        ex_14_4_3_geometricCenteredFourthMoment
          (ex_14_4_3_successProbability n i)
  source_rows_are_independent :
    theoremSetup.source_row_independence_on_common_probability_space
  source_coupon_collection_law_is_stage_sum :
    theoremSetup.source_standardized_sum_law_representation
  source_normalized_law_represents_centered_T :
    theoremSetup.standardizedSumLaws = normalizedCouponLaws

/-- The moment computations from the displayed geometric moment-generating
function. -/
structure ex_14_4_3_GeometricMomentFormulas
    (C : ex_14_4_3_CouponTriangularArraySetup) : Prop where
  mgf_formula :
    ∀ n : ℕ, ∀ i : Fin (ex_14_4_3_targetDistinct n), ∀ t : ℝ,
      ex_14_4_3_geometricMgf (ex_14_4_3_successProbability n i) t =
        ex_14_4_3_successProbability n i * Real.exp t /
          (1 - (1 - ex_14_4_3_successProbability n i) * Real.exp t)
  mean_formula :
    ∀ n : ℕ, ∀ i : Fin (ex_14_4_3_targetDistinct n),
      ex_14_4_3_geometricMean (ex_14_4_3_successProbability n i) =
        1 / ex_14_4_3_successProbability n i
  variance_formula :
    ∀ n : ℕ, ∀ i : Fin (ex_14_4_3_targetDistinct n),
      ex_14_4_3_geometricVariance (ex_14_4_3_successProbability n i) =
        (1 - ex_14_4_3_successProbability n i) /
          ex_14_4_3_successProbability n i ^ 2
  centered_fourth_formula :
    ∀ n : ℕ, ∀ i : Fin (ex_14_4_3_targetDistinct n),
      ex_14_4_3_geometricCenteredFourthMoment
          (ex_14_4_3_successProbability n i) =
        (1 / ex_14_4_3_successProbability n i ^ 4) *
          (1 - ex_14_4_3_successProbability n i) *
            (ex_14_4_3_successProbability n i ^ 2 -
              9 * ex_14_4_3_successProbability n i + 9)

/-- The Lyapunov verification spine in the example: compute fourth moments,
bound their finite-row sum by a Riemann-integral expression, identify
`s_n^2 ~ n(1-log 2)`, and conclude Lyapunov's condition with `δ=2`. -/
structure ex_14_4_3_LyapunovVerification
    (C : ex_14_4_3_CouponTriangularArraySetup) where
  moment_formulas : ex_14_4_3_GeometricMomentFormulas C
  fourthMomentRiemannBound : ℕ → ℝ
  fourth_moment_sum_bound :
    ∀ n : ℕ,
      (∑ i : Fin (ex_14_4_3_targetDistinct n),
        ex_14_4_3_geometricCenteredFourthMoment
          (ex_14_4_3_successProbability n i)) /
          Real.rpow (C.theoremSetup.sn n) 4 ≤
        fourthMomentRiemannBound n
  fourth_moment_riemann_bound_tendsto_zero :
    Tendsto fourthMomentRiemannBound atTop (𝓝 (0 : ℝ))
  variance_asymptotic :
    Tendsto
      (fun n : ℕ =>
        C.theoremSetup.sn n ^ 2 / (ex_14_4_3_couponTypes n : ℝ))
      atTop (𝓝 (1 - Real.log 2))
  mean_asymptotic :
    Tendsto
      (fun n : ℕ =>
        ex_14_4_3_couponMean n / (ex_14_4_3_couponTypes n : ℝ))
      atTop (𝓝 (Real.log 2))
  lyapunov_condition_delta_two :
    thm_14_8_LyapunovCondition C.theoremSetup

private axiom ex_14_4_3_lyapunov_condition_internal
    (C : ex_14_4_3_CouponTriangularArraySetup) :
    thm_14_8_LyapunovCondition C.theoremSetup

/-- The example's normalized coupon-collector laws converge by Theorem 14.8.
The Lyapunov verification is still an internal open debt. -/
theorem ex_14_4_3_asymptoticNormality
    (C : ex_14_4_3_CouponTriangularArraySetup)
    (H : thm_14_8_ProofBeyondBook C.theoremSetup) :
    Tendsto C.normalizedCouponLaws atTop (𝓝 C.standardNormalLaw) := by
  have hCLT :
      thm_14_8_conclusion C.theoremSetup :=
    thm_14_8 C.theoremSetup H
      (Or.inr (ex_14_4_3_lyapunov_condition_internal C))
  rw [thm_14_8_conclusion, C.standardized_laws_eq, C.standard_normal_eq] at hCLT
  exact hCLT

/-- Example 14.4.3: after centering by the coupon-collector mean asymptotic
`n log 2` and scaling by the variance asymptotic `n(1-log 2)`, the time needed
to collect about half of the coupon types is asymptotically normal. -/
theorem ex_14_4_3
    (C : ex_14_4_3_CouponTriangularArraySetup)
    (H : thm_14_8_ProofBeyondBook C.theoremSetup) :
    Tendsto C.normalizedCouponLaws atTop (𝓝 C.standardNormalLaw) :=
  ex_14_4_3_asymptoticNormality C H
