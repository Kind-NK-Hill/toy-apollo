import ToyApollo.Output.ex_14_4_3_coupon_stage_support

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

/-- The source normalization used in Example 14.4.3:
`(x - N log 2) / sqrt(N(1-log 2))`. -/
def ex_14_4_3_normalizedCouponValue (n : ℕ) (x : ℝ) : ℝ :=
  (x - ex_14_4_3_asymptoticMeanScale n) /
    Real.sqrt (ex_14_4_3_asymptoticVarianceScale n)

/-- The displayed normalized laws are the laws of the coupon-collection time
after the source centering and scaling. -/
def ex_14_4_3_TextbookNormalization
    (couponCollectionLaws normalizedCouponLaws : ℕ → ProbabilityMeasure ℝ) :
    Prop :=
  ∀ n : ℕ,
    normalizedCouponLaws n =
      ProbabilityMeasure.map (couponCollectionLaws n)
        ((by
          have hmeas : Measurable (ex_14_4_3_normalizedCouponValue n) := by
            unfold ex_14_4_3_normalizedCouponValue
            fun_prop
          exact hmeas.aemeasurable) :
          AEMeasurable (ex_14_4_3_normalizedCouponValue n)
            ((couponCollectionLaws n : ProbabilityMeasure ℝ) : Measure ℝ))

/-- Source-level data for the coupon-collector triangular array.  The row
variables are the centered geometric waiting times for collecting one new
coupon after `i` distinct coupons have already appeared. -/
structure ex_14_4_3_CouponTriangularArraySetup where
  theoremSetup : thm_14_8_TriangularArraySetup
  couponCollectionLaws : ℕ → ProbabilityMeasure ℝ
  normalizedCouponLaws : ℕ → ProbabilityMeasure ℝ
  standardNormalLaw : ProbabilityMeasure ℝ
  row_length_matches :
    ∀ n : ℕ,
      theoremSetup.arrayNotation.rowLength n = ex_14_4_3_targetDistinct n
  row_laws_are_centered_coupon_stage_laws :
    ∀ n : ℕ, ∀ i : Fin (theoremSetup.arrayNotation.rowLength n),
      theoremSetup.rowLaws n i =
        ex_14_4_3_centeredCouponStageLaw n
          (Fin.cast (row_length_matches n) i)
  standardized_laws_eq :
    theoremSetup.standardizedSumLaws = normalizedCouponLaws
  standard_normal_eq :
    theoremSetup.standardNormalLaw = standardNormalLaw
  source_rows_are_independent :
    theoremSetup.source_row_independence_on_common_probability_space
  source_coupon_collection_law_is_stage_sum :
    theoremSetup.source_standardized_sum_law_representation
  source_normalized_law_represents_centered_T :
    theoremSetup.standardizedSumLaws = normalizedCouponLaws
  textbook_normalization :
    ex_14_4_3_TextbookNormalization couponCollectionLaws normalizedCouponLaws

/-- The row Lyapunov numerator is the coupon fourth-moment sum. -/
theorem ex_14_4_3_row_lyapunov_sum_eq_coupon_fourth_sum
    (C : ex_14_4_3_CouponTriangularArraySetup) :
    ∀ n : ℕ,
      (∑ i : Fin (C.theoremSetup.arrayNotation.rowLength n),
        thm_14_8_lyapunovMoment (C.theoremSetup.rowLaws n i) 2) =
        ∑ i : Fin (ex_14_4_3_targetDistinct n),
          ex_14_4_3_geometricCenteredFourthMoment
            (ex_14_4_3_successProbability n i) := by
  intro n
  let e : Fin (C.theoremSetup.arrayNotation.rowLength n) ≃
      Fin (ex_14_4_3_targetDistinct n) :=
    finCongr (C.row_length_matches n)
  refine Fintype.sum_equiv e _ _ ?_
  intro i
  simp [e, C.row_laws_are_centered_coupon_stage_laws,
    ex_14_4_3_centeredCouponStageLaw_lyapunovMoment_eq]

/-- The triangular-array total variance is the coupon geometric variance sum. -/
theorem ex_14_4_3_totalVariance_eq_geometricVariance_sum
    (C : ex_14_4_3_CouponTriangularArraySetup) :
    ∀ n : ℕ,
      C.theoremSetup.arrayNotation.totalVariance n =
        ∑ i : Fin (ex_14_4_3_targetDistinct n),
          ex_14_4_3_geometricVariance
            (ex_14_4_3_successProbability n i) := by
  intro n
  rw [C.theoremSetup.arrayNotation.totalVariance_eq n]
  let e : Fin (C.theoremSetup.arrayNotation.rowLength n) ≃
      Fin (ex_14_4_3_targetDistinct n) :=
    finCongr (C.row_length_matches n)
  refine Fintype.sum_equiv e _ _ ?_
  intro i
  rw [C.theoremSetup.row_variance_eq_second_moment]
  simp [e, C.row_laws_are_centered_coupon_stage_laws,
    ex_14_4_3_centeredCouponStageLaw_second_moment_eq]

/-- The row variance scale grows at least linearly.  This is the lower-bound
variant of the variance-scale target allowed by Math Gate. -/
theorem ex_14_4_3_variance_scale_lower_bound
    (C : ex_14_4_3_CouponTriangularArraySetup) :
    ∀ᶠ n : ℕ in atTop,
      (ex_14_4_3_couponTypes n : ℝ) / 64 ≤
        C.theoremSetup.arrayNotation.totalVariance n := by
  filter_upwards [ex_14_4_3_index_ratio_sum_linear_lower_bound] with n hindex
  rw [ex_14_4_3_totalVariance_eq_geometricVariance_sum C n]
  exact le_trans hindex (ex_14_4_3_geometricVariance_row_sum_ge_index_sum n)

/-- The moment computations from the displayed geometric moment-generating
function. -/
structure ex_14_4_3_GeometricMomentFormulasForStage
    (n : ℕ) (i : Fin (ex_14_4_3_targetDistinct n)) : Prop where
  mgf_formula :
    ∀ t : ℝ,
      ‖(1 - ex_14_4_3_successProbability n i) * Real.exp t‖ < 1 →
        ProbabilityTheory.mgf Prob63Support.scalarStageWait
          (Prob63Support.stageMeasure (ex_14_4_3_couponTypes n)
            (ex_14_4_3_targetDistinct n)
            (ex_14_4_3_targetDistinct_pos n)
            (ex_14_4_3_targetDistinct_le_couponTypes n) i) t =
          ex_14_4_3_geometricMgf (ex_14_4_3_successProbability n i) t
  mean_formula :
    ∫ m, Prob63Support.scalarStageWait m
      ∂(Prob63Support.stageMeasure (ex_14_4_3_couponTypes n)
        (ex_14_4_3_targetDistinct n)
        (ex_14_4_3_targetDistinct_pos n)
        (ex_14_4_3_targetDistinct_le_couponTypes n) i) =
      ex_14_4_3_geometricMean (ex_14_4_3_successProbability n i)
  variance_formula :
    ∫ x, x ^ 2 ∂((ex_14_4_3_centeredCouponStageLaw n i :
      ProbabilityMeasure ℝ) : Measure ℝ) =
        ex_14_4_3_geometricVariance (ex_14_4_3_successProbability n i)
  centered_fourth_formula :
    thm_14_8_lyapunovMoment (ex_14_4_3_centeredCouponStageLaw n i) 2 =
      ex_14_4_3_geometricCenteredFourthMoment
        (ex_14_4_3_successProbability n i)

/-- The displayed geometric moment formulas hold for the concrete coupon
stage law. -/
theorem ex_14_4_3_geometric_moment_formulas_verified
    (n : ℕ) (i : Fin (ex_14_4_3_targetDistinct n)) :
    ex_14_4_3_GeometricMomentFormulasForStage n i := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    simpa [ex_14_4_3_successProbability, ex_14_4_3_geometricMgf] using
      (ex_14_4_3_stageMeasure_mgf_eq
        (n := ex_14_4_3_couponTypes n)
        (k := ex_14_4_3_targetDistinct n)
        (ex_14_4_3_targetDistinct_pos n)
        (ex_14_4_3_targetDistinct_le_couponTypes n) i
        (t := t) ht)
  · have hmean :=
      Prob63Support.stageWaitIntegral_eq
        (n := ex_14_4_3_couponTypes n)
        (k := ex_14_4_3_targetDistinct n)
        (ex_14_4_3_targetDistinct_pos n)
        (ex_14_4_3_targetDistinct_le_couponTypes n) i
    rw [hmean]
    unfold ex_14_4_3_geometricMean ex_14_4_3_successProbability
      Prob63Support.stageSuccessProb
    have hN : ((ex_14_4_3_couponTypes n : ℕ) : ℝ) ≠ 0 := by
      unfold ex_14_4_3_couponTypes
      positivity
    have hi_lt :
        i.1 < ex_14_4_3_couponTypes n :=
      lt_of_lt_of_le i.2 (ex_14_4_3_targetDistinct_le_couponTypes n)
    have hsub :
        (((ex_14_4_3_couponTypes n - i.1 : ℕ) : ℝ) =
          ((ex_14_4_3_couponTypes n : ℕ) : ℝ) - (i.1 : ℝ)) := by
      exact Nat.cast_sub (Nat.le_of_lt hi_lt)
    have hsub_ne : ((ex_14_4_3_couponTypes n - i.1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.sub_pos_of_lt hi_lt).ne'
    rw [hsub]
    field_simp [hN, hsub_ne]
  · exact ex_14_4_3_centeredCouponStageLaw_second_moment_eq n i
  · exact ex_14_4_3_centeredCouponStageLaw_lyapunovMoment_eq n i

/-- The Lyapunov verification spine in the example: compute fourth moments,
bound their finite-row sum by a Riemann-integral expression, identify
`s_n^2 ~ n(1-log 2)`, and conclude Lyapunov's condition with `δ=2`. -/
structure ex_14_4_3_LyapunovVerification
    (C : ex_14_4_3_CouponTriangularArraySetup) where
  moment_formulas :
    ∀ n : ℕ, ∀ i : Fin (ex_14_4_3_targetDistinct n),
      ex_14_4_3_GeometricMomentFormulasForStage n i
  fourth_moment_sum_bound :
    ∀ n : ℕ,
      (∑ i : Fin (ex_14_4_3_targetDistinct n),
        ex_14_4_3_geometricCenteredFourthMoment
          (ex_14_4_3_successProbability n i)) ≤
        160 * (ex_14_4_3_couponTypes n : ℝ)
  variance_linear_lower_bound :
    ∀ᶠ n : ℕ in atTop,
      (ex_14_4_3_couponTypes n : ℝ) / 64 ≤
        C.theoremSetup.arrayNotation.totalVariance n
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

/-- The fourth-moment/Riemann-sum bounds in the coupon setup imply
Lyapunov's condition with `δ = 2`. -/
theorem ex_14_4_3_lyapunov_condition_from_fourth_moment_riemann_sum
    (C : ex_14_4_3_CouponTriangularArraySetup) :
    thm_14_8_LyapunovCondition C.theoremSetup := by
  refine ⟨2, by norm_num, ?_⟩
  let q : ℕ → ℝ := fun n =>
    (∑ i : Fin (C.theoremSetup.arrayNotation.rowLength n),
      thm_14_8_lyapunovMoment (C.theoremSetup.rowLaws n i) 2) /
        Real.rpow (C.theoremSetup.sn n) (2 + (2 : ℝ))
  let b : ℕ → ℝ := fun n =>
    (160 * 4096 : ℝ) / (ex_14_4_3_couponTypes n : ℝ)
  change Tendsto q atTop (𝓝 (0 : ℝ))
  refine squeeze_zero' (f := q) (g := b) ?_ ?_ ?_
  · filter_upwards with n
    have hnum_nonneg :
        0 ≤
          ∑ i : Fin (C.theoremSetup.arrayNotation.rowLength n),
            thm_14_8_lyapunovMoment (C.theoremSetup.rowLaws n i) 2 := by
      refine Finset.sum_nonneg ?_
      intro i _hi
      unfold thm_14_8_lyapunovMoment
      exact integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg x) _
    have hden_nonneg :
        0 ≤ Real.rpow (C.theoremSetup.sn n) (2 + (2 : ℝ)) := by
      exact Real.rpow_nonneg (le_of_lt (C.theoremSetup.sn_pos n)) _
    exact div_nonneg hnum_nonneg hden_nonneg
  · filter_upwards [ex_14_4_3_variance_scale_lower_bound C] with n hvar
    have hnum_bound :
        (∑ i : Fin (C.theoremSetup.arrayNotation.rowLength n),
          thm_14_8_lyapunovMoment (C.theoremSetup.rowLaws n i) 2) ≤
          160 * (ex_14_4_3_couponTypes n : ℝ) := by
      rw [ex_14_4_3_row_lyapunov_sum_eq_coupon_fourth_sum C n]
      exact ex_14_4_3_fourth_moment_row_sum_is_O_n n
    have hsn_sq_lower :
        (ex_14_4_3_couponTypes n : ℝ) / 64 ≤ C.theoremSetup.sn n ^ 2 := by
      simpa [C.theoremSetup.sn_sq_eq_totalVariance n] using hvar
    have hsn_pos : 0 < C.theoremSetup.sn n := C.theoremSetup.sn_pos n
    have hden_eq :
        Real.rpow (C.theoremSetup.sn n) (2 + (2 : ℝ)) =
          C.theoremSetup.sn n ^ 4 := by
      norm_num
    have hden_lower :
        ((ex_14_4_3_couponTypes n : ℝ) / 64) ^ 2 ≤
          Real.rpow (C.theoremSetup.sn n) (2 + (2 : ℝ)) := by
      rw [hden_eq]
      have hsquare :
          ((ex_14_4_3_couponTypes n : ℝ) / 64) ^ 2 ≤
            (C.theoremSetup.sn n ^ 2) ^ 2 := by
        nlinarith [sq_nonneg
          (C.theoremSetup.sn n ^ 2 -
            (ex_14_4_3_couponTypes n : ℝ) / 64)]
      nlinarith
    have hden_pos :
        0 < Real.rpow (C.theoremSetup.sn n) (2 + (2 : ℝ)) := by
      exact Real.rpow_pos_of_pos hsn_pos _
    have hN_pos : 0 < (ex_14_4_3_couponTypes n : ℝ) := by
      unfold ex_14_4_3_couponTypes
      positivity
    have hsmall_den_pos :
        0 < ((ex_14_4_3_couponTypes n : ℝ) / 64) ^ 2 := by
      exact sq_pos_of_pos (div_pos hN_pos (by norm_num))
    have hquot_bound :
        (∑ i : Fin (C.theoremSetup.arrayNotation.rowLength n),
          thm_14_8_lyapunovMoment (C.theoremSetup.rowLaws n i) 2) /
            Real.rpow (C.theoremSetup.sn n) (2 + (2 : ℝ)) ≤
          (160 * (ex_14_4_3_couponTypes n : ℝ)) /
            (((ex_14_4_3_couponTypes n : ℝ) / 64) ^ 2) := by
      gcongr
    have hsimplify :
        (160 * (ex_14_4_3_couponTypes n : ℝ)) /
            (((ex_14_4_3_couponTypes n : ℝ) / 64) ^ 2) =
          (160 * 4096 : ℝ) / (ex_14_4_3_couponTypes n : ℝ) := by
      field_simp [ne_of_gt hN_pos]
      ring
    simpa [q, b, hsimplify] using hquot_bound
  · have hb :
        Tendsto
          (fun n : ℕ =>
            (160 * 4096 : ℝ) / (ex_14_4_3_couponTypes n : ℝ))
          atTop (𝓝 (0 : ℝ)) := by
      simpa [Function.comp_def, ex_14_4_3_couponTypes, Nat.cast_add] using
        (tendsto_const_div_atTop_nhds_zero_nat (160 * 4096 : ℝ)).comp
          (tendsto_add_atTop_nat 2)
    simpa [b] using hb

/-- The proved local moment and variance bounds verify Lyapunov's condition. -/
theorem ex_14_4_3_lyapunov_condition_from_proved_bounds
    (C : ex_14_4_3_CouponTriangularArraySetup) :
    thm_14_8_LyapunovCondition C.theoremSetup :=
  ex_14_4_3_lyapunov_condition_from_fourth_moment_riemann_sum C

/-- The example's normalized coupon-collector laws converge by Theorem 14.8.
The local Lyapunov branch is supplied by the fourth-moment/Riemann-sum
verification above. -/
theorem ex_14_4_3_asymptoticNormality
    (C : ex_14_4_3_CouponTriangularArraySetup)
    (H : thm_14_8_ProofBeyondBook C.theoremSetup) :
    Tendsto C.normalizedCouponLaws atTop (𝓝 C.standardNormalLaw) := by
  have hCLT :
      thm_14_8_conclusion C.theoremSetup :=
    thm_14_8 C.theoremSetup H
      (Or.inr (ex_14_4_3_lyapunov_condition_from_proved_bounds C))
  rw [thm_14_8_conclusion, C.standardized_laws_eq, C.standard_normal_eq] at hCLT
  exact hCLT

/-- Source-facing convergence statement: the displayed laws are the
textbook-normalized coupon-collection laws and they converge to the standard
normal law. -/
def ex_14_4_3_TextbookNormalizedConvergence
    (C : ex_14_4_3_CouponTriangularArraySetup) : Prop :=
  ex_14_4_3_TextbookNormalization C.couponCollectionLaws C.normalizedCouponLaws ∧
    Tendsto C.normalizedCouponLaws atTop (𝓝 C.standardNormalLaw)

/-- The source-normalized CLT assembled from the parent-owned Lyapunov proof
and the allowed Theorem 14.8 beyond-book boundary. -/
theorem ex_14_4_3_textbook_normalized_clt
    (C : ex_14_4_3_CouponTriangularArraySetup)
    (H : thm_14_8_ProofBeyondBook C.theoremSetup) :
    ex_14_4_3_TextbookNormalizedConvergence C := by
  exact ⟨C.textbook_normalization, ex_14_4_3_asymptoticNormality C H⟩

/-- Example 14.4.3: after centering by the coupon-collector mean asymptotic
`n log 2` and scaling by the variance asymptotic `n(1-log 2)`, the time needed
to collect about half of the coupon types is asymptotically normal. -/
theorem ex_14_4_3
    (C : ex_14_4_3_CouponTriangularArraySetup)
    (H : thm_14_8_ProofBeyondBook C.theoremSetup) :
    ex_14_4_3_TextbookNormalizedConvergence C :=
  ex_14_4_3_textbook_normalized_clt C H
