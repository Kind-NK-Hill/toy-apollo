import Mathlib
import ToyApollo.Output.chapter14_triangular_array_support

/-
TASK ID: thm_14_8
TYPE: Theorem_Statement
SOURCE PLAN: chapter14-central-limit-theorems
TASK CONTENT:
\begin{thmbox}{14.8 (Central Limit Theorem for Triangular Array)}
\end{thmbox}

With the notation above, we have

Xn1 +X n2 +\cdot\cdot\cdot+ Xn,kn

sn

D

-\to N( 0,1)

if one of the following conditions hold:

(Lindeberg condition) For all\epsilon> 0,

s2n

kn\sum

i=1

E[X2

n,i 1{\vertXn,i\vert\geq\epsilonsn}}]\to 0as n \to\infty .

(Lyapunov condition) There exists\delta> 0 such that

s2+\deltan

n\sum

i=1

E[\vertXn,i\vert2+\delta]\to 0as n \to\infty .

In the Lindeberg condition, the expectation is the integral

\int

{\vertx\vert\geq\epsilonsn}

x2 d\mun,i(x),

integrating the function x2 in the range \vertx\vert\geq \epsilonsn with respect to the measure

\mun,i induced by Xn,i Intuitively, this means that the tail of each Xk must decrease

fast enough so that the sum of the tail parts of the variances does not contribute

significantly to the overall variance of Sn. We remark that for independent random

variables, the conditions in the Lindeberg-Levy central limit theorem imply the

Lindeberg condition.

On the other hand, the Lyapunov condition is a stronger condition than the

Lindeberg condition. Specifically, the Lyapunov condition requires that the tail

probability of each random variable Xk decays sufficient fast so that certain power

law holds. This condition is useful in some situations where the Lindeberg condition

is difficult to check.

The proof is beyond the scope of this book. We refer the readers to [ 2] and [4].

Instead of going through the proof, we give an example and demonstrate how to

apply this theorem.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology

noncomputable section

/-- The row notation introduced immediately before Theorem 14.8. -/
abbrev thm_14_8_TriangularArrayNotation :=
  chapter14_TriangularArrayNotation

/-- The source integral
`∫_{|x| ≥ threshold} x^2 dμ`, used in the Lindeberg condition. -/
def thm_14_8_lindebergTailIntegral
    (μ : ProbabilityMeasure ℝ) (threshold : ℝ) : ℝ :=
  ∫ x in {x : ℝ | threshold ≤ |x|}, x ^ 2 ∂(μ : Measure ℝ)

/-- The Lyapunov moment `E[|X|^(2+δ)]`. -/
def thm_14_8_lyapunovMoment
    (μ : ProbabilityMeasure ℝ) (δ : ℝ) : ℝ :=
  ∫ x, Real.rpow |x| (2 + δ) ∂(μ : Measure ℝ)

/-- The law-level data for the triangular array central limit theorem.
The fields retain the textbook order: independent centered rows, variances
`σ_{n,i}^2`, row variance `s_n^2`, and the laws of the normalized row sums. -/
structure thm_14_8_TriangularArraySetup where
  arrayNotation : thm_14_8_TriangularArrayNotation
  rowLaws : (n : ℕ) → Fin (arrayNotation.rowLength n) → ProbabilityMeasure ℝ
  standardizedSumLaws : ℕ → ProbabilityMeasure ℝ
  standardNormalLaw : ProbabilityMeasure ℝ
  sn : ℕ → ℝ
  sn_pos : ∀ n : ℕ, 0 < sn n
  sn_sq_eq_totalVariance :
    ∀ n : ℕ, sn n ^ 2 = arrayNotation.totalVariance n
  sn_tendsto_atTop : Tendsto sn atTop atTop
  row_mean_zero :
    ∀ n : ℕ, ∀ i : Fin (arrayNotation.rowLength n),
      ∫ x, x ∂((rowLaws n i : ProbabilityMeasure ℝ) : Measure ℝ) = 0
  row_variance_eq_second_moment :
    ∀ n : ℕ, ∀ i : Fin (arrayNotation.rowLength n),
      arrayNotation.variance n i =
        ∫ x, x ^ 2 ∂((rowLaws n i : ProbabilityMeasure ℝ) : Measure ℝ)
  source_row_independence_on_common_probability_space : Prop
  source_standardized_sum_law_representation : Prop

/-- Lindeberg's tail condition:
`s_n^{-2} Σ_i E[X_{n,i}^2 1{|X_{n,i}| ≥ ε s_n}] -> 0`. -/
def thm_14_8_LindebergCondition
    (S : thm_14_8_TriangularArraySetup) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto
      (fun n : ℕ =>
        (∑ i : Fin (S.arrayNotation.rowLength n),
          thm_14_8_lindebergTailIntegral (S.rowLaws n i) (ε * S.sn n)) /
            (S.sn n ^ 2))
      atTop (𝓝 (0 : ℝ))

/-- Lyapunov's stronger moment condition:
for some `δ > 0`, `s_n^{-(2+δ)} Σ_i E[|X_{n,i}|^(2+δ)] -> 0`. -/
def thm_14_8_LyapunovCondition
    (S : thm_14_8_TriangularArraySetup) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    Tendsto
      (fun n : ℕ =>
        (∑ i : Fin (S.arrayNotation.rowLength n),
          thm_14_8_lyapunovMoment (S.rowLaws n i) δ) /
            Real.rpow (S.sn n) (2 + δ))
      atTop (𝓝 (0 : ℝ))

/-- The disjunction in Theorem 14.8: either Lindeberg or Lyapunov holds. -/
def thm_14_8_condition
    (S : thm_14_8_TriangularArraySetup) : Prop :=
  thm_14_8_LindebergCondition S ∨ thm_14_8_LyapunovCondition S

/-- The conclusion of Theorem 14.8: normalized row sums converge weakly to
the standard normal law. -/
def thm_14_8_conclusion
    (S : thm_14_8_TriangularArraySetup) : Prop :=
  Tendsto S.standardizedSumLaws atTop (𝓝 S.standardNormalLaw)

/-- The two proof obligations explicitly deferred by the textbook's sentence
"The proof is beyond the scope of this book."  The first is the triangular-array
CLT under Lindeberg's condition; the second is the textbook comparison showing
that Lyapunov's condition implies Lindeberg's condition. -/
structure thm_14_8_ProofBeyondBook
    (S : thm_14_8_TriangularArraySetup) : Prop where
  lindeberg_triangular_array_clt :
    thm_14_8_LindebergCondition S → thm_14_8_conclusion S
  lyapunov_implies_lindeberg :
    thm_14_8_LyapunovCondition S → thm_14_8_LindebergCondition S

/-- The Lindeberg branch of Theorem 14.8. -/
theorem thm_14_8_of_lindeberg
    (S : thm_14_8_TriangularArraySetup)
    (H : thm_14_8_ProofBeyondBook S)
    (hL : thm_14_8_LindebergCondition S) :
    thm_14_8_conclusion S :=
  H.lindeberg_triangular_array_clt hL

/-- The Lyapunov branch of Theorem 14.8, routed through the stronger-implies-
weaker comparison stated in the source text. -/
theorem thm_14_8_of_lyapunov
    (S : thm_14_8_TriangularArraySetup)
    (H : thm_14_8_ProofBeyondBook S)
    (hY : thm_14_8_LyapunovCondition S) :
    thm_14_8_conclusion S :=
  H.lindeberg_triangular_array_clt (H.lyapunov_implies_lindeberg hY)

/-- Theorem 14.8: for a centered independent triangular array with
`s_n^2 = Σ_i σ_{n,i}^2` and `s_n -> ∞`, the standardized row sums converge in
distribution to `N(0,1)` if either Lindeberg's condition or Lyapunov's condition
holds. -/
theorem thm_14_8
    (S : thm_14_8_TriangularArraySetup)
    (H : thm_14_8_ProofBeyondBook S)
    (h : thm_14_8_condition S) :
    thm_14_8_conclusion S := by
  rcases h with hL | hY
  · exact thm_14_8_of_lindeberg S H hL
  · exact thm_14_8_of_lyapunov S H hY
