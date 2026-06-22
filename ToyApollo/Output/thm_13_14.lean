import ToyApollo.Output.thm_13_14_support

/-
TASK ID: thm_13_14
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-continuous-random-variable
TASK CONTENT:
\begin{thmbox}{13.14}
\end{thmbox}

Suppose .(R2,\mathcal{B}(R2), P) is a probability space on R2, and X and Y denote

the x - and y -coordinates, respectively. Let g(x) denote a Borel function in

L1(P) .

Suppose the joint probability density function of X and Y is denoted by

fXY (x, y), ie., for any Borel set B in\mathcal{B}(R2), we have

P(B) =

\int

B

fXY (x,y)d\lambda(x,y),

where. \lambda is the Lebesgue measure on R2. Then, we have

E[g(X)\vertY]=

\int

R

g(x)fX\vertY (x\verty) d\lambda(x), (13.13)

where

fX\vertY (x\verty)\coloneqq fXY (x, y)

fY (y)

and

fY (y)\coloneqq

\int

R

fXY (x, y) d\lambda(x). (13.14)

In particular , if X is integrable, we can compute the conditional expecta-

tionE[X\vertY] by

E[X\vertY]=

\int

R

xfX\vertY (x, y) d\lambda(y).

We may assumefY (y)/=0 for simplicity so that we do not need to worry about

division by zero. We note that the conditional expectation E[g(X)\vertY] in (13.13) is

a\sigma(Y) -measurable function and hence is a function of y .

\textit{Proof} Let h(y)=

\int

R g(x)fX\vertY (x\verty)d\lambda(x) be the candidate function for the

conditional expectation. Our goal is to prove that, for any \sigma(Y) -measurable set B ,

the following equation holds:

\int

B

g(x)dP(x,y) =

\int

B

h(y) dP(x, y). (13.15)

Consider a special type of \sigma(Y) -measurable set of the form B= R \times[ a,b] for

some a<b Assuming we can apply Fubini's theorem to evaluate the integrals by

iterated integration, we will show that Eq. (13.15) holds for this type of set. When

B is of the form R\times[ a,b], we can express the right-hand side of (13.15) as

\int

[a,b]

\int

R

h(y)fXY (x, y) d\lambda(x)d\lambda(y)=

\int

[a,b]

h(y)

\int

R

fXY (x, y) d\lambda(x)d\lambda(y)

=

\int

[a,b]

h(y)fY (y) d\lambda(y)

=

\int

[a,b]

\int

R

g(x)fXY (x, y) d\lambda(x)d\lambda(y).

The last line is the same as the left-hand side of (13.15).

We can justify the application of Fubini's theorem by assuming that \vertg(x)\vert is

integrable, as

\int

R\times[a,b]

\vertg(x)\vertfXY (x,y)d\lambda(x,y) \leq

\int

R\timesR

\vertg(x)\vertfXY (x,y)d\lambda(x,y) < \infty .

We obtain the following equation for all closed intervals I in R:

E[g(X) 1R\timesI ]= E[h(Y) 1R\timesI ]. (13.16)

We can extend (13.16) to all Borel sets B\in \mathcal{B} (R) by appealing to the \pi-\lambda

theorem. First, we observe that the collection of all closed intervals in R form a

\pi-system P. Next, we consider the collection L consisting of subsets S of \Omega that

satisfies

E[g(X) 1R\timesS]= E[h(Y) 1R\timesS].

By what we have proved above, we know that P\subset L We can prove that L is

indeed a \lambda-system, which implies that L contains all Borel sets in R. Therefore,

(13.16) holds for all Borel sets B\in \mathcal{B} (R).

Consequently, we have E[g(X) 1C]= E[h(Y) 1C] for all \sigma(Y) -measurable

sets C This implies that h(Y) is indeed a version of the conditional expectation

E[g(X)\vertY] , as it satisfies the defining properties of the conditional expectation. \hfill $\square$

The second part of the theorem establishes the equivalence between the measure-

theoretic definition of conditional expectation and the definition typically presented

in a first course of probability for continuous random variables. By establishing this

equivalence, we demonstrate that the abstract definition of conditional expectation

generalizes the familiar notion from introductory probability theory.

While the classical approach to conditional expectation is well-suited for dealing

with continuous or discrete random variables, it is not capable of handling the case

where we wish to compute the conditional expectation of a discrete random variable

given a continuous random variable, or vice versa. In such cases, the measure-

theoretic definition provides a more general and rigorous framework for defining

conditional expectation.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Theorem 13.14: under a source-facing joint-density law, density
measurability/nonnegativity, `g(X)` integrability, and the source's nonzero
marginal simplification, the conditional-density integral is a version of
`E[g(X)|Y]`. The closed-interval Fubini calculation, kernel
measurability/integrability, and the π-λ/generator extension are internal
theorem steps. -/
theorem thm_13_14
    (P : Measure (ℝ × ℝ)) [IsProbabilityMeasure P]
    (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ)
    (hDensity : thm_13_14_jointDensityLaw P fXY)
    (hGMeas : Measurable g)
    (hDensityMeas : Measurable fXY)
    (hDensityNonneg : ∀ z : ℝ × ℝ, 0 ≤ fXY z)
    (hGWeightedInt : Integrable (fun z : ℝ × ℝ => fXY z * g z.1) volume)
    (hFY_ne_zero : ∀ y : ℝ, thm_13_14_marginalDensity fXY y ≠ 0) :
    thm_13_14_isConditionalExpectationVersion P g
      (thm_13_14_conditionalExpectationKernel fXY g) :=
  thm_13_14_from_intervalFubini_piLambda P fXY g
    hDensity hGMeas hDensityMeas hDensityNonneg hGWeightedInt
    hFY_ne_zero

/-- The particular identity case `g(x)=x`, corresponding to the displayed
formula for `E[X|Y]`. -/
theorem thm_13_14_identity
    (P : Measure (ℝ × ℝ)) [IsProbabilityMeasure P]
    (fXY : ℝ × ℝ → ℝ)
    (hDensity : thm_13_14_jointDensityLaw P fXY)
    (hXMeas : Measurable (fun x : ℝ => x))
    (hDensityMeas : Measurable fXY)
    (hDensityNonneg : ∀ z : ℝ × ℝ, 0 ≤ fXY z)
    (hXWeightedInt : Integrable (fun z : ℝ × ℝ => fXY z * z.1) volume)
    (hFY_ne_zero : ∀ y : ℝ, thm_13_14_marginalDensity fXY y ≠ 0) :
    thm_13_14_isConditionalExpectationVersion P (fun x : ℝ => x)
      (thm_13_14_identityConditionalExpectationKernel fXY) :=
  thm_13_14 P fXY (fun x : ℝ => x)
    hDensity hXMeas hDensityMeas hDensityNonneg hXWeightedInt
    hFY_ne_zero
