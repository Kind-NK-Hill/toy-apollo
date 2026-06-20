import ToyApollo.Output.thm_11_7_support

/-
TASK ID: thm_11_7
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter11-strong-law-large-numbers
TASK CONTENT:
\begin{thmbox}{11.7 (4th-moment Strong Law of Large Numbers)}
\end{thmbox}

Suppose Xi ,f o r i\geq 1 , are independent random variables with mean \mu and

E[X4

i ]\leq c< \infty for all i Then Sn

n \to \mu almost surely.

\textit{Proof} Without loss of generality, we assume that \mu= 0 . (We can consider Yi =

Xi -\mu if the mean of Xi is not zero.)

The expectation of S4

n can be expanded as

E[S4

n]= E[(X1 +X 2 +\cdot\cdot\cdot+ Xn)4]

=E

[ n\sum

i=1

X4

i +3

\sum

i/=j

X2

i X2

j +4

\sum

i/=j

XiX3

j

+6

\sum

i,j,k

i,j,kdistinct

XiXj X2

k +

\sum

i,j,k,\ell

i,j,k,\elldistinct

XiXj XkX\ell

]

We analyze the terms one by one. For distinct indices i , j , k , and \ell,we have

E[XiXj XkX\ell]= E[XiXj X2

k]= E[XiX3

j ]= 0,

by the assumption that X1,...,X n are independent. The fourth-power terms are

bounded byE[\sumn

i=1 X4

i ]\leq nc becauseE[X4

i ]\leq c.

Fori/=j , by Cauchy-Schwarz inequality,

E[X2

i X2

j ]\leq

\sqrt

E[X4

i ]E[X4

j ]\leq \sqrt c\cdot c = c.

Hence,

3E

[ \sum

i/=j

X2

i X2

j

]

\leq3 n(n- 1 )c

This givesE[S4

n]\leq nc+ 3 n(n- 1 )c. We now fix any \epsilon> 0,

P

( \vertSn\vert

n >\epsilon

)

=P(S 4

n >n 4\epsilon4)\leq nc+ 3 n(n- 1 )c

n4\epsilon4 \leq 3n2c+ nc - 3 nc

n4\epsilon4 \leq 3c

n2\epsilon4 .

Because

\infty\sum

n=1

P

( \vertSn\vert

n >\epsilon

)

\leq

\infty\sum

n=1

3c

n2\epsilon4 <\infty ,

we can apply the first Borel-Cantelli lemma (Theorem 5.8) to conclude that the

event .{\vertSn\vert/n > \epsilon io. } has probability 0. Therefore, by Theorem 10.1, Sn/n

converges to 0 almost surely. \hfill $\square$

Note that Theorem 11.7 does not assume that the random variables Xi are

identically distributed, but it requires that the 4th moments are uniformly bounded.

We state below a stronger version the strong law that assumes finite mean and

pairwise independence.
-/

-- WRITE FINAL LEAN CODE BELOW


open Filter
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal Topology

noncomputable section

/-- Final assembly for Theorem 11.7 from the fourth-moment tail summability
estimate supplied by the source expansion. -/
private theorem thm_11_7_from_tailSummability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (μ : ℝ)
    (hTail : thm_11_7_tailSummabilitySupport P X μ) :
    ConvergesAlmostSurely P (fun n => thm_11_5_sampleMean X n) (fun _ => μ) := by
  refine (thm_10_1 P (fun n => thm_11_5_sampleMean X n) (fun _ : Ω => μ)).2 ?_
  intro ε hε
  have hsum := hTail ε hε
  simpa [deviationInfinitelyOften] using
    (thm_5_8 P
      (fun n : ℕ =>
        almostSureDeviationEvent
          (fun n => thm_11_5_sampleMean X n) (fun _ : Ω => μ) n ε)
      hsum)

/--
Theorem 11.7, the fourth-moment strong law.

The exported statement keeps the source assumptions visible: independent
variables, common mean, and a uniform fourth-moment bound.  The proof first
derives the fourth-moment tail summability estimate from the printed expansion,
then Borel-Cantelli gives null infinitely-often deviation events, and Theorem
10.1 converts those events to almost-sure convergence.
-/
theorem thm_11_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (μ : ℝ)
    (hInd : def_5_10_randomVariables P X)
    (hMean : ∀ i : ℕ, P[X i] = μ)
    (hFourth : ∃ c : ℝ, thm_11_7_fourthMomentUniformBound P X μ c) :
    ConvergesAlmostSurely P (fun n => thm_11_5_sampleMean X n) (fun _ => μ) :=
  thm_11_7_from_tailSummability P X μ
    (thm_11_7_tail_summability_from_fourth_moment P X μ hInd hMean hFourth)
