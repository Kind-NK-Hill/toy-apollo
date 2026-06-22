import ToyApollo.Output.thm_13_18_support

/-
TASK ID: thm_13_18
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-martingale-stopping-time
TASK CONTENT:
\begin{thmbox}{13.18 (Martingale Stopping Theorem)}
\end{thmbox}

Let .(Xn)\infty

n=0 be a martingale and T be a stopping time relative to filtration

(\mathcal{F}n)\infty

n=0. Then

E[XT ]= E[X0]

if one of the following thee conditions hold:

(i) T is bounded by a constant C almost surely.

(ii) T is almost surely finite, and there exists a constant K such that \vertXn\vert\leq K

for all n .

(iii) E[T] < \infty , and there exists a constant c such that \vertXn -X n- 1\vert\leq c for

all n .

\textit{Proof} Under conditions (i), (ii), or (iii), the stopping time T is finite with

probability 1. Therefore, XT is well-defined almost surely and XT n \to X T as.

asn\to\infty .

(i) The martingale is stopped before time C as. We have XT =X C as. Hence,

E[XT ]= E[XC]= E[X0].

(ii) Since \vertXT n\vert is bounded by a constant for all n , by applying the dominated

convergence theorem, we obtain

limn\to\infty E[XT n]= E[Xlimn(T n)]= E[XT ].

In the second equality, we have used the assumption that T is finite as. and

thus limn(T n) = T as. From Theorem 13.17, we know that E[XT n]=

E[XT

n ]= E[X0] for all n Therefore,E[XT ]= E[X0].

(iii) SupposeE[T] is finite, and there exists a constant c such that. \vertXn -Xn- 1\vert\leq c

for all n We writeXT n as a telescoping sum

XT n =X 0 +

T n\sum

k=1

(Xk -X k- 1).

The number of terms is random but is no larger than n with probability 1.

Hence, we are dealing with finitely many additions in the calculation of XT n.

Using the bounded difference assumption, we obtain

\vertXT n\vert\leq\vert X0\vert+

T n\sum

k=1

\vertXk -X k- 1\vert\leq\vert X0\vert+ c\cdot (T n) \leq\vert X0\vert+ cT.

The right-hand side is integrable because both X0 and T are integrable. By

the dominated convergence theorem, we conclude that limn\to\infty E[XT n]=

E[XT ]Since E[XT n]= E[X0] for all n by Theorem 13.17, we obtain

E[XT ]= E[X0]\hfill $\square$

The next example is commonly known as the ABRACADABRA problem [ 10].
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Filter
open scoped ProbabilityTheory Topology

noncomputable section

/-- Theorem 13.18: Martingale Stopping Theorem.  The stopped-process
integrability and adaptedness facts are supplied by Theorem 13.17; `hOptional`
is exactly one of the three textbook routes that identifies the finite stopped
expectations with the stopped value. -/
theorem thm_13_18 {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    {T : Ω → WithTop ℕ} {XT : Ω → ℝ}
    (hM : def_13_7 P 𝓕n X) (hT : def_13_8 𝓕n T)
    (hSigmaFinite :
      ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n)))
    (hOptional : thm_13_18_optionalStoppingCases P X T XT) :
    ∫ ω, XT ω ∂P = ∫ ω, X 0 ω ∂P := by
  have hConst :
      ∀ n : ℕ,
        ∫ ω, def_13_9_stoppedProcess X T n ω ∂P =
          ∫ ω, X 0 ω ∂P :=
    thm_13_17_expectation_constant hM hT hSigmaFinite
  have hStoppedMeas :
      ∀ n : ℕ,
        AEStronglyMeasurable (def_13_9_stoppedProcess X T n) P := by
    intro n
    exact (thm_13_17_stoppedProcess_integrable hM hT n).aestronglyMeasurable
  rcases hOptional with hBounded | hRest
  · exact thm_13_18_bounded_case hConst hBounded
  · rcases hRest with hUniform | hIncrement
    · exact thm_13_18_uniformBound_case hStoppedMeas hConst hUniform
    · exact thm_13_18_boundedIncrement_case hM hStoppedMeas hConst hIncrement

/-- Canonical form of Theorem 13.18, where the stopped value is constructed
internally from `X` and `T` instead of being passed as an arbitrary
representative. -/
theorem thm_13_18_canonical {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    {T : Ω → WithTop ℕ}
    (hM : def_13_7 P 𝓕n X) (hT : def_13_8 𝓕n T)
    (hSigmaFinite :
      ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n)))
    (hOptional : thm_13_18_optionalStoppingCasesCanonical P X T) :
    ∫ ω, thm_13_18_stoppedValueReal X T ω ∂P =
      ∫ ω, X 0 ω ∂P :=
  thm_13_18 hM hT hSigmaFinite
    (thm_13_18_optionalStoppingCases_of_canonical hOptional)
