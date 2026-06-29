import Mathlib
import ToyApollo.Output.def_13_3

/-
TASK ID: thm_13_4
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-sub-sigma-algebra
TASK CONTENT:
\begin{thmbox}{13.4 (Uniqueness of Conditional Expectation)}
\end{thmbox}

If. Z1 and. Z2 are\mathcal{G}-measurable random variables that satisfy

\int

B

Z1 dP =

\int

B

Z2 dP

for allB \in\mathcal{G}, thenZ1 = Z2 as.

\textit{Proof} Let A be the event .{ : Z1() \geq Z2()}The event A is \mathcal{G}-measurable

becauseY = Z1 - Z2 is\mathcal{G}-measurable andA = Y- 1([0,\infty )).

Because A is in. \mathcal{G}and the expectation operator is linear, we have

0 =

\int

A

Z1 - Z2 dP.

However, Z1() - Z2() \geq 0 for in A. The above equation can hold only when

Z1() = Z2() almost everywhere on A, meaning that there is an event E1 \subset A

withP(E 1) = 0 such thatZ1() = Z2() for all. \in A \ E1.

Likewise, consider the event B ={ : Z1() \leq Z2()}We get Z1() =

Z2() almost everywhere on B. There is an event E2 \subset B with P(E 2) = 0 and

Z1() = Z2() for all. \in B \ E2.

We complete the proof by noting that A \cup B = \Omega andP(E 1 \cup E2) = 0. \hfill $\square$

Theorem 13.4 says that if Y is a random variable that satisfies (13.3), any other

random variable. Y' that satisfies (13.3) is equal to Y with probability 1. On the other

hand, if Y is a random variable that satisfies (13.3), then any random variable that

equals Y as. is also a solution to (13.3)A solution to (13.3) is called a version of

E[X\vert\mathcal{G}].

We illustrate the abstract definition of conditional expectation by considering the

smallest and the largest possible sub-\sigma-algebras.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

noncomputable section

/-- If two integrable `G`-measurable random variables have the same integral on
every `G`-measurable set, then they are equal almost surely. This is the
formal uniqueness principle used in Theorem 13.4. -/
theorem thm_13_4_set_integral_uniqueness {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {𝓖 : SigmaField Ω}
    (h𝓖 : IsSubSigmaField 𝓖 𝓕) {Z1 Z2 : Ω → ℝ}
    (hZ1int : @AmbientIntegrable Ω 𝓕 P Z1)
    (hZ2int : @AmbientIntegrable Ω 𝓕 P Z2)
    (hZ1meas : GMeasurable 𝓖 Z1)
    (hZ2meas : GMeasurable 𝓖 Z2)
    (hset : ∀ ⦃B : Set Ω⦄, IsMeasurableIn 𝓖 B →
      ∫ ω in B, Z1 ω ∂P = ∫ ω in B, Z2 ω ∂P) :
    Z1 =ᵐ[P] Z2 := by
  exact ae_eq_of_forall_setIntegral_eq_of_sigmaFinite'
    (μ := P) (m := 𝓖) (m0 := 𝓕) (F' := ℝ) h𝓖
    (fun B _ _ => hZ1int.integrableOn)
    (fun B _ _ => hZ2int.integrableOn)
    (fun B hB _ => hset hB)
    hZ1meas.aestronglyMeasurable hZ2meas.aestronglyMeasurable

/-- Theorem 13.4, uniqueness of conditional expectation: two versions of
`E[X | G]` are equal almost surely. -/
theorem thm_13_4 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {𝓖 : SigmaField Ω}
    {h𝓖 : IsSubSigmaField 𝓖 𝓕} {X Z1 Z2 : Ω → ℝ}
    (h1 : @def_13_3 Ω 𝓕 P 𝓖 h𝓖 X Z1)
    (h2 : @def_13_3 Ω 𝓕 P 𝓖 h𝓖 X Z2) :
    Z1 =ᵐ[P] Z2 := by
  refine @thm_13_4_set_integral_uniqueness Ω 𝓕 P _ 𝓖 h𝓖 Z1 Z2
    (@def_13_3_integrable_version Ω 𝓕 P 𝓖 h𝓖 X Z1 h1)
    (@def_13_3_integrable_version Ω 𝓕 P 𝓖 h𝓖 X Z2 h2)
    (@def_13_3_measurable Ω 𝓕 P 𝓖 h𝓖 X Z1 h1)
    (@def_13_3_measurable Ω 𝓕 P 𝓖 h𝓖 X Z2 h2) ?_
  intro B hB
  have hZ1X :
      ∫ ω in B, Z1 ω ∂P = ∫ ω in B, X ω ∂P :=
    @def_13_3_set_integral_eq Ω 𝓕 P 𝓖 h𝓖 X Z1 h1 B hB
  have hZ2X :
      ∫ ω in B, Z2 ω ∂P = ∫ ω in B, X ω ∂P :=
    @def_13_3_set_integral_eq Ω 𝓕 P 𝓖 h𝓖 X Z2 h2 B hB
  exact hZ1X.trans hZ2X.symm
