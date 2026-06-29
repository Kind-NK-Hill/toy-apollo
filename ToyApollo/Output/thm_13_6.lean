import Mathlib
import ToyApollo.Output.def_13_3
import ToyApollo.Output.thm_13_5

/-
TASK ID: thm_13_6
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-properties
TASK CONTENT:
\begin{thmbox}{13.6 (Existence of Conditional Expectation)}
\end{thmbox}

If X\in L 1(P) and \mathcal{G}is a sub-\sigma-field of \mathcal{F}, then the conditional expectation

E[X\vert\mathcal{G}] exists.

\textit{Proof} For random variable X in L2(P) , we know that the conditional expectation

of X can be obtained by the projection function.

For random variable X in L1(P) , the existence of conditional expectation is a

consequence of the Radon-Nikodym theorem because the measure \nu defined by

\nu(B)=

\int

B

XdP

is absolutely continuous with respect to measure P We can take the Radon-

Nikodym derivatived\nu/dP as the conditional expectation. \hfill $\square$

Most of the random variables we encounter have finite second moment. The

construction of conditional expectation using L2 theory and projection suffices for

most purposes. However, when a random variable is in L1 but not in. L2, we need to

use the Radon-Nikodym theorem to prove the existence. We refer readers to more

advanced textbooks, such as [ 2] and [4], for further details.

From now on, we will assume that conditional expectation for random variable

in. L1 exists.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

noncomputable section

/-- The Radon-Nikodym construction behind conditional expectation: for an
integrable real function `X`, the signed Radon-Nikodym derivative of the signed
measure `B ↦ ∫_B X dP`, restricted to the sub-sigma-field `G`, agrees almost
surely with Mathlib's conditional expectation. -/
theorem thm_13_6_rn_deriv_ae_eq_condExp {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω}
    {h𝓖 : IsSubSigmaField 𝓖 𝓕} [SigmaFinite (P.trim h𝓖)]
    {X : Ω → ℝ} (hX : @AmbientIntegrable Ω 𝓕 P X) :
    SignedMeasure.rnDeriv ((P.withDensityᵥ X).trim h𝓖) (P.trim h𝓖)
      =ᵐ[P] P[X | 𝓖] :=
  rnDeriv_ae_eq_condExp (hm := h𝓖) hX

/-- The candidate conditional expectation given by the RN/L1 construction is
`G`-measurable. -/
theorem thm_13_6_condExp_measurable {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω}
    {X : Ω → ℝ} :
    GMeasurable 𝓖 (P[X | 𝓖]) :=
  stronglyMeasurable_condExp.measurable

/-- The candidate conditional expectation is integrable. -/
theorem thm_13_6_condExp_integrable {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω} {X : Ω → ℝ} :
    @AmbientIntegrable Ω 𝓕 P (P[X | 𝓖]) :=
  integrable_condExp

/-- The defining set-integral identity for the conditional expectation
constructed by the Radon-Nikodym/L1 theory. -/
theorem thm_13_6_condExp_set_integral {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω}
    {h𝓖 : IsSubSigmaField 𝓖 𝓕} [SigmaFinite (P.trim h𝓖)]
    {X : Ω → ℝ} (hX : @AmbientIntegrable Ω 𝓕 P X)
    {B : Set Ω} (hB : IsMeasurableIn 𝓖 B) :
    ∫ ω in B, P[X | 𝓖] ω ∂P = ∫ ω in B, X ω ∂P :=
  setIntegral_condExp h𝓖 hX hB

/-- Theorem 13.6: every integrable real random variable has a conditional
expectation with respect to a sub-sigma-field. -/
theorem thm_13_6 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω}
    (h𝓖 : IsSubSigmaField 𝓖 𝓕) [SigmaFinite (P.trim h𝓖)]
    {X : Ω → ℝ} (hX : @AmbientIntegrable Ω 𝓕 P X) :
    ∃ Y : Ω → ℝ, @def_13_3 Ω 𝓕 P 𝓖 h𝓖 X Y := by
  refine ⟨P[X | 𝓖], ?_⟩
  refine ⟨hX, @thm_13_6_condExp_integrable Ω 𝓕 P 𝓖 X,
    @thm_13_6_condExp_measurable Ω 𝓕 P 𝓖 X, ?_⟩
  intro B hB
  exact @thm_13_6_condExp_set_integral Ω 𝓕 P 𝓖 h𝓖 _ X hX B hB
