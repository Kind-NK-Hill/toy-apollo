import Mathlib
import ToyApollo.Output.def_13_3
import ToyApollo.Output.thm_13_4
import ToyApollo.Output.thm_13_6

/-
TASK ID: thm_13_8
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-properties
TASK CONTENT:
\begin{thmbox}{13.8 (Tower Property)}
\end{thmbox}

Suppose\mathcal{F}\mathcal{G} \mathcal{H} is a tower of \sigma-algebras and X is inL1(P) Then

E[X\vert\mathcal{H}]= E[E [X\vert\mathcal{G}]\vert\mathcal{H}]as.

\textit{Proof} We want to show that for all B\in \mathcal{H} ,

\int

B

E[X\vert\mathcal{H}]dP =

\int

B

E[E [X\vert\mathcal{G}]\vert\mathcal{H}]dP. (13.9)

The left-hand side is .

\int

B XdP The right-hand side is equal to .

\int

B E[X\vert\mathcal{G}]dP =\int

B XdP The first equality is due to B\in \mathcal{H} The second equality follows from

B\in \mathcal{G}Therefore, both sides of (13.9) are identical.

Since (13.9) holds for all \mathcal{H}-measurable set B , we conclude that E[E [X\vert\mathcal{G}]\vert\mathcal{H}]

is a version of the conditional expectation of X given. \mathcal{H}\hfill $\square$
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

noncomputable section

/-- In the first line of the textbook proof, the conditional expectation with
respect to `H` has the same integral as `X` on every `H`-measurable set. -/
theorem thm_13_8_left_set_integral {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓗 : SigmaField Ω}
    (h𝓗 : IsSubSigmaField 𝓗 𝓕)
    [SigmaFinite (P.trim h𝓗)]
    {X : Ω → ℝ} (hX : @AmbientIntegrable Ω 𝓕 P X)
    {B : Set Ω} (hB : IsMeasurableIn 𝓗 B) :
    ∫ ω in B, P[X | 𝓗] ω ∂P = ∫ ω in B, X ω ∂P :=
  @thm_13_6_condExp_set_integral Ω 𝓕 P 𝓗 h𝓗 _ X hX B hB

/-- The right-hand side of the textbook proof: for `B ∈ H`, first use the
definition of conditional expectation given `H`, then use `H ≤ G` to apply the
definition of conditional expectation given `G`. -/
theorem thm_13_8_right_set_integral {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 𝓗 : SigmaField Ω}
    (h𝓖 : IsSubSigmaField 𝓖 𝓕) (h𝓗 : IsSubSigmaField 𝓗 𝓕)
    (h𝓗𝓖 : IsSubSigmaField 𝓗 𝓖)
    [SigmaFinite (P.trim h𝓖)] [SigmaFinite (P.trim h𝓗)]
    {X : Ω → ℝ} (hX : @AmbientIntegrable Ω 𝓕 P X)
    {B : Set Ω} (hB : IsMeasurableIn 𝓗 B) :
    ∫ ω in B, P[P[X | 𝓖] | 𝓗] ω ∂P = ∫ ω in B, X ω ∂P := by
  calc
    ∫ ω in B, P[P[X | 𝓖] | 𝓗] ω ∂P
        = ∫ ω in B, P[X | 𝓖] ω ∂P :=
      @thm_13_6_condExp_set_integral Ω 𝓕 P 𝓗 h𝓗 _
        (P[X | 𝓖]) (@thm_13_6_condExp_integrable Ω 𝓕 P 𝓖 X) B hB
    _ = ∫ ω in B, X ω ∂P :=
      @thm_13_6_condExp_set_integral Ω 𝓕 P 𝓖 h𝓖 _ X hX B (h𝓗𝓖 hB)

/-- The iterated conditional expectation is a version of `E[X | H]`, exactly as
the last sentence of the textbook proof states. -/
theorem thm_13_8_iterated_condExp_is_version {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 𝓗 : SigmaField Ω}
    (h𝓖 : IsSubSigmaField 𝓖 𝓕) (h𝓗 : IsSubSigmaField 𝓗 𝓕)
    (h𝓗𝓖 : IsSubSigmaField 𝓗 𝓖)
    [SigmaFinite (P.trim h𝓖)] [SigmaFinite (P.trim h𝓗)]
    {X : Ω → ℝ} (hX : @AmbientIntegrable Ω 𝓕 P X) :
    @def_13_3 Ω 𝓕 P 𝓗 h𝓗 X (P[P[X | 𝓖] | 𝓗]) := by
  refine ⟨hX, @thm_13_6_condExp_integrable Ω 𝓕 P 𝓗 (P[X | 𝓖]),
    @thm_13_6_condExp_measurable Ω 𝓕 P 𝓗 (P[X | 𝓖]), ?_⟩
  intro B hB
  exact @thm_13_8_right_set_integral Ω 𝓕 P 𝓖 𝓗 h𝓖 h𝓗 h𝓗𝓖 _ _ X hX B hB

/-- Textbook proof assembled through Definition 13.3 and Theorem 13.4: the
iterated conditional expectation is the same version, almost surely. -/
theorem thm_13_8_via_versions {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {𝓖 𝓗 : SigmaField Ω}
    (h𝓖 : IsSubSigmaField 𝓖 𝓕) (h𝓗 : IsSubSigmaField 𝓗 𝓕)
    (h𝓗𝓖 : IsSubSigmaField 𝓗 𝓖)
    [SigmaFinite (P.trim h𝓖)] [SigmaFinite (P.trim h𝓗)]
    {X : Ω → ℝ} (hX : @AmbientIntegrable Ω 𝓕 P X) :
    P[X | 𝓗] =ᵐ[P] P[P[X | 𝓖] | 𝓗] := by
  have h_left : @def_13_3 Ω 𝓕 P 𝓗 h𝓗 X (P[X | 𝓗]) := by
    refine ⟨hX, @thm_13_6_condExp_integrable Ω 𝓕 P 𝓗 X,
      @thm_13_6_condExp_measurable Ω 𝓕 P 𝓗 X, ?_⟩
    intro B hB
    exact @thm_13_8_left_set_integral Ω 𝓕 P 𝓗 h𝓗 _ X hX B hB
  have h_right : @def_13_3 Ω 𝓕 P 𝓗 h𝓗 X (P[P[X | 𝓖] | 𝓗]) :=
    @thm_13_8_iterated_condExp_is_version Ω 𝓕 P 𝓖 𝓗 h𝓖 h𝓗 h𝓗𝓖 _ _ X hX
  exact @thm_13_4 Ω 𝓕 P _ 𝓗 h𝓗 X (P[X | 𝓗]) (P[P[X | 𝓖] | 𝓗])
    h_left h_right

/-- Theorem 13.8, the tower property of conditional expectation. -/
theorem thm_13_8 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {𝓖 𝓗 : SigmaField Ω}
    (h𝓖 : IsSubSigmaField 𝓖 𝓕) (h𝓗𝓖 : IsSubSigmaField 𝓗 𝓖)
    [SigmaFinite (P.trim h𝓖)] {X : Ω → ℝ}
    (hX : @AmbientIntegrable Ω 𝓕 P X) :
    P[X | 𝓗] =ᵐ[P] P[P[X | 𝓖] | 𝓗] := by
  have h𝓗 : IsSubSigmaField 𝓗 𝓕 := fun {A} hA => h𝓖 (h𝓗𝓖 hA)
  haveI : SigmaFinite (P.trim h𝓗) := inferInstance
  exact @thm_13_8_via_versions Ω 𝓕 P _ 𝓖 𝓗 h𝓖 h𝓗 h𝓗𝓖 _ _ X hX
