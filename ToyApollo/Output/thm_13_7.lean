import Mathlib
import ToyApollo.Output.def_13_3
import ToyApollo.Output.thm_13_4
import ToyApollo.Output.thm_13_6

/-
TASK ID: thm_13_7
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-properties
TASK CONTENT:
\begin{thmbox}{13.7 (Properties of Conditional Expectation)}
\end{thmbox}

Let.(\Omega, \mathcal{F},P) denote a probability space, and let \mathcal{G}be a\sigma-subfield of. \mathcal{F}:

1. If X is inL1(P) and is\mathcal{G}-measurable, thenE[X\vert\mathcal{G}]= X as. In particular ,

for any constant c,E[c\vert\mathcal{G}]= c as.

2. (Nonnegativity) IfX \geq 0 as., thenE[X\vert\mathcal{G}]\geq 0 as.

3. (Linearity) SupposeX, Y \in L1(P) and a is a constant. We have

E[X + Y\vert\mathcal{G}]= E[X\vert\mathcal{G}]+ E[Y\vert\mathcal{G}],

and

E[aX\vert\mathcal{G}]= aE[X\vert\mathcal{G}].

4. (Monotonicity) If X and Y are in L1(P) and X \leq Y as., then E[X\vert\mathcal{G}]\leq

E[Y\vert\mathcal{G}] as.

5. (Conditional triangle inequality) For random variable X inL1(P) ,

\vert\vert\vertE[X\vert\mathcal{G}]

\vert\vert\vert \leqE

[

\vertX\vert\vert \mathcal{G}

]

\textit{Proof}

(1) We verify that X is \mathcal{G}-measurable, and we can replace X by X in the defining

propertyE[ X1B]= E[X1B] for allB \in\mathcal{G}The second statement in (1) follows

because a constant random variable is \mathcal{G}-measurable for any \sigma-algebra. \mathcal{G}.

(2) SupposeX \geq 0 almost surely, and. X is a version of E[X\vert\mathcal{G}]For integern \geq 1,

take En to be the set .{ : X \leq- 1/n}, for integer n \geq 1The s e t En is

\mathcal{G}-measurable because X is \mathcal{G}-measurable. Because X is nonnegative as. by

assumption,

\int

En

X=

\int

En

X \geq 0

for all n. Hence,

0 \leq

\int

En

XdP \leq

\int

En

(

- 1

n

)

dP=- 1

nP(En).

This is possible only if P(En) = 0. Since P(En) = 0 for all n \geq 1, the event

{ X< 0}=\cup nEn must have probability zero. This proves that X\geq 0 as.

(3) For any eventB\in \mathcal{G},we have

\int

B

X=

\int

B

X. (13.6)

\int

B

Y =

\int

B

Y, (13.7)

where X and Y are versions of E[X\vert\mathcal{G}] and E[Y\vert\mathcal{G}], respectively. By adding

(13.6) and (13.7), we obtain

\int

B

Z=

\int

B

(X+ Y) =

\int

B

( X+ Y). (13.8)

Comparing with the defining property of conditional expectation for E[Z\vert\mathcal{G}],

\int

B

Z=

\int

B

Z,

where. Z denotes a version of E[Z\vert\mathcal{G}], we see that

\int

B

Z=

\int

B

( X+ Y)

for allB\in \mathcal{G}This proves Z= X+ Y as.

Similarly, we can proveE[aX\vert\mathcal{G}]= a X as.

(4) SinceY- X \geq 0 as., by the nonnegativity of conditional expectation, we have

E[Y- X \vert\mathcal{G}]\geq 0 as. By linearity, we obtain E[Y\vert\mathcal{G}]- E[X\vert\mathcal{G}]\geq 0.

(5) SinceX\leq\vert X\vert, by monotonic property of conditional expectation,

E[X\vert\mathcal{G}]\leq E[\vert X\vert\vert \mathcal{G}]as.

Similarly, from.-X\leq\vert X\vert, we derive that

-E [X\vert\mathcal{G}]= E[-X\vert\mathcal{G}]\leq E[\vert X\vert\vert \mathcal{G}]as.

This proves that the absolute value of the conditional expectation of X given \mathcal{G}

is less than or equal to the conditional expectation of \vertX\vert given. \mathcal{G}.

\hfill $\square$

The properties listed in the previous theorem all have analog in ordinary

expectation. The basic convergence theorems such as Fatou's lemma, monotone

convergence theorem, and dominated convergence theorem also have versions for

conditional expectation. However, the next three properties are unique to conditional

expectation.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

noncomputable section

/-- Property (1): if `X` is already measurable with respect to `G`, conditioning
on `G` returns `X`. -/
theorem thm_13_7_of_stronglyMeasurable {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω} (h𝓖 : IsSubSigmaField 𝓖 𝓕)
    [SigmaFinite (P.trim h𝓖)] {X : Ω → ℝ}
    (hXm : StronglyMeasurable[𝓖] X) (hXi : Integrable X P) :
    P[X | 𝓖] = X :=
  condExp_of_stronglyMeasurable h𝓖 hXm hXi

/-- Property (1), stated with the local textbook predicate from Definition
13.3. -/
theorem thm_13_7_of_GMeasurable {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω} (h𝓖 : IsSubSigmaField 𝓖 𝓕)
    [SigmaFinite (P.trim h𝓖)] {X : Ω → ℝ}
    (hXm : GMeasurable 𝓖 X) (hXi : Integrable X P) :
    P[X | 𝓖] = X :=
  have hXsm : StronglyMeasurable[𝓖] X :=
    (show Measurable[𝓖] X from hXm).stronglyMeasurable
  @thm_13_7_of_stronglyMeasurable Ω 𝓕 P 𝓖 h𝓖 _ X hXsm hXi

/-- Constant functions are already known under every sigma-field. -/
theorem thm_13_7_const {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {𝓖 : SigmaField Ω}
    (h𝓖 : IsSubSigmaField 𝓖 𝓕) (c : ℝ) :
    P[fun _ : Ω => c | 𝓖] = fun _ => c :=
  condExp_const h𝓖 c

/-- Property (2): nonnegative random variables have nonnegative conditional
expectations. -/
theorem thm_13_7_nonneg {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω} {X : Ω → ℝ}
    (hX : 0 ≤ᵐ[P] X) :
    0 ≤ᵐ[P] P[X | 𝓖] :=
  condExp_nonneg hX

/-- Property (3), additive part. -/
theorem thm_13_7_add {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω} {X Y : Ω → ℝ}
    (hX : Integrable X P) (hY : Integrable Y P) :
    P[X + Y | 𝓖] =ᵐ[P] P[X | 𝓖] + P[Y | 𝓖] :=
  condExp_add hX hY 𝓖

/-- Property (3), scalar-multiplication part. -/
theorem thm_13_7_smul {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω} (a : ℝ) (X : Ω → ℝ) :
    P[a • X | 𝓖] =ᵐ[P] a • P[X | 𝓖] :=
  condExp_smul a X 𝓖

/-- Property (4): monotonicity of conditional expectation. -/
theorem thm_13_7_mono {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω} {X Y : Ω → ℝ}
    (hX : Integrable X P) (hY : Integrable Y P) (hXY : X ≤ᵐ[P] Y) :
    P[X | 𝓖] ≤ᵐ[P] P[Y | 𝓖] :=
  condExp_mono hX hY hXY

/-- Property (5): the conditional triangle inequality. -/
theorem thm_13_7_abs_le {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω} {X : Ω → ℝ}
    (hX : Integrable X P) :
    (fun ω => |P[X | 𝓖] ω|) ≤ᵐ[P] P[fun ω => |X ω| | 𝓖] := by
  filter_upwards
    [condExp_mono hX hX.abs (ae_of_all P fun ω => le_abs_self (X ω)),
      (condExp_neg (μ := P) (f := X) (m := 𝓖)).symm.le.trans
        (condExp_mono hX.neg hX.abs (ae_of_all P fun ω => neg_le_abs (X ω))),
      condExp_nonneg (μ := P) (m := 𝓖)
        (ae_of_all P fun ω => abs_nonneg (X ω))]
    with ω hpos hneg hright
  simpa [abs_of_nonneg hright] using abs_le_abs hpos hneg

/-- Theorem 13.7, bundled as the five standard properties of conditional
expectation listed in the text. -/
theorem thm_13_7 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {𝓖 : SigmaField Ω}
    (h𝓖 : IsSubSigmaField 𝓖 𝓕) [SigmaFinite (P.trim h𝓖)] :
    (∀ X : Ω → ℝ, GMeasurable 𝓖 X → Integrable X P →
        P[X | 𝓖] = X) ∧
      (∀ c : ℝ, P[fun _ : Ω => c | 𝓖] = fun _ => c) ∧
      (∀ X : Ω → ℝ, 0 ≤ᵐ[P] X → 0 ≤ᵐ[P] P[X | 𝓖]) ∧
      (∀ X Y : Ω → ℝ, Integrable X P → Integrable Y P →
        P[X + Y | 𝓖] =ᵐ[P] P[X | 𝓖] + P[Y | 𝓖]) ∧
      (∀ (a : ℝ) (X : Ω → ℝ), P[a • X | 𝓖] =ᵐ[P] a • P[X | 𝓖]) ∧
      (∀ X Y : Ω → ℝ, Integrable X P → Integrable Y P → X ≤ᵐ[P] Y →
        P[X | 𝓖] ≤ᵐ[P] P[Y | 𝓖]) ∧
      (∀ X : Ω → ℝ, Integrable X P →
        (fun ω => |P[X | 𝓖] ω|) ≤ᵐ[P] P[fun ω => |X ω| | 𝓖]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X hXm hXi
    exact @thm_13_7_of_GMeasurable Ω 𝓕 P 𝓖 h𝓖 _ X hXm hXi
  · intro c
    exact @thm_13_7_const Ω 𝓕 P _ 𝓖 h𝓖 c
  · intro X hX
    exact @thm_13_7_nonneg Ω 𝓕 P 𝓖 X hX
  · intro X Y hX hY
    exact @thm_13_7_add Ω 𝓕 P 𝓖 X Y hX hY
  · intro a X
    exact @thm_13_7_smul Ω 𝓕 P 𝓖 a X
  · intro X Y hX hY hXY
    exact @thm_13_7_mono Ω 𝓕 P 𝓖 X Y hX hY hXY
  · intro X hX
    exact @thm_13_7_abs_le Ω 𝓕 P 𝓖 X hX
