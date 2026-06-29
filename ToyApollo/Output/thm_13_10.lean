import Mathlib
import ToyApollo.Output.def_13_3
import ToyApollo.Output.def_13_4
import ToyApollo.Output.thm_13_4
import ToyApollo.Output.thm_13_6
import ToyApollo.Output.thm_13_7

/-
TASK ID: thm_13_10
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-properties
TASK CONTENT:
\begin{thmbox}{13.10}
\end{thmbox}

Suppose X is a random variable in .(\Omega,\mathcal{F},P) that is integrable and \mathcal{G}is a

sub-\sigma-algebra of. \mathcal{F}I f\sigma(X) and. \mathcal{G}are independent, then

E[X\vert\mathcal{G}]= E[X]as.

In particular , when X and Y are independent random variables, we have

E[X\vertY]= E[X] as.

\textit{Proof} It is sufficient to show that for each B\in \mathcal{G},

\int

B

XdP =

\int

B

E[X]dP. (13.11)

SupposeX= 1 A for some\mathcal{F}-measurable set A For any set B\in \mathcal{G}, the left-hand

side of (13.11) is

\int

B

1A dP=

\int

1A\capB dP= P(A \capB) = P(A)P(B).

On the other hand, we can write the right-hand side of (13.11) as

\int

B

E[1A]dP = E [1A]

\int

B

dP= P(A)P(B).

Therefore, (13.11) holds forX= 1 A and anyB\in \mathcal{G}.

We can extend this to simple functions, nonnegative functions, and finally to

real-valued functions. \hfill $\square$
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

noncomputable section

/-- For an event indicator, the ordinary expectation is its probability. This is
the numerical identity used in the first step of the textbook proof. -/
theorem thm_13_10_indicator_expectation {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {A : Set Ω} (hA : MeasurableSet A) :
    ∫ ω, A.indicator (fun _ : Ω => (1 : ℝ)) ω ∂P = P.real A := by
  simpa using integral_indicator_one (μ := P) (s := A) hA

/-- Indicator case of Theorem 13.10: if `sigma(1_A)` is independent of `G`,
then conditioning the event indicator on `G` gives the constant ordinary
expectation. -/
theorem thm_13_10_indicator {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω} (h𝓖 : IsSubSigmaField 𝓖 𝓕)
    [SigmaFinite (P.trim h𝓖)] {A : Set Ω} (hA : @MeasurableSet Ω 𝓕 A)
    (hindep : Indep
      (def_13_4_sigma (A.indicator (fun _ : Ω => (1 : ℝ)))) 𝓖 P) :
    P[A.indicator (fun _ : Ω => (1 : ℝ)) | 𝓖] =ᵐ[P]
      fun _ => ∫ ω, A.indicator (fun _ : Ω => (1 : ℝ)) ω ∂P := by
  let IA : Ω → ℝ := A.indicator (fun _ : Ω => (1 : ℝ))
  have hIAm : @Measurable Ω ℝ 𝓕 _ IA := by
    exact (show @Measurable Ω ℝ 𝓕 _ (fun _ : Ω => (1 : ℝ)) from
      measurable_const).indicator hA
  have hIAσ : StronglyMeasurable[def_13_4_sigma IA] IA :=
    (comap_measurable IA).stronglyMeasurable
  have hIA_sub : IsSubSigmaField (def_13_4_sigma IA) 𝓕 :=
    @def_13_4_sigma_subSigma_of_measurable Ω ℝ 𝓕 _ IA hIAm
  exact condExp_indep_eq hIA_sub h𝓖 hIAσ hindep

/-- Source-shaped bridge for Theorem 13.10.  Under independence of `sigma(X)`
and `G`, the textbook defining identity (13.11) holds on every `G`-measurable
set `B`: the integral of `X` over `B` equals the integral of the constant
ordinary expectation of `X` over `B`. -/
theorem thm_13_10_setIntegral_eq_of_indep {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω} (h𝓖 : IsSubSigmaField 𝓖 𝓕)
    [SigmaFinite (P.trim h𝓖)] {X : Ω → ℝ}
    (hXm : @Measurable Ω ℝ 𝓕 _ X) (hXi : Integrable X P)
    (hindep : Indep (def_13_4_sigma X) 𝓖 P)
    {B : Set Ω} (hB : IsMeasurableIn 𝓖 B) :
    ∫ ω in B, X ω ∂P =
      ∫ ω in B, (fun _ : Ω => ∫ ω, X ω ∂P) ω ∂P := by
  have hXσ : StronglyMeasurable[def_13_4_sigma X] X :=
    (comap_measurable X).stronglyMeasurable
  have hX_sub : IsSubSigmaField (def_13_4_sigma X) 𝓕 :=
    @def_13_4_sigma_subSigma_of_measurable Ω ℝ 𝓕 _ X hXm
  have hCE : P[X | 𝓖] =ᵐ[P] fun _ : Ω => ∫ ω, X ω ∂P :=
    condExp_indep_eq hX_sub h𝓖 hXσ hindep
  calc
    ∫ ω in B, X ω ∂P = ∫ ω in B, P[X | 𝓖] ω ∂P := by
      exact (setIntegral_condExp h𝓖 hXi hB).symm
    _ = ∫ ω in B, (fun _ : Ω => ∫ ω, X ω ∂P) ω ∂P := by
      apply setIntegral_congr_ae (h𝓖 hB)
      filter_upwards [hCE] with ω hω _hωB
      exact hω

/-- Indicator version of the source set-integral calculation in Theorem
13.10.  This lands the displayed `P(A ∩ B) = P(A)P(B)` calculation as the
conditional-expectation defining identity for `1_A`. -/
theorem thm_13_10_indicator_setIntegral_eq {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {𝓖 : SigmaField Ω}
    (h𝓖 : IsSubSigmaField 𝓖 𝓕) [SigmaFinite (P.trim h𝓖)]
    {A : Set Ω} (hA : @MeasurableSet Ω 𝓕 A)
    (hindep : Indep
      (def_13_4_sigma (A.indicator (fun _ : Ω => (1 : ℝ)))) 𝓖 P)
    {B : Set Ω} (hB : IsMeasurableIn 𝓖 B) :
    ∫ ω in B, A.indicator (fun _ : Ω => (1 : ℝ)) ω ∂P =
      ∫ ω in B,
        (fun _ : Ω => ∫ ω, A.indicator (fun _ : Ω => (1 : ℝ)) ω ∂P) ω ∂P := by
  let IA : Ω → ℝ := A.indicator (fun _ : Ω => (1 : ℝ))
  have hAσ : @MeasurableSet Ω (def_13_4_sigma IA) A := by
    have hpre : A = IA ⁻¹' ({1} : Set ℝ) := by
      ext ω
      by_cases hω : ω ∈ A <;> simp [IA, Set.indicator, hω]
    rw [hpre]
    rw [MeasurableSpace.measurableSet_comap]
    exact ⟨({1} : Set ℝ), measurableSet_singleton 1, rfl⟩
  have hBind : @MeasurableSet Ω 𝓖 B := hB
  have hABmul : P (A ∩ B) = P A * P B :=
    (hindep.indepSet_of_measurableSet hAσ hBind).measure_inter_eq_mul
  have hABreal : P.real (A ∩ B) = P.real A * P.real B := by
    rw [measureReal_def, hABmul, ENNReal.toReal_mul, ← measureReal_def,
      ← measureReal_def]
  have hleft :
      ∫ ω in B, A.indicator (fun _ : Ω => (1 : ℝ)) ω ∂P =
        P.real (A ∩ B) := by
    rw [← integral_indicator (h𝓖 hB)]
    have hfun : B.indicator (A.indicator (fun _ : Ω => (1 : ℝ))) =
        (A ∩ B).indicator (fun _ : Ω => (1 : ℝ)) := by
      ext ω
      by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;>
        simp [Set.indicator, hωA, hωB]
    rw [hfun]
    exact integral_indicator_one (μ := P) (s := A ∩ B) (hA.inter (h𝓖 hB))
  have hright :
      ∫ ω in B,
        (fun _ : Ω => ∫ ω, A.indicator (fun _ : Ω => (1 : ℝ)) ω ∂P) ω ∂P =
        P.real A * P.real B := by
    rw [setIntegral_const]
    rw [show (∫ ω, A.indicator (fun _ : Ω => (1 : ℝ)) ω ∂P) =
      P.real A from integral_indicator_one (μ := P) (s := A) hA]
    simp [smul_eq_mul, mul_comm]
  rw [hleft, hright, hABreal]

/-- Theorem 13.10: if `sigma(X)` and `G` are independent, then the conditional
expectation of integrable `X` given `G` is the constant ordinary expectation. -/
theorem thm_13_10 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω} (h𝓖 : IsSubSigmaField 𝓖 𝓕)
    [SigmaFinite (P.trim h𝓖)] {X : Ω → ℝ}
    (hXm : @Measurable Ω ℝ 𝓕 _ X) (_hXi : Integrable X P)
    (hindep : Indep (def_13_4_sigma X) 𝓖 P) :
    P[X | 𝓖] =ᵐ[P] fun _ => ∫ ω, X ω ∂P := by
  have hXσ : StronglyMeasurable[def_13_4_sigma X] X :=
    (comap_measurable X).stronglyMeasurable
  have hX_sub : IsSubSigmaField (def_13_4_sigma X) 𝓕 :=
    @def_13_4_sigma_subSigma_of_measurable Ω ℝ 𝓕 _ X hXm
  exact condExp_indep_eq hX_sub h𝓖 hXσ hindep

/-- The "in particular" form: independent random variables satisfy
`E[X | Y] = E[X]`, where conditioning on `Y` means conditioning on
`sigma(Y)`. -/
theorem thm_13_10_indepFun {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Ω → ℝ}
    (hXm : @Measurable Ω ℝ 𝓕 _ X) (hYm : @Measurable Ω ℝ 𝓕 _ Y)
    [SigmaFinite (P.trim (def_13_4_sigma_subSigma_of_measurable hYm))]
    (hXi : Integrable X P) (hindep : IndepFun X Y P) :
    P[X | def_13_4_sigma Y] =ᵐ[P] fun _ => ∫ ω, X ω ∂P := by
  have hσindep : Indep (def_13_4_sigma X) (def_13_4_sigma Y) P := by
    simpa [def_13_4_sigma] using hindep
  exact @thm_13_10 Ω 𝓕 P (def_13_4_sigma Y)
    (def_13_4_sigma_subSigma_of_measurable hYm) _ X hXm hXi hσindep
