import Mathlib
import ToyApollo.Output.thm_13_8
import ToyApollo.Output.def_13_7

/-
TASK ID: thm_13_15
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-martingale-stopping-time
TASK CONTENT:
\begin{thmbox}{13.15}
\end{thmbox}

In Definition 13.7, we can replace the third condition by

E[Xm\vert\mathcal{F}n]= Xn as. for allm \geq n. (13.18)

\textit{Proof} To show that (13.18) implies the third condition in Definition 13.7, we can

take m= n + 1 To prove the reverse direction, suppose m\geq n + 1 B yt h e

tower property (Theorem 13.8), we have E[Xm\vert\mathcal{F}n]= E[E[Xm\vert\mathcal{F}m- 1]\vert\mathcal{F}n]=

E[Xm- 1\vert\mathcal{F}n] as. Repeating this argument, we obtain E[Xm\vert\mathcal{F}n] = \cdot\cdot\cdot =

E[Xn+1\vert\mathcal{F}n]= Xn as. \hfill $\square$

In a martingale, the unconditioned expectation E[Xn] remains constant for all n .
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped ProbabilityTheory

noncomputable section

/-- Equation (13.18): the multi-step version of the martingale condition,
`E[X_m | F_n] = X_n` whenever `m >= n`. -/
def thm_13_15_multiStepCondition {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕n : ℕ → MeasurableSpace Ω)
    (X : ℕ → Ω → ℝ) : Prop :=
  ∀ n m : ℕ, n ≤ m → P[X m | 𝓕n n] =ᵐ[P] X n

/-- The multi-step condition implies the one-step condition by taking
`m = n + 1`, as in the first direction of the textbook proof. -/
theorem thm_13_15_oneStep_of_multiStep {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (hMulti : thm_13_15_multiStepCondition P 𝓕n X) :
    def_13_7_oneStepCondition P 𝓕n X := by
  intro n
  exact hMulti n (n + 1) (Nat.le_succ n)

/-- The equal-time conditional expectation identity used as the base of the
tower-property descent. It follows from adaptedness and integrability. -/
theorem thm_13_15_condExp_self {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (hM : def_13_7 P 𝓕n X)
    (hSigmaFinite : ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n)))
    (n : ℕ) :
    P[X n | 𝓕n n] =ᵐ[P] X n := by
  have hfiltration := def_13_7_isFiltration hM
  haveI : SigmaFinite (P.trim (hfiltration.1 n)) := hSigmaFinite n
  have hcond :
      P[X n | 𝓕n n] = X n :=
    condExp_of_stronglyMeasurable (hfiltration.1 n)
      ((def_13_7_adapted hM n).stronglyMeasurable)
      (def_13_7_integrable hM n)
  rw [hcond]

/-- The reverse direction of Theorem 13.15: repeated use of the tower property
reduces `E[X_m | F_n]` one time step at a time until it reaches `X_n`. -/
theorem thm_13_15_multiStep_of_martingale {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (hM : def_13_7 P 𝓕n X)
    (hSigmaFinite : ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n))) :
    thm_13_15_multiStepCondition P 𝓕n X := by
  intro n m hnm
  revert n
  induction m with
  | zero =>
      intro n hnm
      have hn : n = 0 := Nat.eq_zero_of_le_zero hnm
      subst n
      exact thm_13_15_condExp_self hM hSigmaFinite 0
  | succ m ih =>
      intro n hnm
      rcases Nat.lt_or_eq_of_le hnm with hlt | heq
      · have hnle_m : n ≤ m := Nat.le_of_lt_succ hlt
        have hfiltration := def_13_7_isFiltration hM
        have hle_nm : 𝓕n n ≤ 𝓕n m :=
          hfiltration.2 n m hnle_m
        haveI : SigmaFinite (P.trim (hfiltration.1 m)) :=
          hSigmaFinite m
        have htower :
            P[P[X (m + 1) | 𝓕n m] | 𝓕n n] =ᵐ[P]
              P[X (m + 1) | 𝓕n n] :=
          condExp_condExp_of_le hle_nm (hfiltration.1 m)
        have hstep : P[X (m + 1) | 𝓕n m] =ᵐ[P] X m :=
          def_13_7_condExp_succ hM m
        calc
          P[X (m + 1) | 𝓕n n]
              =ᵐ[P] P[P[X (m + 1) | 𝓕n m] | 𝓕n n] := htower.symm
          _ =ᵐ[P] P[X m | 𝓕n n] := condExp_congr_ae hstep
          _ =ᵐ[P] X n := ih n hnle_m
      · subst n
        exact thm_13_15_condExp_self hM hSigmaFinite (m + 1)

/-- Theorem 13.15: in Definition 13.7, the one-step martingale condition can be
replaced by the multi-step conditional expectation identity (13.18). -/
theorem thm_13_15 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (hfiltration : def_13_6_isFiltration (𝓕 := 𝓕) 𝓕n)
    (hIntegrable : ∀ n : ℕ, Integrable (X n) P)
    (hAdapted : def_13_6_adapted 𝓕n X)
    (hSigmaFinite : ∀ n : ℕ, SigmaFinite (P.trim (hfiltration.1 n))) :
    def_13_7_oneStepCondition P 𝓕n X ↔
      thm_13_15_multiStepCondition P 𝓕n X := by
  constructor
  · intro hOne
    have hM : def_13_7 P 𝓕n X :=
      ⟨hfiltration, hIntegrable, hAdapted, hOne⟩
    exact thm_13_15_multiStep_of_martingale hM hSigmaFinite
  · intro hMulti
    exact thm_13_15_oneStep_of_multiStep hMulti
