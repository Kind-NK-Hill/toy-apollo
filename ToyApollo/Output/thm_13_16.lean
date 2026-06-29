import Mathlib
import ToyApollo.Output.thm_13_15

/-
TASK ID: thm_13_16
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-martingale-stopping-time
TASK CONTENT:
\begin{thmbox}{13.16}
\end{thmbox}

If.(Xn)\infty

n=0 is a martingale relative to some filtration .(\mathcal{F}n)\infty

n=0, then. E[Xn]=

E[X0] for alln\geq 1 .

\textit{Proof} Take expectation on both sides of (13.18)\hfill $\square$
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped ProbabilityTheory

noncomputable section

/-- If a conditional expectation is almost surely equal to `Y`, then taking
expectations gives `E[X] = E[Y]`. This is the formal version of "take
expectations on both sides." -/
theorem thm_13_16_integral_eq_of_condExp {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : MeasurableSpace Ω} (h𝓖 : 𝓖 ≤ 𝓕)
    [SigmaFinite (P.trim h𝓖)] {X Y : Ω → ℝ}
    (hCE : P[X | 𝓖] =ᵐ[P] Y) :
    ∫ ω, X ω ∂P = ∫ ω, Y ω ∂P := by
  calc
    ∫ ω, X ω ∂P = ∫ ω, P[X | 𝓖] ω ∂P := (integral_condExp h𝓖).symm
    _ = ∫ ω, Y ω ∂P := integral_congr_ae hCE

/-- Instantiating Theorem 13.15's multi-step condition at time `0` gives
`E[X_n | F_0] = X_0`. -/
theorem thm_13_16_condExp_zero {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (hM : def_13_7 P 𝓕n X)
    (hSigmaFinite : ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n)))
    (n : ℕ) :
    P[X n | 𝓕n 0] =ᵐ[P] X 0 := by
  exact thm_13_15_multiStep_of_martingale hM hSigmaFinite 0 n (Nat.zero_le n)

/-- Theorem 13.16: expectations of a martingale are constant. -/
theorem thm_13_16 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (hM : def_13_7 P 𝓕n X)
    (hSigmaFinite : ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n))) :
    ∀ n : ℕ, 1 ≤ n → ∫ ω, X n ω ∂P = ∫ ω, X 0 ω ∂P := by
  intro n _hn
  have hfiltration := def_13_7_isFiltration hM
  haveI : SigmaFinite (P.trim (hfiltration.1 0)) := hSigmaFinite 0
  exact thm_13_16_integral_eq_of_condExp (hfiltration.1 0)
    (thm_13_16_condExp_zero hM hSigmaFinite n)
