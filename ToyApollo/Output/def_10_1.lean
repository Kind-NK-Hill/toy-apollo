import Mathlib

/-
TASK ID: def_10_1
TYPE: Definition
SOURCE PLAN: chapter10-almost-sure-probability
TASK CONTENT:
\begin{defbox}{10.1}
A sequence of random variables $(X_n)_{n\geq 1}$ defined on a probability space $(\Omega,\mathcal{F},P)$ is said to converge to $X$ surely if
\[
\lim_{n\to\infty} X_n(\omega)=X(\omega)
\]
for all $\omega\in\Omega$.

A sequence of random variables $(X_n)_{n\geq 1}$ is said to converge to $X$ almost surely if there exists an event $E$ with $P(E)=1$ such that
\[
\lim_{n\to\infty} X_n(\omega)=X(\omega)
\]
for $\omega$ in $E$. In this case, we write $X_n\xrightarrow{\mathrm{a.s.}}X$ or $X_n\to X$ with probability $1$.
\end{defbox}
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory

/-- Sure convergence of a sequence of real-valued random variables: pointwise
convergence at every sample point. -/
def ConvergesSurely {Ω : Type*} (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  ∀ ω : Ω, Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))

/-- Almost sure convergence in the Mathlib-native almost-everywhere form. -/
def ConvergesAlmostSurely {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))

/-- The event-form definition from the textbook: convergence on an event of
measure one. -/
def ConvergesAlmostSurelyOnEvent {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  ∃ E : Set Ω, MeasurableSet E ∧ μ E = 1 ∧
    ∀ ω ∈ E, Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))

/-- Exported definition for Definition 10.1: the sure and almost-sure convergence
interfaces introduced by the textbook. -/
def def_10_1 :=
  (@ConvergesSurely, @ConvergesAlmostSurely, @ConvergesAlmostSurelyOnEvent)
