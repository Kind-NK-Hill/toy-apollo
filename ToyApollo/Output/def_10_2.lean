import Mathlib
import ToyApollo.Output.def_10_1

/-
TASK ID: def_10_2
TYPE: Definition
SOURCE PLAN: chapter10-almost-sure-probability
TASK CONTENT:
\begin{defbox}{10.2}
A sequence of random variables $(X_n)_{n\geq 1}$ is said to converge to $X$ in probability if for any $\epsilon>0$,
\[
P(\lvert X_n-X\rvert>\epsilon)\to 0
\]
as $n\to\infty$. In this case, we write $X_n\xrightarrow{P}X$ or $X_n\to X$ in probability.
\end{defbox}
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory

/-- The event that the `n`-th random variable is more than `ε` away from the
limit random variable. -/
def deviationEvent {Ω : Type*} (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (n : ℕ) (ε : ℝ) :
    Set Ω :=
  {ω : Ω | |Xn n ω - X ω| > ε}

/-- Convergence in probability: for every positive `ε`, the probability of the
deviation event tends to zero. -/
def ConvergesInProbability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n : ℕ => μ (deviationEvent Xn X n ε)) atTop (nhds 0)

/-- Exported definition for Definition 10.2. -/
def def_10_2 :=
  @ConvergesInProbability
