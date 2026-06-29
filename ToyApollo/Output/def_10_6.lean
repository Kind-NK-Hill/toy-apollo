import Mathlib
import ToyApollo.Output.def_10_1
import ToyApollo.Output.def_10_2
import ToyApollo.Output.thm_10_9

/-
TASK ID: def_10_6
TYPE: Definition
SOURCE PLAN: chapter10-random-vectors
TASK CONTENT:
\begin{defbox}{10.6}
Let $(\Omega,\mathcal{F},P)$ denote a probability space, and let $V_n(\omega)$ be a sequence of $d$-dimensional random vectors defined on $\Omega$. The sequence of random vectors $V_n(\omega)$ is said to converge almost surely to $V(\omega)$ if there is an event $E$ with $P(E)=1$ such that
\[
\lim_{n\to\infty}V_n(\omega)=V(\omega)
\]
for all $\omega\in E$.

We say that $V_n(\omega)$ converges in probability to $V(\omega)$ if for all $\epsilon>0$, the probability
\[
P(\{\omega:\lVert V_n(\omega)-V(\omega)\rVert>\epsilon\})
\]
approaches zero as $n\to\infty$.
\end{defbox}
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory

/-- Almost sure convergence of random vectors, in the textbook event-of-probability
one form. -/
def VectorConvergesAlmostSurely {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (μ : Measure Ω)
    (Vn : ℕ → Ω → Fin d → ℝ) (V : Ω → Fin d → ℝ) : Prop :=
  ∃ E : Set Ω, MeasurableSet E ∧ μ E = 1 ∧
    ∀ ω ∈ E, Tendsto (fun n : ℕ => Vn n ω) atTop (nhds (V ω))

/-- The event that the `n`-th random vector is more than `ε` away from its
candidate limit in Euclidean norm. -/
def vectorDeviationEvent {Ω : Type*} {d : ℕ} (Vn : ℕ → Ω → Fin d → ℝ)
    (V : Ω → Fin d → ℝ) (n : ℕ) (ε : ℝ) : Set Ω :=
  {ω : Ω | ‖Vn n ω - V ω‖ > ε}

/-- Convergence in probability for random vectors, using the Euclidean norm. -/
def VectorConvergesInProbability {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (μ : Measure Ω)
    (Vn : ℕ → Ω → Fin d → ℝ) (V : Ω → Fin d → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n : ℕ => μ (vectorDeviationEvent Vn V n ε)) atTop (nhds 0)

/-- Exported definition for Definition 10.6. -/
def def_10_6 :=
  (@VectorConvergesAlmostSurely, @VectorConvergesInProbability)
