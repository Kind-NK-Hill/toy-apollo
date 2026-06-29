import Mathlib

/-
TASK ID: thm_13_11
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-discrete-random-variable
TASK CONTENT:
\begin{thmbox}{13.11}
\end{thmbox}

Suppose X is an integrable random variable defined on a probability space

(\Omega,\mathcal{F},P) and.(Ai)\infty

i=1 be a sequence of mutually disjoint sets in \mathcal{F}Then

\infty\sum

i=1

\int

Ai

XdP =

\int

\cupiAi

XdP.

\textit{Proof} For each integer m\geq 1 ,l e t Ym =X \summ

i=1 1Ai We obviously have

\vertYm\vert\leq\vert X\vert, and since E[\vertX\vert] is finite by assumption, we can apply the dominated

convergence theorem to obtain

\infty\sum

i=1

\int

Ai

XdP = limm\to\infty

m\sum

i=1

\int

\Omega

X1Ai dP=

\int

\Omega

limm\to\infty

m\sum

i=1

X1Ai dP=

\int

\cupiAi

XdP.

This proves the equality in Theorem 13.11. \hfill $\square$

With the result in the previous theorem, we can compute the conditional

expectation given a countable partition of the sample space.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

noncomputable section

/-- Theorem 13.11: countable additivity of the integral over mutually disjoint
measurable sets. -/
theorem thm_13_11 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (A : ℕ → Set Ω)
    (hX : Integrable X P)
    (hA : ∀ i : ℕ, MeasurableSet (A i))
    (hDisjoint : Pairwise fun i j : ℕ => Disjoint (A i) (A j)) :
    (∑' i : ℕ, ∫ ω in A i, X ω ∂P) =
      ∫ ω in ⋃ i : ℕ, A i, X ω ∂P := by
  have hIntOn : IntegrableOn X (⋃ i : ℕ, A i) P := hX.integrableOn
  simpa using
    (integral_iUnion (μ := P) (f := X) hA hDisjoint hIntOn).symm
