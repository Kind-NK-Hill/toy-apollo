import Mathlib

/-
TASK ID: def_1_1
TYPE: Definition
SOURCE PLAN: 37_chap1_mixed_singular
TASK CONTENT:
\begin{defbox}{1.1}
A real-valued random variable $X$ is said to be \textit{singular} if there exists a set $S$ with length $0$ such that $X$ takes a value in $S$ with probability $1$. Similarly, a random vector $\mathbf{X}$ with values in $\mathbb{R}^n$ is called \textit{singular} if there exists a set $S$ with zero volume such that $\Pr(\mathbf{X}\in S)=1$.

The Cantor distribution is another example of singular random variables.
\end{defbox}
-/

open MeasureTheory Set

/-- A real-valued random variable is singular if it is supported with probability `1`
on a set of Lebesgue measure `0`. -/
def IsSingularRealRandomVariable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) :
    Prop :=
  ∃ S : Set ℝ, volume S = 0 ∧ P (X ⁻¹' S) = 1

/-- A random vector is singular if it is supported with probability `1`
on a subset of Euclidean space with volume `0`. -/
def IsSingularRandomVector {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : Ω → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ S : Set (EuclideanSpace ℝ (Fin n)), volume S = 0 ∧ P (X ⁻¹' S) = 1

/-- Exported definition for Definition 1.1. -/
def def_1_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) : Prop :=
  IsSingularRealRandomVariable P X
