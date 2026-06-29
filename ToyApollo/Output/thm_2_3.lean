import Mathlib
import ToyApollo.Output.def_2_5

/-
TASK ID: thm_2_3
TYPE: Theorem_with_Proof
SOURCE PLAN: 42_chap2_measure_functions
TASK CONTENT:
\begin{thmbox}{2.3 (Finite Subadditivity)}
Let $(\Omega,\mathcal{F},\mu)$ be a measure space, and suppose $A$ and $B$ are $\mathcal{F}$-measurable sets. Then
\[
\mu(A\cup B)\le \mu(A)+\mu(B).
\]
\end{thmbox}

\textit{Proof} $\mu(A\cup B)=\mu(A \uplus (B\setminus A))=\mu(A)+\mu(B\setminus A)\le \mu(A)+\mu(B)$. \hfill $\square$

The next general property is about an increasing and decreasing sequence of events.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set

/-- Exported theorem for finite subadditivity of measures. -/
theorem thm_2_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A B : Set Ω) :
    μ (A ∪ B) ≤ μ A + μ B := by
  simpa using measure_union_le A B
