import Mathlib

/-
TASK ID: def_8_5
TYPE: Definition
SOURCE PLAN: 34_chap8_total_variation_distance
TASK CONTENT:
\begin{defbox}{8.5}
The \textit{total variation distance} of two probability measures $P$ and $Q$ on a common measurable space $(\Omega,\mathcal{F})$ is defined as
\begin{equation}
d_{TV}(P,Q)\triangleq \sup_{A\in \mathcal{F}} |P(A)-Q(A)|.
\tag{8.3}
\end{equation}
\end{defbox}
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set

/-- The total variation distance of two measures on the same measurable space, written exactly as
the textbook supremum over measurable sets. -/
noncomputable def totalVariationDistance
    {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) : ℝ :=
  sSup {d : ℝ | ∃ A : Set Ω, MeasurableSet A ∧ d = |P.real A - Q.real A|}

/-- Exported definition for Definition 8.5. -/
noncomputable def def_8_5
    {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) : ℝ :=
  totalVariationDistance P Q
