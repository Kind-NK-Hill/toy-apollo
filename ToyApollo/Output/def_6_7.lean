import Mathlib

/-
TASK ID: def_6_7
TYPE: Definition
SOURCE PLAN: 22_chap6_expectation
TASK CONTENT:
\begin{defbox}{6.7}
The \textit{expectation} of a random variable $X$ is defined by
\[
E[X] \triangleq \int X\, dP,
\]
where the integral is taken over the sample space $\Omega$ with probability measure $P$.
\end{defbox}
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

namespace Def67Support

noncomputable def posPart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → EReal) : Ω → ENNReal :=
  fun ω => (X ω).toENNReal

noncomputable def negPart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → EReal) : Ω → ENNReal :=
  fun ω => (-X ω).toENNReal

noncomputable def posLIntegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → EReal) : ENNReal :=
  ∫⁻ ω, posPart X ω ∂P

noncomputable def negLIntegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → EReal) : ENNReal :=
  ∫⁻ ω, negPart X ω ∂P

noncomputable def textbookIntegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → EReal) : Option EReal :=
  if posLIntegral P X = ⊤ ∧ negLIntegral P X = ⊤ then
    none
  else
    some ((posLIntegral P X : EReal) - (negLIntegral P X : EReal))

end Def67Support

/-- Definition 6.7: expectation is the textbook integral under a probability
measure. -/
noncomputable def expectation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → EReal) : Option EReal :=
  Def67Support.textbookIntegral P X

/-- Task-level alias for Definition 6.7. -/
noncomputable def def_6_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → EReal) :
    Option EReal :=
  expectation P X
