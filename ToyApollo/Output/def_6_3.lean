import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-
TASK ID: def_6_3
TYPE: Definition
SOURCE PLAN: 20_chap6_nonnegative_functions
TASK CONTENT:
\begin{defbox}{6.3}
For a nonnegative measurable function $X$, we define the \textit{Lebesgue integral} of $X$ by
\[
\int X\, d\mu \triangleq \sup \left\{ \int f\, d\mu : f \text{ is simple},\ 0\le f\le X \right\}.
\]
\end{defbox}
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/--
The textbook approximation class
`S(X) = {f : f is simple, 0 ≤ f ≤ X}` for a nonnegative function `X`.
-/
def simpleApproximationSet (X : Ω → ENNReal) : Set (SimpleFunc Ω ENNReal) :=
  {f | ∀ ω, f ω ≤ X ω}

/--
Definition 6.3: the Lebesgue integral of a nonnegative measurable function,
implemented in Mathlib by `lintegral`.
-/
noncomputable def def_6_3 (μ : Measure Ω) (X : Ω → ENNReal) : ENNReal :=
  ∫⁻ ω, X ω ∂μ
