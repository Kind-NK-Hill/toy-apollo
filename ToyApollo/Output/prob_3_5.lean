import Mathlib

open MeasureTheory Set

/-
\textbf{3.5.} Let $F(x)$ be a Stieltjes measure function that corresponds to a probability measure.
Show that the set of points at which $F(x)$ has a jump discontinuity is at most countably infinite.
-/
theorem prob_3_5 (F : StieltjesFunction ℝ) (h : F.measure Set.univ = 1) :
    Set.Countable {x | ¬ContinuousAt F x} := by
      apply_rules [ Monotone.countable_not_continuousAt, F.mono ]