import Mathlib
import ToyApollo.Output.thm_11_3

/-
TASK ID: prob_11_1
TYPE: Problem
SOURCE PLAN: chapter11-problems
TASK CONTENT:
\textbf{11.1.} Suppose r< s. Show that if E[\vertX\verts] is finite, then E[\vertX\vertr] is also finite.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

/--
Problem 11.1 in the standard `L^p` language: on a probability space, finite
`s`-moment implies finite `r`-moment whenever `r < s`.

The textbook proof is the usual finite-measure monotonicity of `L^p` norms.  In
the chapter's notation, `MemLp X p P` is exactly the assertion that
`E[|X|^p]` is finite.
-/
theorem prob_11_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : Ω → ℝ} {r s : ℕ}
    (hrs : r < s) (hs : MemLp X (s : ENNReal) P) :
    MemLp X (r : ENNReal) P := by
  exact hs.mono_exponent (by exact_mod_cast le_of_lt hrs)

/--
The weak version with `r ≤ s`, useful when later chapters refer to the same
moment-monotonicity step without a strict inequality.
-/
theorem prob_11_1_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : Ω → ℝ} {r s : ℕ}
    (hrs : r ≤ s) (hs : MemLp X (s : ENNReal) P) :
    MemLp X (r : ENNReal) P := by
  exact hs.mono_exponent (by exact_mod_cast hrs)
