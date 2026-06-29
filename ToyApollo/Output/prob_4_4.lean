import Mathlib

/-
TASK ID: prob_4_4
TYPE: Problem
SOURCE PLAN: 12_chap4_problems
TASK CONTENT:
\textbf{4.4.} Let $Z(\omega)$ be a complex random variable and $\alpha$ be a complex constant. Show that $\alpha Z(\omega)$ is a complex random variable.
-/

-- WRITE FINAL LEAN CODE BELOW

theorem prob_4_4 {Ω : Type*} [MeasurableSpace Ω]
    (Z : Ω → ℂ) (hZ : Measurable Z) (α : ℂ) :
    Measurable (fun ω => α * Z ω) := by
  exact measurable_const.mul hZ
