import Mathlib

/-
TASK ID: prob_4_1
TYPE: Problem
SOURCE PLAN: 12_chap4_problems
TASK CONTENT:
\textbf{4.1.} Let $(\Omega, \mathcal{F})$ be a measurable space and $f$ be a function from $\Omega$ to $\mathbb{R}$. Show that if one of the following conditions hold:
\begin{itemize}
    \item $f^{-1}((\infty, a)) \in \mathcal{F}$ for all $a \in \mathbb{R}$
    \item $f^{-1}((\infty, a]) \in \mathcal{F}$ for all $a \in \mathbb{R}$
\end{itemize}
then $f$ is $(\mathcal{F}, \mathcal{B}(\mathbb{R}))$-measurable.
-/

-- WRITE FINAL LEAN CODE BELOW

theorem prob_4_1 {Ω : Type _} [MeasurableSpace Ω] (f : Ω → ℝ)
    (h :
      (∀ a : ℝ, MeasurableSet (f ⁻¹' Set.Iio a)) ∨
        (∀ a : ℝ, MeasurableSet (f ⁻¹' Set.Iic a))) :
    Measurable f := by
  rcases h with h1 | h2
  · exact measurable_of_Iio h1
  · exact measurable_of_Iic h2
