import Mathlib

/-
TASK ID: prob_4_12
TYPE: Problem
SOURCE PLAN: 12_chap4_problems
TASK CONTENT:
\textbf{4.12.} A real-valued function $f(x)$ is said to be \textit{upper semi-continuous} at a point $x_0$ if for any $y > f(x_0)$, there exists an open neighborhood $U$ of $x_0$ such that $f(x) < y$ for all $x$ in $U$. The function $f(x)$ is defined as upper semi-continuous if it is upper semi-continuous at every point in its domain.

Prove that an upper semi-continuous function is Borel measurable, i.e., prove that it is $(\mathcal{B}(\mathbb{R}), \mathcal{B}(\mathbb{R}))$-measurable.
-/

-- WRITE FINAL LEAN CODE BELOW

theorem prob_4_12 {f : ℝ → ℝ} (hf : UpperSemicontinuous f) :
    Measurable f := by
  exact hf.measurable
