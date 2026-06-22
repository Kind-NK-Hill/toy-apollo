/-
TASK ID: intro_10_4
TYPE: Remark
SOURCE PLAN: chapter10-random-vectors

This parent-facing file is a non-proof textual carrier for source narrative.
It preserves the remark text for Phase 2 status accounting and exports no
mathematical dependency.
-/

/-- Textual carrier for `Convergence of Random Vectors`. -/
def intro_10_4 : String :=
  "\\subsection*{10.4 Convergence of Random Vectors}\n\nIn this section, we " ++
  "formally establish the relationship between the convergence of random " ++
  "vectors and the convergence of their component random variables.\n\nConsider" ++
  " measurable functions that take value in $\\mathbb{R}^d$. Let " ++
  "$(\\Omega,\\mathcal{F},P)$ denote a probability space and $V(\\omega)$ denote" ++
  " a measurable mapping from $(\\Omega,\\mathcal{F})$ to " ++
  "$(\\mathbb{R}^d,\\mathcal{B}(\\mathbb{R}^d))$. We can prove that a vector " ++
  "function is measurable if and only if each component is a measurable " ++
  "function. This result in measure theory is known as the coordinate-wise " ++
  "convergence theorem."
