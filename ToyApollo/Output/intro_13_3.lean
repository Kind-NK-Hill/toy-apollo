/-
TASK ID: intro_13_3
TYPE: Remark
SOURCE PLAN: chapter13-properties

This parent-facing file is a non-proof textual carrier for source narrative.
It preserves the remark text for Phase 2 status accounting and exports no
mathematical dependency.
-/

/-- Textual carrier for `Properties of Conditional Expectation`. -/
def intro_13_3 : String :=
  "\\subsection*{13.3 Properties of Conditional Expectation}\n\nIn this section," ++
  " we consider a probability space .(\\Omega, \\mathcal{F},P) and a " ++
  "sub-\\sigma-field. \\mathcal{G}of. \\mathcal{F}.\n\nWe first address the " ++
  "existence of conditional expectation, which follows from the\n\n" ++
  "Radon-Nikodym theorem.\n\nLet \\mu and \\nu be measures defined on the same " ++
  "measurable space. We say that\n\nmeasure \\nu is absolutely continuous with " ++
  "respect to measure \\mu if \\mu(A)= 0\n\n\\nu(A)= 0 This is denoted by \\nu\\ll " ++
  "\\mu .\n\nFor example, a continuous-type distribution is absolutely " ++
  "continuous with respect\n\nto the Lebesgue measure. The theorem by Radon and" ++
  " Nikodym provides a partial\n\nconverse result. We state it below without " ++
  "proof."
