/-
TASK ID: rem_10_1_limsup
TYPE: Remark
SOURCE PLAN: chapter10-almost-sure-probability

This parent-facing file is a non-proof textual carrier for source narrative.
It preserves the remark text for Phase 2 status accounting and exports no
mathematical dependency.
-/

/-- Textual carrier for `Limsup Tail Formulation`. -/
def rem_10_1_limsup : String :=
  "The event $\\{\\omega:\\lvert X_n(\\omega)-X(\\omega)\\rvert>\\epsilon\\ " ++
  "\\mathrm{i.o.}\\}$ in the last theorem can be written in terms of limsup:\n\\[" ++
  "\n\\{\\omega:\\lvert X_n(\\omega)-X(\\omega)\\rvert>\\epsilon\\ \\mathrm{i.o.}\\}\n=\n" ++
  "\\bigcap_{n=1}^{\\infty}\\bigcup_{m\\geq n}\n\\{\\omega:\\lvert " ++
  "X_m(\\omega)-X(\\omega)\\rvert>\\epsilon\\}.\n\\]\nBy using the semi-continuity " ++
  "property of probability measure, we can alternately express Theorem 10.1 " ++
  "as\n\\[\nX_n\\xrightarrow{\\mathrm{a.s.}}X\n\\quad\\Longleftrightarrow\\quad\n" ++
  "\\forall \\epsilon>0,\\;\n\\lim_{n\\to\\infty}P\\left(\n\\bigcup_{m\\geq n}\n" ++
  "\\{\\omega:\\lvert X_m(\\omega)-X(\\omega)\\rvert>\\epsilon\\}\n\\right)=0.\n" ++
  "\\tag{10.1}\n\\]\nThis equation is useful to check almost sure convergence, as" ++
  " it allows us to focus on the behavior of the tails of the sequence."
