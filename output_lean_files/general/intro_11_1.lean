/-
TASK ID: intro_11_1
TYPE: Remark
SOURCE PLAN: chapter11-bounds-inequalities

This parent-facing file is a non-proof textual carrier for source narrative.
It preserves the remark text for Phase 2 status accounting and exports no
mathematical dependency.
-/

/-- Textual carrier for `Some Useful Bounds and Inequalities`. -/
def intro_11_1 : String :=
  "\\subsection*{11.1 Some Useful Bounds and Inequalities}\n\n11Laws of Large " ++
  "Numbers\n\nThe laws of large numbers give operational meaning to the " ++
  "expectation of a random\n\nvariable. If we generate independent realizations" ++
  " of a random variable and compute\n\ntheir mean, the weak law of large " ++
  "numbers states that the sample mean converges\n\nto the expected value in " ++
  "probability as we increase the number of samples. In\n\nthis chapter, we " ++
  "present two versions of the weak law of large numbers. The first\n\none " ++
  "assumes that the random variables have finite variance, while the second " ++
  "one\n\nassumes that the mean is finite.\n\nThe weak law has numerous " ++
  "applications. We discuss two sample applications:\n\nMonte Carlo integration" ++
  " and data compression. Monte Carlo integration is a simple\n\nbut effective " ++
  "method for approximating integral in high dimensions, which arises\n\nin " ++
  "financial computations. Data compression is a topic in information theory." ++
  " The\n\nfundamental result by Shannon on data compression is based on the " ++
  "weak law of\n\nlarge numbers. We end this chapter with a version of the " ++
  "strong law of large number\n\nthat assumes the fourth moments of the random " ++
  "variables are finite.\n\nThe first inequality is the complex version of " ++
  "Cauchy-Schwarz inequality. In the\n\nnext theorem,X* denote the complex " ++
  "conjugate of X ."
