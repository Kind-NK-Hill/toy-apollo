/-
TASK ID: intro_10
TYPE: Remark
SOURCE PLAN: chapter10-almost-sure-probability

This parent-facing file is a non-proof textual carrier for source narrative.
It preserves the remark text for Phase 2 status accounting and exports no
mathematical dependency.
-/

/-- Textual carrier for `Modes of Convergence`. -/
def intro_10 : String :=
  "\\section*{Modes of Convergence}\n\nTo estimate an unknown parameter, we can " ++
  "draw independent samples and obtain an estimator from the samples. A " ++
  "fundamental question is whether the estimates will converge to the " ++
  "intended value if we increase the number of samples. There are several " ++
  "ways to define convergence of random variables. A useful notion of " ++
  "convergence is almost sure (a.s.) convergence, in which the random " ++
  "variables are required to converge to a limit with probability $1$.\n\n" ++
  "Another important convergence concept is convergence in the $r$-th mean, " ++
  "where $r$ is a constant larger than or equal to $1$. When $r=1$, we " ++
  "usually call it convergence in the mean, or $L^1$ convergence. We have " ++
  "seen in the proof of the dominated convergence theorem that, under the " ++
  "conditions in the dominated convergence theorem, the sequence of random " ++
  "variables indeed converges in $L^1$. When $r=2$, this is commonly called " ++
  "mean square convergence, or convergence in quadratic mean. It has numerous" ++
  " applications in estimation and filtering.\n\nConvergence in probability is " ++
  "a weaker notion of convergence compared to a.s. convergence and " ++
  "convergence in the mean. This is the mode of convergence in the weak law " ++
  "of large numbers. The most relaxed mode of convergence is convergence in " ++
  "distribution, which is the basis of the central limit theorem. The total " ++
  "variation distance also defines a convergence concept that is useful in " ++
  "large deviation theory.\n\nAt the end of this chapter we derive the " ++
  "continuous mapping theorem for a.s. convergence and convergence in " ++
  "probability."
