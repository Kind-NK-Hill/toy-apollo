/-
TASK ID: rem_10_3_discontinuity_points
TYPE: Remark
SOURCE PLAN: chapter10-distribution-total-variation

This parent-facing file is a non-proof textual carrier for source narrative.
It preserves the remark text for Phase 2 status accounting and exports no
mathematical dependency.
-/

/-- Textual carrier for `Discontinuity Points in Distribution Convergence`. -/
def rem_10_3_discontinuity_points : String :=
  "In the definition of convergence in distribution, we do not need to " ++
  "consider the discontinuity points of the target cdf $F(x)$. To see why, " ++
  "consider a sequence of positive real numbers $x_1,x_2,x_3,\\ldots$ " ++
  "converging to $0$ from the right. Let\n\\[\n" ++
  "F_n(x)=\\mathbf{1}_{[x_n,\\infty)}(x)\n\\]\nbe the cumulative distribution " ++
  "function of the Dirac measure that concentrates at the point $x_n$, for " ++
  "$n\\geq 1$. We naturally regard this sequence of probability distributions " ++
  "as converging to the Dirac measure that concentrates at $x=0$. We can " ++
  "check that $F_n(0)=0$ for all $n$, hence\n\\[\n" ++
  "\\lim_{n\\to\\infty}F_n(x)=\\mathbf{1}_{(0,\\infty)}(x).\n\\]\nThe limit is not a " ++
  "Stieltjes measure function as it is not continuous from the right at " ++
  "$x=0$. However, the target cdf is $F(x)=\\mathbf{1}_{[0,\\infty)}(x)$, whose" ++
  " value at $x=0$ is different from the limit $\\lim_{n\\to\\infty}F_n(x)$. " ++
  "Because the discontinuity point $x=0$ is neglected in the definition of " ++
  "convergence in distribution, we do have $F_n(x)\\to F(x)$ in distribution."
