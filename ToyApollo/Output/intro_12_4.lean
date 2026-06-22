/-
TASK ID: intro_12_4
TYPE: Remark
SOURCE PLAN: chapter12-mmse-estimation

This parent-facing file is a non-proof textual carrier for source narrative.
It preserves the remark text for Phase 2 status accounting and exports no
mathematical dependency.
-/

/-- Textual carrier for `Application. MMSE Estimation`. -/
def intro_12_4 : String :=
  "\\subsection*{12.4 Application. MMSE Estimation}\n\nThe minimum mean-squared " ++
  "error (MMSE) criterion is a widely used approach for\n\noptimal linear " ++
  "filtering in signal processing. The Orthogonality Principle provides a\n\n" ++
  "powerful tool for deriving the linear MMSE estimator. For more details, " ++
  "readers can\n\nrefer to textbooks on estimation theory, such as [ 5]In this " ++
  "section, we will present\n\nsome examples of linear and nonlinear MMSE " ++
  "estimation.\n\n12.4.1 Linear MMSE Estimator\n\nSuppose Y , X1,X2,...,X n are " ++
  "inL2(P) We want to find a1,a 2,...,a n such that\n\nthe mean-squared error\n\n" ++
  "Y-\n\nn\\sum\n\ni=1\n\naiXi2\n\nis minimized.\n\nLet W be the space consisting of all" ++
  " linear combinations .\n\n\\sumn\n\ni=1 aiXi One can\n\ncheck that this is a " ++
  "closed subspace. By the Orthogonality Principle in Theorem12.5,\n\nwe can " ++
  "solve for ai from\n\n\\langleY-\n\nn\\sum\n\nj= 1\n\naj Xj ,Xi\\rangle= 0,for i = 1 " ++
  ",2,...,n .\n\nThis amounts to solving a system of linear equations:\n\n" ++
  "E[X1X1]E [X1X2]\\cdot\\cdot\\cdot E[X1Xn]\n\nE[X2X1]E [X2X2]\\cdot\\cdot\\cdot " ++
  "E[X2Xn]\n\n..\n\n.. ... ...\n\nE[XnX1]E [XnX2]\\cdot\\cdot\\cdot E[XnXn]\n\na1\n\na2\n\n" ++
  "..\n\nan\n\n=\n\nE[X1Y]\n\nE[X2Y]\n\n..\n\nE[XnY]\n\nWhen the matrix on the left is " ++
  "nonsingular, we can solve for ai 's. We remark that\n\nwhenX1,...,X n have " ++
  "zero mean, this matrix is the same as the covariance matrix."
