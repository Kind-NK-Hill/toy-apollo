/-
TASK ID: rem_10_3_tv_vs_distribution
TYPE: Remark
SOURCE PLAN: chapter10-distribution-total-variation

This parent-facing file is a non-proof textual carrier for source narrative.
It preserves the remark text for Phase 2 status accounting and exports no
mathematical dependency.
-/

/-- Textual carrier for `Total Variation Versus Distribution Convergence`. -/
def rem_10_3_tv_vs_distribution : String :=
  "There is an important difference between these two modes of convergence. " ++
  "In convergence in total variation distance, the probability measures must " ++
  "be defined on the same probability space, while in convergence in " ++
  "distribution, the probability measures may be defined on different " ++
  "probability spaces. In general, convergence in total variation implies " ++
  "convergence in distribution."
