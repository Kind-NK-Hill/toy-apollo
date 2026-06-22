/-
TASK ID: rem_10_2_relationships
TYPE: Remark
SOURCE PLAN: chapter10-mean

This parent-facing file is a non-proof textual carrier for source narrative.
It preserves the remark text for Phase 2 status accounting and exports no
mathematical dependency.
-/

/-- Textual carrier for `Mean Convergence and Almost Sure Convergence`. -/
def rem_10_2_relationships : String :=
  "From Theorem 7.5, we see that whenever the dominated convergence theorem " ++
  "can be applied, the sequence of random variables converges in the mean " ++
  "with $r=1$. Convergence in the mean and convergence almost surely do not " ++
  "have a direct relationship with each other. As the next two examples show," ++
  " convergence in the mean does not imply almost sure convergence and vice " ++
  "versa."
