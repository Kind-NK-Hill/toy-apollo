/-
TASK ID: rem_10_3_pdf_check_intro
TYPE: Remark
SOURCE PLAN: chapter10-distribution-total-variation

This parent-facing file is a non-proof textual carrier for source narrative.
It preserves the remark text for Phase 2 status accounting and exports no
mathematical dependency.
-/

/-- Textual carrier for `Pdf Convergence as a Practical Check`. -/
def rem_10_3_pdf_check_intro : String :=
  "The last example is an example of convergence in distribution but not " ++
  "convergence in total variation.\n\nThe cumulative distribution function is " ++
  "used in the definition of convergence in distribution. However, in " ++
  "practice, we can also check convergence in distribution using probability " ++
  "density function, as demonstrated in the following example."
