/-
TASK ID: intro_12_3
TYPE: Remark
SOURCE PLAN: chapter12-orthogonality-principle

This parent-facing file is a non-proof textual carrier for source narrative.
It preserves the remark text for Phase 2 status accounting and exports no
mathematical dependency.
-/

/-- Textual carrier for `Orthogonality Principle`. -/
def intro_12_3 : String :=
  "\\subsection*{12.3 Orthogonality Principle}\n\nWhen W has infinite dimension," ++
  " computing the projection of a random variable\n\nY onto a closed space W " ++
  "using the definition may be difficult. The next theorem\n\nprovides a useful" ++
  " characterization of the projection function in terms of perpen-\n\ndicular " ++
  "projection. Essentially, the theorem states that the optimal solution in W" ++
  "\n\nthat minimizes the distance to Y is achieved when and only when the " ++
  "error vector\n\nis perpendicular to W Note that we are not proving any " ++
  "existence result in the\n\ntheorem below, as the well-definedness of the " ++
  "projection function has already been\n\nestablished in Theorem 12.4. The " ++
  "objective of the theorem below is to give an\n\nalternate way to compute the" ++
  " projection of a random variable."
