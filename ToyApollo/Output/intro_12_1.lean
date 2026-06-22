/-
TASK ID: intro_12_1
TYPE: Remark
SOURCE PLAN: chapter12-l2-norm-inner-product

This parent-facing file is a non-proof textual carrier for source narrative.
It preserves the remark text for Phase 2 status accounting and exports no
mathematical dependency.
-/

/-- Textual carrier for `L2-Norm and Inner Product Space`. -/
def intro_12_1 : String :=
  "\\subsection*{12.1 L2-Norm and Inner Product Space}\n\nThis chapter presents " ++
  "a geometric perspective on random variables by viewing them\n\nas vectors in" ++
  " a vector space. Although this vector space has infinite dimension\n\nin " ++
  "general, this viewpoint offers insights into the behavior of random " ++
  "variables.\n\nAssuming that all random variables in the vector space have " ++
  "finite second moments,\n\nwe can define an inner product that resembles the " ++
  "dot product in a finite-dimensional\n\nEuclidean space. This inner product " ++
  "allows us to define notions such as orthogonal-\n\nity and the analog of the" ++
  " triangle inequality in this infinite-dimensional vector space.\n\nTo study " ++
  "random variables form this geometric perspective, we borrow tech-\n\nniques " ++
  "from Hilbert space theory. We can define the projection operator, which\n\n" ++
  "maps a random variable to a subspace, and prove the Orthogonality " ++
  "Principle in\n\nthe context of probability theory. These tools are then " ++
  "applied to the derivation of\n\nstatistical estimators that minimize " ++
  "mean-squared error."
