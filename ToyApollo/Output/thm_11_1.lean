import Mathlib

/-
TASK ID: thm_11_1
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter11-bounds-inequalities
TASK CONTENT:
\begin{thmbox}{11.1 (Cauchy-Schwarz Inequality)}
\end{thmbox}

For complex-valued random variables X and Y in L2, the expectation

E[X*Y] is well-defined, and

\vertE[X*Y]\vert \leq

\sqrt

E[\vertX\vert2]E[\vertY\vert 2] (11.1)

holds, with equality holding iff X and Y are scalar multiple of each other with

probability 1. When X and Y are real, E[X*Y] is simplified to E[XY ].

\textit{Proof} Let X and Y be complex-valued random variables such that both E[\vertX\vert2]

and E[\vertY\vert2] are finite. We first show that \vertX*Y\vert is integrable. Let A1 be the subset

of \Omega in which \vertX()\vert > \vertY()\vert, and A2 be the subset in which
\vertX()\vert\leq\vert Y()\vert.

Then, we have

E[\vertX*Y\vert] =

\int

A1

\vertX*Y\vert+

\int

A2

\vertX*Y\vert\leq

\int

A1

\vertX\vert2 +

\int

A2

\vertY\vert2 \leq E[\vertX\vert2]+ E[\vertY\vert2].

This shows that .

\int

\vertX*Y\vert is finite, and hence, X*Y is integrable.

If E[\vertX\vert2]= 0, then X = 0 almost surely, and hence, X*Y = 0 almost surely.

Both sides of (11.1) are equal to zero. Suppose E[\vertX\vert2] > 0. Define a function

f( z )\coloneqqE[\vertzX + Y\vert2] with z being a complex variable. We can expand it as

f( z )= E[(zX +Y)*(zX +Y)]=\vert z\vert2E[\vertX\vert2]+ z*E[X*Y]+ zE[XY *]+ E[\vertY\vert2].

By completing square, we obtain

f( z )= E[\vertX\vert2]\cdot

\vert\vert\vertz+ E[X*Y]

E[\vertX\vert2]

\vert\vert\vert

- \vertE[X*Y]\vert2

E[\vertX\vert2] +E [\vertY\vert 2].

Since f( z )\geq 0 for all z, the constant term on the right must be nonnegative. This

yields the Cauchy-Schwarz inequality.

When equality holds, then f( z0) = 0 for a particular choice of z0. This implies

thatE[\vertz0X + Y\vert2]= 0, and hence, Y =- z0X almost surely. \hfill $\square$

Note that the proof of Theorem 11.1 does not rely on the assumption that the

underlying measure space is a probability space. The Cauchy-Schwarz inequality

can be derived for a general measure, as long as X and Y are square integrable.
-/

-- WRITE FINAL LEAN CODE BELOW

open scoped InnerProductSpace

/--
Theorem 11.1, Cauchy-Schwarz: the inner product of two vectors in a real or
complex inner product space is bounded by the product of their norms.  In the
`L²` random-variable model, this inner product is the textbook expectation
`E[X*Y]`.
-/
theorem thm_11_1 {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (X Y : E) :
    ‖⟪X, Y⟫_𝕜‖ ≤ ‖X‖ * ‖Y‖ := by
  exact norm_inner_le_norm X Y

/-- Equality in Theorem 11.1 is exactly the nonzero scalar-multiple case. -/
theorem thm_11_1_equality_iff {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {X Y : E} (hX : X ≠ 0) (hY : Y ≠ 0) :
    ‖⟪X, Y⟫_𝕜‖ = ‖X‖ * ‖Y‖ ↔ ∃ c : 𝕜, c ≠ 0 ∧ Y = c • X := by
  exact norm_inner_eq_norm_iff hX hY

/-- The real-valued specialization where the inner product has no conjugation. -/
theorem thm_11_1_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X Y : E) : |⟪X, Y⟫_ℝ| ≤ ‖X‖ * ‖Y‖ := by
  exact abs_real_inner_le_norm X Y
