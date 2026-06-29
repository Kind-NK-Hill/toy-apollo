import Mathlib
import ToyApollo.Output.thm_11_1
import ToyApollo.Output.thm_12_1

/-
TASK ID: thm_12_2
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter12-l2-norm-inner-product
TASK CONTENT:
\begin{thmbox}{12.2 (Minkowski Inequality)}
\end{thmbox}

For any two random variables X and Y in L 2(P) ,

X+ Y 2 \leq X2 + Y2.

\textit{Proof} We give a proof for complex-valued random variables. Using the Cauchy-

Schwarz inequality (Theorem 11.1),

X+ Y 2

2 \leqE [\vertX\vert2]+ 2R e(E[X*Y])+ E [\vertY\vert 2]

\leqE [\vertX\vert2]+ 2

\sqrt

E[\vertX\vert2]E[\vertY\vert 2]+ E[\vertY\vert 2]

=( X2 + Y2)2.

Taking the square roots of both sides yields the Minkowski inequality. \hfill $\square$

Similar to the case of L1 norm, a random vector with zero L2 norm is equivalent

to the zero function but need not be equal to the zero function. We continue with the

convention that two random variables that are equal almost everywhere are regarded

as the same random variable. With this caveat, we have shown that L2(P) is a

normed vector space.

Using the Minkowski inequality, we can see that the L2 norm defines a metric

on the space L2(P) , by regarding X - Y2 as the distance between two random

variables. Moreover, we can prove that the space of random variables in L2(P) is

complete with respect to the norm induced by inner product. It is a consequence of

the Riesz-Fischer theorem.
-/

-- WRITE FINAL LEAN CODE BELOW

open scoped InnerProductSpace

/-- The Cauchy-Schwarz bound used in the printed proof of Minkowski. -/
theorem thm_12_2_cauchy_schwarz_input {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (X Y : E) :
    ‖⟪X, Y⟫_𝕜‖ ≤ ‖X‖ * ‖Y‖ :=
  thm_11_1 X Y

/-- Zero norm is equality to zero in the normed-space quotient; for `L²`
objects this is exactly the textbook a.e.-equality convention. -/
theorem thm_12_2_zero_norm_eq_zero {E : Type*} [NormedAddCommGroup E] (X : E) :
    ‖X‖ = 0 ↔ X = 0 :=
  norm_eq_zero

/-- The squared estimate in the printed proof of Minkowski: expand
`‖X + Y‖²` by the inner product, control the cross term by Cauchy-Schwarz,
and collect the square `(‖X‖ + ‖Y‖)²`. -/
theorem thm_12_2_squared_estimate {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (X Y : E) :
    ‖X + Y‖ ^ 2 ≤ (‖X‖ + ‖Y‖) ^ 2 := by
  have hcs : ‖⟪X, Y⟫_𝕜‖ ≤ ‖X‖ * ‖Y‖ :=
    thm_12_2_cauchy_schwarz_input X Y
  have hre : RCLike.re ⟪X, Y⟫_𝕜 ≤ ‖X‖ * ‖Y‖ :=
    (RCLike.re_le_norm _).trans hcs
  have hsym : RCLike.re ⟪Y, X⟫_𝕜 = RCLike.re ⟪X, Y⟫_𝕜 := by
    have h :=
      congrArg (fun z : 𝕜 => RCLike.re z) (inner_conj_symm X Y)
    change RCLike.re ((starRingEnd 𝕜) ⟪Y, X⟫_𝕜) =
      RCLike.re ⟪X, Y⟫_𝕜 at h
    rw [RCLike.conj_re] at h
    exact h
  calc
    ‖X + Y‖ ^ 2 = RCLike.re ⟪X + Y, X + Y⟫_𝕜 := by
      exact InnerProductSpace.norm_sq_eq_re_inner (𝕜 := 𝕜) (X + Y)
    _ =
        RCLike.re
          (⟪X, X⟫_𝕜 + ⟪X, Y⟫_𝕜 + ⟪Y, X⟫_𝕜 + ⟪Y, Y⟫_𝕜) := by
      rw [inner_add_add_self]
    _ =
        ‖X‖ ^ 2 + RCLike.re ⟪X, Y⟫_𝕜 +
          RCLike.re ⟪Y, X⟫_𝕜 + ‖Y‖ ^ 2 := by
      simp
    _ = ‖X‖ ^ 2 + 2 * RCLike.re ⟪X, Y⟫_𝕜 + ‖Y‖ ^ 2 := by
      rw [hsym]
      ring
    _ ≤ ‖X‖ ^ 2 + 2 * (‖X‖ * ‖Y‖) + ‖Y‖ ^ 2 := by
      nlinarith [hre]
    _ = (‖X‖ + ‖Y‖) ^ 2 := by
      ring

/-- Theorem 12.2, Minkowski inequality: the triangle inequality for the `L²`
norm. -/
theorem thm_12_2 {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (X Y : E) :
    ‖X + Y‖ ≤ ‖X‖ + ‖Y‖ :=
  (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).1
    (thm_12_2_squared_estimate (𝕜 := 𝕜) X Y)
