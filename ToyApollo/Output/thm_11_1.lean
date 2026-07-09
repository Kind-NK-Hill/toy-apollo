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

open MeasureTheory
open scoped InnerProductSpace

/--
Theorem 11.1, Cauchy-Schwarz (abstract inner-product form).  The inner product of
two vectors in a real or complex inner product space is bounded by the product of
their norms.  This is the reusable Hilbert-space interface consumed downstream by
`def_12_1` and `thm_12_2`.  The source Theorem 11.1 is specifically about the
`L²`/expectation object `E[X*Y]`; that textbook statement, with its
integrability/well-definedness step and completing-the-square proof, is landed in
the `thm_11_1_expectation` section below rather than being black-boxed here.
-/
theorem thm_11_1 {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (X Y : E) :
    ‖⟪X, Y⟫_𝕜‖ ≤ ‖X‖ * ‖Y‖ := by
  exact norm_inner_le_norm X Y

/-- Equality in Theorem 11.1, nonzero case: `‖⟪X, Y⟫‖ = ‖X‖ ‖Y‖` iff `Y` is a
nonzero scalar multiple of `X`.  The source's degenerate case (`X = 0` or
`Y = 0`, where both sides of (11.1) vanish) is recorded separately in
`thm_11_1_equality_zero`. -/
theorem thm_11_1_equality_iff {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {X Y : E} (hX : X ≠ 0) (hY : Y ≠ 0) :
    ‖⟪X, Y⟫_𝕜‖ = ‖X‖ * ‖Y‖ ↔ ∃ c : 𝕜, c ≠ 0 ∧ Y = c • X := by
  exact norm_inner_eq_norm_iff hX hY

/-- The source's degenerate equality case: when either variable is `0`, both sides
of the Cauchy-Schwarz identity are `0`, so equality holds. -/
theorem thm_11_1_equality_zero {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (Y : E) :
    ‖⟪(0 : E), Y⟫_𝕜‖ = ‖(0 : E)‖ * ‖Y‖ := by
  simp

/-- The real-valued specialization where the inner product has no conjugation. -/
theorem thm_11_1_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X Y : E) : |⟪X, Y⟫_ℝ| ≤ ‖X‖ * ‖Y‖ := by
  exact abs_real_inner_le_norm X Y

/-! ### Source-faithful `L²`/expectation landing (real specialization)

The declarations above give the abstract Hilbert-space statement, which suffices
for the downstream Hilbert-space consumers.  The source Theorem 11.1 is, however,
specifically a statement about square-integrable random variables: `E[X*Y]` is
well-defined and `|E[X*Y]| ≤ sqrt(E[X²] E[Y²])`.  The declarations below land that
textbook object directly on the expectation `∫ X Y ∂μ`, and prove the bound by the
source's own argument — nonnegativity of the quadratic `E[(t·X + Y)²]` and
completing the square (`thm_11_1_quadratic_nonneg`) — rather than by restating a
Mathlib inner-product lemma. -/

/-- Source step 1 ("we first show that `|X*Y|` is integrable"): for
square-integrable real `X`, `Y` the product `X·Y` is integrable, so `E[X Y]` is
well-defined. -/
theorem thm_11_1_integrable_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Integrable (fun ω => X ω * Y ω) μ :=
  hX.integrable_mul hY

/-- Source completing-the-square building block: the quadratic `E[(t·X + Y)²]` is
nonnegative for every real `t`, and expands to the nonnegative quadratic
`(E[X²])·t² + 2(E[X Y])·t + E[Y²]`. -/
theorem thm_11_1_quadratic_nonneg {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (t : ℝ) :
    0 ≤ (∫ ω, X ω ^ 2 ∂μ) * (t * t)
        + (2 * ∫ ω, X ω * Y ω ∂μ) * t + (∫ ω, Y ω ^ 2 ∂μ) := by
  have hX2 : Integrable (fun ω => X ω ^ 2) μ :=
    (hX.integrable_mul hX).congr (by filter_upwards with ω; simp [Pi.mul_apply, pow_two])
  have hY2 : Integrable (fun ω => Y ω ^ 2) μ :=
    (hY.integrable_mul hY).congr (by filter_upwards with ω; simp [Pi.mul_apply, pow_two])
  have hXY : Integrable (fun ω => X ω * Y ω) μ := hX.integrable_mul hY
  have hnn : 0 ≤ ∫ ω, (t * X ω + Y ω) ^ 2 ∂μ :=
    integral_nonneg (fun ω => sq_nonneg _)
  have hexp : (∫ ω, (t * X ω + Y ω) ^ 2 ∂μ)
      = (∫ ω, X ω ^ 2 ∂μ) * (t * t)
        + (2 * ∫ ω, X ω * Y ω ∂μ) * t + (∫ ω, Y ω ^ 2 ∂μ) := by
    have hpt : (fun ω => (t * X ω + Y ω) ^ 2)
        = (fun ω => (t * t) * X ω ^ 2 + (2 * t) * (X ω * Y ω) + Y ω ^ 2) := by
      funext ω; ring
    have e1 : Integrable (fun ω => (t * t) * X ω ^ 2) μ := hX2.const_mul _
    have e2 : Integrable (fun ω => (2 * t) * (X ω * Y ω)) μ := hXY.const_mul _
    have e12 : Integrable
        (fun ω => (t * t) * X ω ^ 2 + (2 * t) * (X ω * Y ω)) μ := e1.add e2
    rw [hpt, integral_add e12 hY2, integral_add e1 e2,
      integral_const_mul, integral_const_mul]
    ring
  rw [hexp] at hnn
  exact hnn

/-- **Theorem 11.1 (real case, source form).**  For square-integrable real random
variables the expectation `E[X Y]` satisfies the Cauchy-Schwarz bound
`|E[X Y]| ≤ sqrt(E[X²]) · sqrt(E[Y²])`.  Proof by the source's nonnegative-quadratic
/ completing-the-square argument (`thm_11_1_quadratic_nonneg`), not by restating a
Mathlib lemma. -/
theorem thm_11_1_expectation {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    |∫ ω, X ω * Y ω ∂μ|
      ≤ Real.sqrt (∫ ω, X ω ^ 2 ∂μ) * Real.sqrt (∫ ω, Y ω ^ 2 ∂μ) := by
  have ha : 0 ≤ ∫ ω, X ω ^ 2 ∂μ := integral_nonneg (fun ω => sq_nonneg _)
  have hd : discrim (∫ ω, X ω ^ 2 ∂μ) (2 * ∫ ω, X ω * Y ω ∂μ) (∫ ω, Y ω ^ 2 ∂μ) ≤ 0 :=
    discrim_le_zero (thm_11_1_quadratic_nonneg hX hY)
  have hsq : (∫ ω, X ω * Y ω ∂μ) ^ 2
      ≤ (∫ ω, X ω ^ 2 ∂μ) * (∫ ω, Y ω ^ 2 ∂μ) := by
    have hdd : (2 * ∫ ω, X ω * Y ω ∂μ) ^ 2
        - 4 * (∫ ω, X ω ^ 2 ∂μ) * (∫ ω, Y ω ^ 2 ∂μ) ≤ 0 := by
      simpa [discrim] using hd
    nlinarith [hdd]
  rw [← Real.sqrt_mul ha, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hsq
