import Mathlib
import ToyApollo.Output.def_12_2

/-
TASK ID: thm_12_1
TYPE: Theorem_Statement
SOURCE PLAN: chapter12-l2-norm-inner-product
TASK CONTENT:
\begin{thmbox}{12.1}
\end{thmbox}

Let\langle\cdot,\cdot\ranglebe an inner product over a field K , where K is either R or C :

Fo r X, Y1,Y 2 \in L2(P) and \alpha, \beta \in K,

\langleX, \alphaY1 +\betaY 2\rangle= \alpha\langleX, Y1\rangle+\beta\langleX, Y2\rangle.

For real inner product, we have\langleX, Y\rangle=\langle Y, X\ranglefor X, Y \inL 2(P) .

For complex inner product, we have\langleX, Y\rangle=\langle Y, X\rangle* for X, Y \in L2(P) .

Fo r X \in L2(P) and \alpha \inK ,\alphaX2 =\vert \alpha\vert\cdot X2.

The triangle inequality for L 2 norm is called the Minkowski inequality.
-/

-- WRITE FINAL LEAN CODE BELOW

open scoped InnerProductSpace

/-- Linearity of the textbook inner product in the second argument. -/
theorem thm_12_1_inner_add_smul {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (X Y1 Y2 : E) (α β : 𝕜) :
    ⟪X, α • Y1 + β • Y2⟫_𝕜 =
      α * ⟪X, Y1⟫_𝕜 + β * ⟪X, Y2⟫_𝕜 := by
  calc
    ⟪X, α • Y1 + β • Y2⟫_𝕜 =
        ⟪X, α • Y1⟫_𝕜 + ⟪X, β • Y2⟫_𝕜 := by
      rw [inner_add_right]
    _ = α * ⟪X, Y1⟫_𝕜 + β * ⟪X, Y2⟫_𝕜 := by
      rw [inner_smul_right, inner_smul_right]

/-- Real inner products are symmetric. -/
theorem thm_12_1_real_symm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X Y : E) :
    ⟪X, Y⟫_ℝ = ⟪Y, X⟫_ℝ := by
  exact (real_inner_comm X Y).symm

/-- Complex and real `RCLike` inner products are conjugate symmetric. -/
theorem thm_12_1_conj_symm {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (X Y : E) :
    ⟪X, Y⟫_𝕜 = star ⟪Y, X⟫_𝕜 := by
  exact (inner_conj_symm X Y).symm

/-- Scaling the `L²` norm by a scalar scales it by the scalar norm. -/
theorem thm_12_1_norm_smul {𝕜 E : Type*} [Norm 𝕜]
    [NormedAddCommGroup E] [SMul 𝕜 E] [NormSMulClass 𝕜 E]
    (α : 𝕜) (X : E) :
    ‖α • X‖ = ‖α‖ * ‖X‖ := by
  exact norm_smul α X

/-- The triangle inequality for the norm induced by the inner product. -/
theorem thm_12_1_triangle {E : Type*} [NormedAddCommGroup E] (X Y : E) :
    ‖X + Y‖ ≤ ‖X‖ + ‖Y‖ := by
  exact norm_add_le X Y

/-- Theorem 12.1: the basic algebraic properties of an inner product and its
induced norm.  The preceding Definition 12.2 instantiates these facts for the
textbook `L²(P)` inner product. -/
theorem thm_12_1 {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (X Y Y1 Y2 : E) (α β : 𝕜) :
    ⟪X, α • Y1 + β • Y2⟫_𝕜 =
        α * ⟪X, Y1⟫_𝕜 + β * ⟪X, Y2⟫_𝕜 ∧
      ⟪X, Y⟫_𝕜 = star ⟪Y, X⟫_𝕜 ∧
      ‖α • X‖ = ‖α‖ * ‖X‖ ∧
      ‖X + Y‖ ≤ ‖X‖ + ‖Y‖ := by
  exact ⟨thm_12_1_inner_add_smul X Y1 Y2 α β,
    thm_12_1_conj_symm X Y, thm_12_1_norm_smul α X,
    thm_12_1_triangle X Y⟩
