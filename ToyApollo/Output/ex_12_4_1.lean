import Mathlib
import ToyApollo.Output.thm_12_5
import ToyApollo.Output.ex_12_2_3

/-
TASK ID: ex_12_4_1
TYPE: Example_Proof
SOURCE PLAN: chapter12-mmse-estimation
TASK CONTENT:
\textbf{Example 12.4.1 (Linear MMSE Estimator with Two Input Random Variables)} \\

When n= 2 , the problem is to find a1 and a2 that minimize Y- a 1X1 -a 2X22. The optimal

solution is given by the following system of linear equations:

[

E[X2

1]E [X1X2]

E[X1X2]E [X2

2]

][

a1

a2

]

=

[

E[X1Y]

E[X2Y]

]

The matrix on the left is positive semi-definite by the Cauchy-Schwarz inequality. The determinant

is positive if and only if X1 and. X2 are linearly independent.

We can use this system of linear equations to solve the linear regression problem in Example12.2.3,

by substituting the expectation E[X2

1] by . 1

n

\sumn

i=1 x2

i , the inner product E[X1X2] by . 1

n

\sumn

i=1 xi ,

etc. By solving

[ 1

n

\sumn

i=1 x2

i

n

\sumn

i=1 xi

n

\sumn

i=1 xi 1

][

a

b

]

=

[ 1

n

\sumn

i=1 xiyi

n

\sumn

i=1 yi

]

,

we recover the answer to the least square problem:

a= n \sum

i xiyi - \sum

i xi

\sum

i yi

n \sum

i x2 -( \sum

i xi)2 ,

b=

\sum

i yi -a \sum

i xi

n .
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

open scoped InnerProductSpace BigOperators

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- The two-input linear MMSE candidate `a₁X₁ + a₂X₂`. -/
def ex_12_4_1_estimate (X1 X2 : Ω →₂[P] ℝ) (a1 a2 : ℝ) : Ω →₂[P] ℝ :=
  a1 • X1 + a2 • X2

/-- The textbook normal-equation condition: the residual is orthogonal to both
regressors. -/
def ex_12_4_1_normalEquations (Y X1 X2 : Ω →₂[P] ℝ) (a1 a2 : ℝ) : Prop :=
  ⟪Y - ex_12_4_1_estimate (P := P) X1 X2 a1 a2, X1⟫_ℝ = 0 ∧
    ⟪Y - ex_12_4_1_estimate (P := P) X1 X2 a1 a2, X2⟫_ℝ = 0

/-- The displayed two-by-two linear system for the coefficients. -/
def ex_12_4_1_linearSystem (Y X1 X2 : Ω →₂[P] ℝ) (a1 a2 : ℝ) : Prop :=
  ⟪X1, X1⟫_ℝ * a1 + ⟪X1, X2⟫_ℝ * a2 = ⟪X1, Y⟫_ℝ ∧
    ⟪X1, X2⟫_ℝ * a1 + ⟪X2, X2⟫_ℝ * a2 = ⟪X2, Y⟫_ℝ

/-- The determinant of the two-by-two Gram matrix in Example 12.4.1. -/
def ex_12_4_1_gramDet (X1 X2 : Ω →₂[P] ℝ) : ℝ :=
  ⟪X1, X1⟫_ℝ * ⟪X2, X2⟫_ℝ - ⟪X1, X2⟫_ℝ ^ 2

/-- The pair of regressors as a `Fin 2` family. -/
def ex_12_4_1_pair (X1 X2 : Ω →₂[P] ℝ) : Fin 2 → Ω →₂[P] ℝ :=
  ![X1, X2]

/-- Linear independence of the two regressors in `L²(P)`. -/
def ex_12_4_1_linearIndependent (X1 X2 : Ω →₂[P] ℝ) : Prop :=
  LinearIndependent ℝ (ex_12_4_1_pair (P := P) X1 X2)

/-- The finite-sample sum `∑ᵢ xᵢ` used in the regression substitution. -/
def ex_12_4_1_sampleSumX {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i

/-- The finite-sample sum `∑ᵢ yᵢ` used in the regression substitution. -/
def ex_12_4_1_sampleSumY {n : ℕ} (y : Fin n → ℝ) : ℝ :=
  ∑ i, y i

/-- The finite-sample sum `∑ᵢ xᵢ²` used in the regression substitution. -/
def ex_12_4_1_sampleSumXX {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i ^ 2

/-- The finite-sample sum `∑ᵢ xᵢyᵢ` used in the regression substitution. -/
def ex_12_4_1_sampleSumXY {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  ∑ i, x i * y i

/-- The nonzero denominator in the closed-form least-squares slope. -/
def ex_12_4_1_sampleDenom {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ex_12_4_1_sampleSumXX x * (n : ℝ) - ex_12_4_1_sampleSumX x ^ 2

/-- The closed-form least-squares slope recovered from the empirical system. -/
def ex_12_4_1_sampleSlope {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  (ex_12_4_1_sampleSumXY x y * (n : ℝ) -
      ex_12_4_1_sampleSumX x * ex_12_4_1_sampleSumY y) /
    ex_12_4_1_sampleDenom x

/-- The closed-form least-squares intercept recovered from the empirical
system. -/
def ex_12_4_1_sampleIntercept {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  (ex_12_4_1_sampleSumY y -
      ex_12_4_1_sampleSlope x y * ex_12_4_1_sampleSumX x) / (n : ℝ)

/-- The two-by-two normal system after substituting empirical expectations
from Example 12.2.3. -/
def ex_12_4_1_empiricalNormalSystem {n : ℕ}
    (x y : Fin n → ℝ) (a b : ℝ) : Prop :=
  (ex_12_4_1_sampleSumXX x / (n : ℝ)) * a +
      (ex_12_4_1_sampleSumX x / (n : ℝ)) * b =
    ex_12_4_1_sampleSumXY x y / (n : ℝ) ∧
  (ex_12_4_1_sampleSumX x / (n : ℝ)) * a + b =
    ex_12_4_1_sampleSumY y / (n : ℝ)

theorem ex_12_4_1_X1_mem (X1 X2 : Ω →₂[P] ℝ) :
    X1 ∈ ex_12_2_3_W (P := P) X1 X2 := by
  unfold ex_12_2_3_W
  exact Submodule.subset_span (by simp)

theorem ex_12_4_1_X2_mem (X1 X2 : Ω →₂[P] ℝ) :
    X2 ∈ ex_12_2_3_W (P := P) X1 X2 := by
  unfold ex_12_2_3_W
  exact Submodule.subset_span (by simp)

/-- Orthogonality to the regression subspace, supplied by Theorem 12.5 for a
projection, gives the two normal equations. -/
theorem ex_12_4_1_normalEquations_of_orthogonal
    (Y X1 X2 : Ω →₂[P] ℝ) (a1 a2 : ℝ)
    (horth :
      ∀ Z : ex_12_2_3_closedW (P := P) X1 X2,
        ⟪Y - ((⟨ex_12_4_1_estimate (P := P) X1 X2 a1 a2,
              ex_12_2_3_fit_mem (P := P) X1 X2 a1 a2⟩ :
            ex_12_2_3_closedW (P := P) X1 X2) : Ω →₂[P] ℝ),
          (Z : Ω →₂[P] ℝ)⟫_ℝ = 0) :
    ex_12_4_1_normalEquations (P := P) Y X1 X2 a1 a2 := by
  constructor
  · simpa [ex_12_4_1_estimate, ex_12_2_3_fit] using
      horth ⟨X1, ex_12_4_1_X1_mem (P := P) X1 X2⟩
  · simpa [ex_12_4_1_estimate, ex_12_2_3_fit] using
      horth ⟨X2, ex_12_4_1_X2_mem (P := P) X1 X2⟩

/-- The normal equations expand to the displayed linear system. -/
theorem ex_12_4_1_system_of_normalEquations
    (Y X1 X2 : Ω →₂[P] ℝ) (a1 a2 : ℝ)
    (h : ex_12_4_1_normalEquations (P := P) Y X1 X2 a1 a2) :
    ex_12_4_1_linearSystem (P := P) Y X1 X2 a1 a2 := by
  rcases h with ⟨h1, h2⟩
  constructor
  · unfold ex_12_4_1_estimate at h1
    rw [inner_sub_left, inner_add_left, inner_smul_left, inner_smul_left] at h1
    simp only [starRingEnd_apply, star_trivial] at h1
    rw [real_inner_comm X2 X1, real_inner_comm Y X1]
    nlinarith
  · unfold ex_12_4_1_estimate at h2
    rw [inner_sub_left, inner_add_left, inner_smul_left, inner_smul_left] at h2
    simp only [starRingEnd_apply, star_trivial] at h2
    rw [real_inner_comm Y X2]
    nlinarith

/-- Substituting finite-sample empirical expectations into the displayed
normal equations gives the empirical regression system. -/
theorem ex_12_4_1_linearSystem_of_empirical_substitution
    (Y X I : Ω →₂[P] ℝ) {n : ℕ} (x y : Fin n → ℝ) (a b : ℝ)
    (hXX : ⟪X, X⟫_ℝ = ex_12_4_1_sampleSumXX x / (n : ℝ))
    (hXI : ⟪X, I⟫_ℝ = ex_12_4_1_sampleSumX x / (n : ℝ))
    (hII : ⟪I, I⟫_ℝ = 1)
    (hXY : ⟪X, Y⟫_ℝ = ex_12_4_1_sampleSumXY x y / (n : ℝ))
    (hIY : ⟪I, Y⟫_ℝ = ex_12_4_1_sampleSumY y / (n : ℝ))
    (hsys : ex_12_4_1_empiricalNormalSystem x y a b) :
    ex_12_4_1_linearSystem (P := P) Y X I a b := by
  rcases hsys with ⟨h1, h2⟩
  have hXXnorm : ‖X‖ ^ 2 = ex_12_4_1_sampleSumXX x / (n : ℝ) := by
    simpa [real_inner_self_eq_norm_sq] using hXX
  have hIInorm : ‖I‖ ^ 2 = (1 : ℝ) := by
    simpa [real_inner_self_eq_norm_sq] using hII
  unfold ex_12_4_1_linearSystem
  constructor
  · simpa [hXXnorm, hXI, hXY] using h1
  · simpa [hXI, hIInorm, hIY] using h2

/-- Solving the empirical two-by-two system recovers the textbook closed-form
least-squares slope and intercept. -/
theorem ex_12_4_1_empirical_closedForm_solves
    {n : ℕ} (x y : Fin n → ℝ)
    (hn : (n : ℝ) ≠ 0)
    (hden : ex_12_4_1_sampleDenom x ≠ 0) :
    ex_12_4_1_empiricalNormalSystem x y
      (ex_12_4_1_sampleSlope x y)
      (ex_12_4_1_sampleIntercept x y) := by
  unfold ex_12_4_1_empiricalNormalSystem ex_12_4_1_sampleIntercept
  constructor
  · rw [ex_12_4_1_sampleSlope]
    field_simp [hn, hden]
    rw [ex_12_4_1_sampleDenom]
    ring
  · rw [ex_12_4_1_sampleSlope]
    field_simp [hn, hden]
    rw [ex_12_4_1_sampleDenom]
    ring

/-- The two-by-two Gram matrix is positive semidefinite at the determinant
level, by Cauchy-Schwarz. -/
theorem ex_12_4_1_gramDet_nonneg (X1 X2 : Ω →₂[P] ℝ) :
    0 ≤ ex_12_4_1_gramDet (P := P) X1 X2 := by
  unfold ex_12_4_1_gramDet
  have hcs := real_inner_mul_inner_self_le X1 X2
  nlinarith [hcs, sq_nonneg (⟪X1, X2⟫_ℝ)]

/-- The determinant notation agrees with the determinant of the actual `Fin 2`
Gram matrix. -/
theorem ex_12_4_1_gramDet_eq_matrix_det (X1 X2 : Ω →₂[P] ℝ) :
    ex_12_4_1_gramDet (P := P) X1 X2 =
      (Matrix.gram ℝ (ex_12_4_1_pair (P := P) X1 X2)).det := by
  rw [Matrix.det_fin_two]
  simp [ex_12_4_1_gramDet, ex_12_4_1_pair, pow_two, real_inner_comm X2 X1]

/-- If the two regressors are linearly independent, the Gram determinant is
strictly positive. -/
theorem ex_12_4_1_gramDet_pos_of_linearIndependent
    (X1 X2 : Ω →₂[P] ℝ)
    (hli : ex_12_4_1_linearIndependent (P := P) X1 X2) :
    0 < ex_12_4_1_gramDet (P := P) X1 X2 := by
  have hpos : (Matrix.gram ℝ (ex_12_4_1_pair (P := P) X1 X2)).PosDef :=
    Matrix.posDef_gram_of_linearIndependent hli
  have hunit : IsUnit (Matrix.gram ℝ (ex_12_4_1_pair (P := P) X1 X2)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hpos.isUnit
  have hneMatrix : (Matrix.gram ℝ (ex_12_4_1_pair (P := P) X1 X2)).det ≠ 0 :=
    hunit.ne_zero
  have hne : ex_12_4_1_gramDet (P := P) X1 X2 ≠ 0 := by
    rw [ex_12_4_1_gramDet_eq_matrix_det (P := P) X1 X2]
    exact hneMatrix
  exact lt_of_le_of_ne (ex_12_4_1_gramDet_nonneg (P := P) X1 X2) (Ne.symm hne)

/-- Conversely, a strictly positive Gram determinant forces the two regressors
to be linearly independent. -/
theorem ex_12_4_1_linearIndependent_of_gramDet_pos
    (X1 X2 : Ω →₂[P] ℝ)
    (hdet : 0 < ex_12_4_1_gramDet (P := P) X1 X2) :
    ex_12_4_1_linearIndependent (P := P) X1 X2 := by
  let v := ex_12_4_1_pair (P := P) X1 X2
  let M := Matrix.gram ℝ v
  have hdetM : M.det ≠ 0 := by
    have hEq : ex_12_4_1_gramDet (P := P) X1 X2 = M.det := by
      simpa [M, v] using ex_12_4_1_gramDet_eq_matrix_det (P := P) X1 X2
    rw [← hEq]
    exact ne_of_gt hdet
  have hunitM : IsUnit M :=
    (Matrix.isUnit_iff_isUnit_det M).mpr ((isUnit_iff_ne_zero).mpr hdetM)
  have hinj : Function.Injective M.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 hunitM
  rw [ex_12_4_1_linearIndependent, Fintype.linearIndependent_iff]
  intro c hc i
  have hMc : M.mulVec c = 0 := by
    ext j
    have hinner : ⟪v j, ∑ i, c i • v i⟫_ℝ = 0 := by
      rw [hc, inner_zero_right]
    simpa [M, Matrix.gram, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      inner_add_right, inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using hinner
  have hc0 : c = 0 := hinj (by simpa using hMc)
  exact congr_fun hc0 i

/-- The determinant is positive exactly when the two regressors are linearly
independent. -/
theorem ex_12_4_1_gramDet_pos_iff_linearIndependent (X1 X2 : Ω →₂[P] ℝ) :
    0 < ex_12_4_1_gramDet (P := P) X1 X2 ↔
      ex_12_4_1_linearIndependent (P := P) X1 X2 := by
  exact
    ⟨ex_12_4_1_linearIndependent_of_gramDet_pos (P := P) X1 X2,
      ex_12_4_1_gramDet_pos_of_linearIndependent (P := P) X1 X2⟩

/-- The projection onto the span of two regressors has two scalar coordinates. -/
theorem ex_12_4_1_projection_has_coefficients (Y X1 X2 : Ω →₂[P] ℝ) :
    ∃ a1 a2 : ℝ,
      ex_12_4_1_estimate (P := P) X1 X2 a1 a2 =
        (def_12_5 P (ex_12_2_3_closedW (P := P) X1 X2) Y : Ω →₂[P] ℝ) := by
  have hmem :
      (def_12_5 P (ex_12_2_3_closedW (P := P) X1 X2) Y : Ω →₂[P] ℝ) ∈
        ex_12_2_3_W (P := P) X1 X2 := by
    exact (def_12_5 P (ex_12_2_3_closedW (P := P) X1 X2) Y).2
  unfold ex_12_2_3_W at hmem
  rcases Submodule.mem_span_pair.mp hmem with ⟨a1, a2, hcoeff⟩
  exact ⟨a1, a2, by simpa [ex_12_4_1_estimate] using hcoeff⟩

/-- Example 12.4.1: the projection onto the span of the two inputs has
coefficients satisfying the displayed normal equations, and the Gram determinant
is nonnegative. -/
theorem ex_12_4_1 (Y X1 X2 : Ω →₂[P] ℝ) :
    (∃ a1 a2 : ℝ, ex_12_4_1_linearSystem (P := P) Y X1 X2 a1 a2) ∧
      0 ≤ ex_12_4_1_gramDet (P := P) X1 X2 ∧
        (0 < ex_12_4_1_gramDet (P := P) X1 X2 ↔
          ex_12_4_1_linearIndependent (P := P) X1 X2) ∧
          (∀ (n : ℕ) (x y : Fin n → ℝ),
            (n : ℝ) ≠ 0 →
              ex_12_4_1_sampleDenom x ≠ 0 →
                ex_12_4_1_empiricalNormalSystem x y
                  (ex_12_4_1_sampleSlope x y)
                  (ex_12_4_1_sampleIntercept x y)) := by
  rcases ex_12_4_1_projection_has_coefficients (P := P) Y X1 X2 with ⟨a1, a2, hcoeff⟩
  have horthProjection :
      ∀ Z : ex_12_2_3_closedW (P := P) X1 X2,
        ⟪Y - (def_12_5 P (ex_12_2_3_closedW (P := P) X1 X2) Y : Ω →₂[P] ℝ),
          (Z : Ω →₂[P] ℝ)⟫_ℝ = 0 :=
    thm_12_5_projection_orthogonal P (ex_12_2_3_closedW (P := P) X1 X2) Y
  have horth :
      ∀ Z : ex_12_2_3_closedW (P := P) X1 X2,
        ⟪Y - ((⟨ex_12_4_1_estimate (P := P) X1 X2 a1 a2,
              ex_12_2_3_fit_mem (P := P) X1 X2 a1 a2⟩ :
            ex_12_2_3_closedW (P := P) X1 X2) : Ω →₂[P] ℝ),
          (Z : Ω →₂[P] ℝ)⟫_ℝ = 0 := by
    intro Z
    simpa [hcoeff] using horthProjection Z
  exact
    ⟨⟨a1, a2,
        ex_12_4_1_system_of_normalEquations (P := P) Y X1 X2 a1 a2
          (ex_12_4_1_normalEquations_of_orthogonal (P := P) Y X1 X2 a1 a2 horth)⟩,
      ex_12_4_1_gramDet_nonneg (P := P) X1 X2,
      ex_12_4_1_gramDet_pos_iff_linearIndependent (P := P) X1 X2,
      fun n x y hn hden =>
        ex_12_4_1_empirical_closedForm_solves x y hn hden⟩
