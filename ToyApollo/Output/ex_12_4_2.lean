import Mathlib
import ToyApollo.Output.def_12_2
import ToyApollo.Output.def_9_1
import ToyApollo.Output.thm_7_13

/-
TASK ID: ex_12_4_2
TYPE: Example_Proof
SOURCE PLAN: chapter12-mmse-estimation
TASK CONTENT:
\textbf{Example 12.4.2 (Scaling Factor for Linear MMSE Estimate)} \\

Suppose we want to estimate a random variable X , which is observed with some additive noise N .

The observed random variable is Y= cX + N ,w h e r e c is a nonzero constant. We suppose that X

has mean \mu and variance \sigma2

X , N has zero mean and variance \sigma2

N ,a n d X and N are independent.

We also suppose that the parameters c ,\mu,\sigma2

X ,a n d. \sigma2

N are known, andc/=0 .

An unbiased estimate of X is simplyX= Y/c , if we can measure the random variable Y H o w e v e r ,

if we want to minimize the mean-squared error, the optimal constant k that minimizes the mean-

squared errorkY- X 2 can be computed by differentiating

k2E[Y 2]- 2kE[XY]+ E[X2]

with respect to k The optimal value scaling coefficient is

k* = E[XY]

E[Y 2] = c\sigma2

X

c2\sigma2

X +\sigma 2

N

The linear MMSE estimate of X is then given by

XMMSE = c2\sigma2

X

c2\sigma2

X +\sigma 2

N

\cdot Y

c .

We multiply the unbiased estimateY/c by the scaling factor.

c2\sigma2

X

c2\sigma2

X+\sigma2

N

to obtain the MMSE estimate,

which is a linear function of the observed variable Y .

12.4.2 Nonlinear MMSE Estimation

In general, given Y , X1, X2,...,X n \inL 2(P) , the problem of nonlinear MMSE

estimation is to find a measurable function g(x1,x 2,...,x n) such that

Y- g(X 1,X 2,...,X n)2

is minimized. We formulate the problem in terms of \sigma-algebra.

Recall that \sigma(X1,X 2,...,X n) denotes the smallest \sigma-algebra of \mathcal{F} such that

X1,...,X n are measurable. A function g(x1,x 2,...,x n) mapping from. Rn to. R is

measurable with respect to \sigma(X1,X 2,...,X n) iff

g- 1(B)\in \sigma(X 1,X 2,...,X n)for all B \in \mathcal{B} (R).

The next theorem characterizes the random variables that can be written as a

measurable function of X1 to. Xn.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory

open scoped InnerProductSpace BigOperators

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

/-- The observed signal `Y = cX + N`, in the Chapter 12 L2 Hilbert space. -/
def ex_12_4_2_observed (c : ℝ) (X N : Ω →₂[P] ℝ) : Ω →₂[P] ℝ :=
  c • X + N

/-- Textbook mean, using the local Chapter 12 expectation notation. -/
def ex_12_4_2_mean (X : Ω → ℝ) : ℝ :=
  P[X]

/-- Textbook variance, reusing the local Definition 9.1 variance. -/
def ex_12_4_2_variance (X : Ω → ℝ) : ℝ :=
  _root_.variance P X

/-- Second moment written through the local Chapter 12 L2 inner product. -/
def ex_12_4_2_secondMoment (X : Ω → ℝ) (hX : L2Function P X) : ℝ :=
  l2Inner P X X hX hX

/-- The one-dimensional quadratic MSE expression
`k^2 E[Y^2] - 2k E[XY] + E[X^2]`. -/
def ex_12_4_2_quadraticMSE (EYY EXY EXX k : ℝ) : ℝ :=
  k ^ 2 * EYY - 2 * k * EXY + EXX

/-- The coefficient obtained by differentiating the quadratic MSE. -/
def ex_12_4_2_optimalK (EYY EXY : ℝ) : ℝ :=
  EXY / EYY

/-- The source's centered-noise scaling coefficient. -/
def ex_12_4_2_sourceK (c sigmaX2 sigmaN2 : ℝ) : ℝ :=
  c * sigmaX2 / (c ^ 2 * sigmaX2 + sigmaN2)

/-- The multiplicative shrinkage of the unbiased estimator `Y / c`. -/
def ex_12_4_2_shrinkage (c sigmaX2 sigmaN2 : ℝ) : ℝ :=
  c ^ 2 * sigmaX2 / (c ^ 2 * sigmaX2 + sigmaN2)

/-- The linear MMSE estimate in the source's centered form. -/
def ex_12_4_2_mmseEstimate (c sigmaX2 sigmaN2 : ℝ) (Y : Ω → ℝ) : Ω → ℝ :=
  fun ω => ex_12_4_2_sourceK c sigmaX2 sigmaN2 * Y ω

/-- The unbiased estimate `Y / c`. -/
def ex_12_4_2_unbiasedEstimate (c : ℝ) (Y : Ω → ℝ) : Ω → ℝ :=
  fun ω => Y ω / c

/-- Completing the square for the quadratic MSE shows that `E[XY] / E[Y^2]`
is the minimizer when `E[Y^2] > 0`. -/
theorem ex_12_4_2_quadraticMSE_sub_min
    (EYY EXY EXX k : ℝ) (hEYY : EYY ≠ 0) :
    ex_12_4_2_quadraticMSE EYY EXY EXX k -
        ex_12_4_2_quadraticMSE EYY EXY EXX (ex_12_4_2_optimalK EYY EXY) =
      EYY * (k - ex_12_4_2_optimalK EYY EXY) ^ 2 := by
  unfold ex_12_4_2_quadraticMSE ex_12_4_2_optimalK
  field_simp [hEYY]
  ring

theorem ex_12_4_2_quadraticMSE_minimal
    (EYY EXY EXX k : ℝ) (hEYY : 0 < EYY) :
    0 ≤
      ex_12_4_2_quadraticMSE EYY EXY EXX k -
        ex_12_4_2_quadraticMSE EYY EXY EXX (ex_12_4_2_optimalK EYY EXY) := by
  rw [ex_12_4_2_quadraticMSE_sub_min EYY EXY EXX k hEYY.ne']
  exact mul_nonneg hEYY.le (sq_nonneg _)

/-- Independence and zero mean of the noise remove the cross moment `E[XN]`. -/
theorem ex_12_4_2_independent_noise_orthogonal {X N : Ω → ℝ}
    (hXL2 : L2Function P X) (hNL2 : L2Function P N)
    (hXN : def_5_2 P X N) (hX_int : Integrable X P) (hN_int : Integrable N P)
    (hXN_int : Integrable (fun ω => X ω * N ω) P) (hN0 : ex_12_4_2_mean (P := P) N = 0) :
    l2Inner P X N hXL2 hNL2 = 0 := by
  unfold l2Inner ex_12_4_2_mean at *
  rw [thm_7_13 hXN hX_int hN_int hXN_int, hN0, mul_zero]

/-- The raw Chapter 12 inner product agrees with Mathlib's `L²` inner product
on the `toLp` representatives. -/
theorem ex_12_4_2_toLp_inner_eq_l2Inner {X N : Ω → ℝ}
    (hXL2 : L2Function P X) (hNL2 : L2Function P N) :
    ⟪L2Function.toLp hXL2, L2Function.toLp hNL2⟫_ℝ =
      l2Inner P X N hXL2 hNL2 := by
  rw [L2.inner_def]
  unfold l2Inner L2Function.toLp
  apply integral_congr_ae
  have hXae := MemLp.coeFn_toLp (show MemLp X (2 : ENNReal) P from hXL2)
  have hNae := MemLp.coeFn_toLp (show MemLp N (2 : ENNReal) P from hNL2)
  filter_upwards [hXae, hNae] with ω hXω hNω
  rw [hXω, hNω]
  rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply']
  simp

/-- For centered `X` and orthogonal noise, `E[X(cX+N)] = c σ_X²`. -/
theorem ex_12_4_2_crossMoment_observed
    (c sigmaX2 : ℝ) (X N : Ω →₂[P] ℝ)
    (hXN : ⟪X, N⟫_ℝ = 0) (hXX : ⟪X, X⟫_ℝ = sigmaX2) :
    ⟪X, ex_12_4_2_observed (P := P) c X N⟫_ℝ = c * sigmaX2 := by
  unfold ex_12_4_2_observed
  rw [inner_add_right, inner_smul_right, hXN, hXX]
  simp only [add_zero]

/-- For centered `X` and orthogonal noise,
`E[(cX+N)^2] = c^2 σ_X² + σ_N²`. -/
theorem ex_12_4_2_observed_secondMoment
    (c sigmaX2 sigmaN2 : ℝ) (X N : Ω →₂[P] ℝ)
    (hXN : ⟪X, N⟫_ℝ = 0) (hXX : ⟪X, X⟫_ℝ = sigmaX2)
    (hNN : ⟪N, N⟫_ℝ = sigmaN2) :
    ⟪ex_12_4_2_observed (P := P) c X N,
      ex_12_4_2_observed (P := P) c X N⟫_ℝ =
        c ^ 2 * sigmaX2 + sigmaN2 := by
  have hNX : ⟪N, X⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact hXN
  unfold ex_12_4_2_observed
  rw [inner_add_left, inner_add_right, inner_add_right, inner_smul_left, inner_smul_right,
    inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply, star_trivial]
  rw [hXN, hXX, hNN, hNX]
  ring

theorem ex_12_4_2_sourceK_eq_optimalK (c sigmaX2 sigmaN2 : ℝ) :
    ex_12_4_2_optimalK (c ^ 2 * sigmaX2 + sigmaN2) (c * sigmaX2) =
      ex_12_4_2_sourceK c sigmaX2 sigmaN2 := by
  rfl

/-- The source's estimate is the unbiased estimate `Y / c` multiplied by the
displayed shrinkage factor. -/
theorem ex_12_4_2_mmseEstimate_eq_shrinkage_unbiased
    (c sigmaX2 sigmaN2 : ℝ) (Y : Ω → ℝ) (hc : c ≠ 0) :
    ex_12_4_2_mmseEstimate c sigmaX2 sigmaN2 Y =
      fun ω =>
        ex_12_4_2_shrinkage c sigmaX2 sigmaN2 *
          ex_12_4_2_unbiasedEstimate c Y ω := by
  funext ω
  unfold ex_12_4_2_mmseEstimate ex_12_4_2_shrinkage ex_12_4_2_unbiasedEstimate
    ex_12_4_2_sourceK
  field_simp [hc]

/-- Example 12.4.2, in the centered second-moment form used by the displayed
coefficient.  The public theorem now assembles the source route from
`Y = cX + N`, independent zero-mean noise, and the observed moment identities. -/
theorem ex_12_4_2 (c sigmaX2 sigmaN2 EXX : ℝ) {X N : Ω → ℝ}
    (hXL2 : L2Function P X) (hNL2 : L2Function P N)
    (hXN : def_5_2 P X N) (hX_int : Integrable X P) (hN_int : Integrable N P)
    (hXN_int : Integrable (fun ω => X ω * N ω) P)
    (hN0 : ex_12_4_2_mean (P := P) N = 0)
    (hXX : ex_12_4_2_secondMoment (P := P) X hXL2 = sigmaX2)
    (hNN : ex_12_4_2_secondMoment (P := P) N hNL2 = sigmaN2)
    (hc : c ≠ 0) (hden : 0 < c ^ 2 * sigmaX2 + sigmaN2) :
    ⟪L2Function.toLp hXL2,
        ex_12_4_2_observed (P := P) c (L2Function.toLp hXL2) (L2Function.toLp hNL2)⟫_ℝ =
        c * sigmaX2 ∧
      ⟪ex_12_4_2_observed (P := P) c (L2Function.toLp hXL2) (L2Function.toLp hNL2),
        ex_12_4_2_observed (P := P) c (L2Function.toLp hXL2) (L2Function.toLp hNL2)⟫_ℝ =
        c ^ 2 * sigmaX2 + sigmaN2 ∧
      ex_12_4_2_optimalK
          ⟪ex_12_4_2_observed (P := P) c (L2Function.toLp hXL2) (L2Function.toLp hNL2),
            ex_12_4_2_observed (P := P) c (L2Function.toLp hXL2) (L2Function.toLp hNL2)⟫_ℝ
          ⟪L2Function.toLp hXL2,
            ex_12_4_2_observed (P := P) c (L2Function.toLp hXL2) (L2Function.toLp hNL2)⟫_ℝ =
        ex_12_4_2_sourceK c sigmaX2 sigmaN2 ∧
      (∀ k : ℝ,
        0 ≤
          ex_12_4_2_quadraticMSE
              ⟪ex_12_4_2_observed (P := P) c (L2Function.toLp hXL2) (L2Function.toLp hNL2),
                ex_12_4_2_observed (P := P) c (L2Function.toLp hXL2) (L2Function.toLp hNL2)⟫_ℝ
              ⟪L2Function.toLp hXL2,
                ex_12_4_2_observed (P := P) c (L2Function.toLp hXL2) (L2Function.toLp hNL2)⟫_ℝ
              EXX k -
            ex_12_4_2_quadraticMSE
              ⟪ex_12_4_2_observed (P := P) c (L2Function.toLp hXL2) (L2Function.toLp hNL2),
                ex_12_4_2_observed (P := P) c (L2Function.toLp hXL2) (L2Function.toLp hNL2)⟫_ℝ
              ⟪L2Function.toLp hXL2,
                ex_12_4_2_observed (P := P) c (L2Function.toLp hXL2) (L2Function.toLp hNL2)⟫_ℝ
              EXX (ex_12_4_2_sourceK c sigmaX2 sigmaN2)) ∧
      ex_12_4_2_mmseEstimate c sigmaX2 sigmaN2
          (fun ω =>
            ex_12_4_2_observed (P := P) c (L2Function.toLp hXL2) (L2Function.toLp hNL2) ω) =
        fun ω =>
          ex_12_4_2_shrinkage c sigmaX2 sigmaN2 *
            ex_12_4_2_unbiasedEstimate c
              (fun ω =>
                ex_12_4_2_observed (P := P) c
                  (L2Function.toLp hXL2) (L2Function.toLp hNL2) ω) ω := by
  have hrawOrth :
      l2Inner P X N hXL2 hNL2 = 0 :=
    ex_12_4_2_independent_noise_orthogonal (P := P) hXL2 hNL2 hXN hX_int hN_int
      hXN_int hN0
  have horth :
      ⟪L2Function.toLp hXL2, L2Function.toLp hNL2⟫_ℝ = 0 := by
    rw [ex_12_4_2_toLp_inner_eq_l2Inner (P := P) hXL2 hNL2, hrawOrth]
  have hXXLp :
      ⟪L2Function.toLp hXL2, L2Function.toLp hXL2⟫_ℝ = sigmaX2 := by
    rw [ex_12_4_2_toLp_inner_eq_l2Inner (P := P) hXL2 hXL2]
    exact hXX
  have hNNLp :
      ⟪L2Function.toLp hNL2, L2Function.toLp hNL2⟫_ℝ = sigmaN2 := by
    rw [ex_12_4_2_toLp_inner_eq_l2Inner (P := P) hNL2 hNL2]
    exact hNN
  have hCross :
      ⟪L2Function.toLp hXL2,
          ex_12_4_2_observed (P := P) c (L2Function.toLp hXL2) (L2Function.toLp hNL2)⟫_ℝ =
          c * sigmaX2 :=
    ex_12_4_2_crossMoment_observed (P := P) c sigmaX2
      (L2Function.toLp hXL2) (L2Function.toLp hNL2) horth hXXLp
  have hObserved :
      ⟪ex_12_4_2_observed (P := P) c (L2Function.toLp hXL2) (L2Function.toLp hNL2),
        ex_12_4_2_observed (P := P) c (L2Function.toLp hXL2) (L2Function.toLp hNL2)⟫_ℝ =
          c ^ 2 * sigmaX2 + sigmaN2 :=
    ex_12_4_2_observed_secondMoment (P := P) c sigmaX2 sigmaN2
      (L2Function.toLp hXL2) (L2Function.toLp hNL2) horth hXXLp hNNLp
  constructor
  · exact hCross
  constructor
  · exact hObserved
  constructor
  · rw [hObserved, hCross]
    exact ex_12_4_2_sourceK_eq_optimalK c sigmaX2 sigmaN2
  constructor
  · intro k
    rw [hObserved, hCross]
    simpa [ex_12_4_2_sourceK_eq_optimalK c sigmaX2 sigmaN2] using
      ex_12_4_2_quadraticMSE_minimal (c ^ 2 * sigmaX2 + sigmaN2)
        (c * sigmaX2) EXX k hden
  · exact ex_12_4_2_mmseEstimate_eq_shrinkage_unbiased c sigmaX2 sigmaN2
      (fun ω =>
        ex_12_4_2_observed (P := P) c (L2Function.toLp hXL2) (L2Function.toLp hNL2) ω) hc
