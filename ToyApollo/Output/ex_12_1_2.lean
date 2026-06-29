import Mathlib
import ToyApollo.Output.def_12_2

/-
TASK ID: ex_12_1_2
TYPE: Example_Proof
SOURCE PLAN: chapter12-l2-norm-inner-product
TASK CONTENT:
\textbf{Example 12.1.2 (A Complex Hilbert Space of Infinite Dimension)} \\

Let \Omega ={ 1, 2, 3,... } be the sample space, and the power set P(\Omega) be the \sigma-algebra. Consider a

probability measure P defined on \Omega by

P({k}) \coloneqq 1

2k

for k \geq 1. A random variable X can be identified with an infinite complex sequence

X (x1,x 2,x 3,... ) ,

where xk are complex numbers for k = 1, 2, 3,... .

The random variable X belongs to L 2(P) if and only if the series \sum\infty

k=1 \vertxk\vert2/2k is convergent.

If we are given another random variable Y , whose values at 1 , 2, 3, 4,.are y 1,y 2,y 3,y 4,... ,t h e

inner product between X and Y is given by

\langleX, Y\rangle=

\infty\sum

k=1

x*

k yk/2k.

Here, x *

k denotes the complex conjugate of x k .

The followings are other basic properties of inner product.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

open scoped ENNReal BigOperators

noncomputable section

/-- The countably infinite sample space `{1, 2, 3, ...}` from Example 12.1.2,
encoded by `ℕ`; the Lean index `n` corresponds to the textbook point `k = n+1`. -/
abbrev ex_12_1_2_space := ℕ

/-- The geometric point mass at the Lean index `n`, corresponding to
`P({n+1}) = 1 / 2^(n+1)`. -/
def ex_12_1_2_weight (n : ex_12_1_2_space) : ENNReal :=
  (2⁻¹ : ENNReal) ^ (n + 1)

/-- The same point mass as a real scalar, used in Bochner-integral sums. -/
noncomputable def ex_12_1_2_realWeight (n : ex_12_1_2_space) : ℝ :=
  (ex_12_1_2_weight n).toReal

/-- The real scalar weight is the textbook `1 / 2^(n+1)`. -/
theorem ex_12_1_2_realWeight_eq (n : ex_12_1_2_space) :
    ex_12_1_2_realWeight n = (1 / (2 : ℝ) ^ (n + 1)) := by
  simp [ex_12_1_2_realWeight, ex_12_1_2_weight, one_div]

/-- The probability measure on the countable sample space with masses
`1 / 2^(n+1)`. -/
noncomputable def ex_12_1_2_measure : Measure ex_12_1_2_space :=
  Measure.sum fun n => ex_12_1_2_weight n • Measure.dirac n

theorem ex_12_1_2_weight_ne_top (n : ex_12_1_2_space) :
    ex_12_1_2_weight n ≠ ⊤ := by
  simp [ex_12_1_2_weight]

/-- The point masses sum to one, so the constructed measure is a probability
measure. -/
theorem ex_12_1_2_measure_univ :
    ex_12_1_2_measure Set.univ = 1 := by
  rw [ex_12_1_2_measure]
  simpa [ex_12_1_2_weight, Measure.sum_apply,
    ENNReal.tsum_geometric_add_one] using
    (ENNReal.inv_mul_cancel (by norm_num : (2 : ENNReal) ≠ 0)
      (by simp : (2 : ENNReal) ≠ ⊤))

/-- A complex random variable on the countable sample space is the same data as
an infinite complex sequence. -/
def ex_12_1_2_sequenceOfRandomVariable
    (X : ex_12_1_2_space → ℂ) : ℕ → ℂ :=
  X

/-- Conversely, an infinite complex sequence defines a complex random variable
on the countable sample space. -/
def ex_12_1_2_randomVariableOfSequence
    (x : ℕ → ℂ) : ex_12_1_2_space → ℂ :=
  x

/-- The two descriptions are definitionally the same under the `ℕ` encoding. -/
theorem ex_12_1_2_sequence_correspondence
    (X : ex_12_1_2_space → ℂ) :
    ex_12_1_2_randomVariableOfSequence
      (ex_12_1_2_sequenceOfRandomVariable X) = X :=
  rfl

/-- The textbook weighted square series for membership in `L²(P)`. -/
def ex_12_1_2_L2Series (X : ex_12_1_2_space → ℂ) : Prop :=
  Summable fun n => ex_12_1_2_realWeight n * ‖X n‖ ^ 2

/-- On this countable probability space, `X ∈ L²(P)` exactly means that the
weighted square series `Σ |xₙ|² / 2ⁿ` converges. -/
theorem ex_12_1_2_memLp_iff_series
    (X : ex_12_1_2_space → ℂ) :
    MemLp X (2 : ENNReal) ex_12_1_2_measure ↔
      ex_12_1_2_L2Series X := by
  have hX : AEStronglyMeasurable X ex_12_1_2_measure :=
    (measurable_of_countable X).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hX, ex_12_1_2_L2Series]
  have hfinite : ∀ n, ex_12_1_2_weight n ≠ ⊤ :=
    ex_12_1_2_weight_ne_top
  constructor
  · intro h
    have hs_abs : Summable fun n : ex_12_1_2_space =>
        (ex_12_1_2_weight n).toReal * |‖X n‖ ^ 2| := by
      exact (integrable_sum_dirac_iff
        (f := fun n : ex_12_1_2_space => ‖X n‖ ^ 2)
        (x := fun n : ex_12_1_2_space => n)
        (c := ex_12_1_2_weight) hfinite).mp
        (by simpa [ex_12_1_2_measure] using h)
    exact hs_abs.congr fun n => by
      simp [ex_12_1_2_realWeight, abs_of_nonneg (sq_nonneg (‖X n‖))]
  · intro h
    have hs_abs : Summable fun n : ex_12_1_2_space =>
        (ex_12_1_2_weight n).toReal * |‖X n‖ ^ 2| :=
      h.congr fun n => by
        simp [ex_12_1_2_realWeight, abs_of_nonneg (sq_nonneg (‖X n‖))]
    have hint : Integrable (fun n : ex_12_1_2_space => ‖X n‖ ^ 2)
        (Measure.sum fun n => ex_12_1_2_weight n • Measure.dirac n) :=
      (integrable_sum_dirac_iff
        (f := fun n : ex_12_1_2_space => ‖X n‖ ^ 2)
        (x := fun n : ex_12_1_2_space => n)
        (c := ex_12_1_2_weight) hfinite).mpr hs_abs
    simpa [ex_12_1_2_measure] using hint

/-- Complex conjugation preserves `L²` membership in this example. -/
theorem ex_12_1_2_star_memLp
    {X : ex_12_1_2_space → ℂ}
    (hX : MemLp X (2 : ENNReal) ex_12_1_2_measure) :
    MemLp (fun n => star (X n)) (2 : ENNReal) ex_12_1_2_measure := by
  refine hX.of_le_mul (c := 1)
    ((measurable_of_countable fun n : ex_12_1_2_space => star (X n)).aestronglyMeasurable)
    ?_
  filter_upwards with n
  simp [norm_star]

/-- If `X` and `Y` are in `L²(P)`, then the complex inner-product integrand
`X*Y` is integrable. -/
theorem ex_12_1_2_inner_integrable_of_memLp
    {X Y : ex_12_1_2_space → ℂ}
    (hX : MemLp X (2 : ENNReal) ex_12_1_2_measure)
    (hY : MemLp Y (2 : ENNReal) ex_12_1_2_measure) :
    Integrable (fun n => star (X n) * Y n) ex_12_1_2_measure := by
  have hstar : MemLp (fun n => star (X n)) (2 : ENNReal)
      ex_12_1_2_measure :=
    ex_12_1_2_star_memLp hX
  simpa [Pi.mul_apply] using hstar.integrable_mul hY

/-- The complex `L²` inner product from Definition 12.2 becomes the weighted
series `Σ conj(xₙ)yₙ / 2ⁿ` on this countable example. -/
theorem ex_12_1_2_inner_formula
    (X Y : ex_12_1_2_space → ℂ)
    (hX : MemLp X (2 : ENNReal) ex_12_1_2_measure)
    (hY : MemLp Y (2 : ENNReal) ex_12_1_2_measure) :
    complexL2Inner ex_12_1_2_measure X Y hX hY =
      ∑' n : ex_12_1_2_space,
        ex_12_1_2_realWeight n • (star (X n) * Y n) := by
  have hXY : Integrable (fun n => star (X n) * Y n) ex_12_1_2_measure :=
    ex_12_1_2_inner_integrable_of_memLp hX hY
  have hfinite : ∀ n, ex_12_1_2_weight n ≠ ⊤ :=
    ex_12_1_2_weight_ne_top
  have hs : Summable fun n : ex_12_1_2_space =>
      (ex_12_1_2_weight n).toReal *
        ‖star (X n) * Y n‖ := by
    simpa [ex_12_1_2_measure] using
      (Integrable.summable_of_dirac
        (f := fun n : ex_12_1_2_space => star (X n) * Y n)
        (x := fun n : ex_12_1_2_space => n)
        (c := ex_12_1_2_weight) hXY)
  rw [complexL2Inner, ex_12_1_2_measure]
  simpa [ex_12_1_2_realWeight] using
    (integral_sum_dirac_eq_tsum
      (f := fun n : ex_12_1_2_space => star (X n) * Y n)
      (x := fun n : ex_12_1_2_space => n)
      (c := ex_12_1_2_weight) hfinite hs)

/-- Example 12.1.2 packaged: the geometric measure is a probability measure,
random variables are complex sequences, `L²` membership is weighted square
summability, and the complex inner product is the weighted conjugate series. -/
theorem ex_12_1_2 (X Y : ex_12_1_2_space → ℂ)
    (hX : MemLp X (2 : ENNReal) ex_12_1_2_measure)
    (hY : MemLp Y (2 : ENNReal) ex_12_1_2_measure) :
    ex_12_1_2_measure Set.univ = 1 ∧
      (MemLp X (2 : ENNReal) ex_12_1_2_measure ↔
        ex_12_1_2_L2Series X) ∧
      complexL2Inner ex_12_1_2_measure X Y hX hY =
        ∑' n : ex_12_1_2_space,
          ex_12_1_2_realWeight n • (star (X n) * Y n) := by
  exact ⟨ex_12_1_2_measure_univ,
    ex_12_1_2_memLp_iff_series X,
    ex_12_1_2_inner_formula X Y hX hY⟩
