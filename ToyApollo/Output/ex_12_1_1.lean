import Mathlib
import ToyApollo.Output.def_12_2

/-
TASK ID: ex_12_1_1
TYPE: Example_Proof
SOURCE PLAN: chapter12-l2-norm-inner-product
TASK CONTENT:
\textbf{Example 12.1.1 (A Finite Inner Product Space)} \\

Consider a finite probability space with sample space \Omega ={ a, b, c}The \sigma-algebra is the discrete

\sigma-algebra P(\Omega) , and the probability measure is given by P({a}) = pa , P({b}) = pb, P({c}) =

pc,w h e r e pa , pb,a n d pc are nonnegative real numbers that sum to 1.

We can specify a random variable X by giving its value at the three points in \Omega , which can be

represented as a vector (X(a), X(b), X(c))Conversely, any three-dimensional vector (x1,x 2,x 3)

is associated to a random variable X by defining X(a) \coloneqqx1, X(b) \coloneqqx2,a n d X(c) \coloneqqx3. Thus,

the random variables in this probability space have a one-to-one correspondence with the vectors

in a three-dimensional vector space over R.

The inner product between two random variables X and Y , which are represented by vectors

(x1,x 2,x 3) and (y1,y 2,y 3), respectively, is computed as

\langleX, Y\rangle= pax1y1 + pbx2y2 + pcx3y3.

The second moment of a random variable X is thus equal to pax2

1 + pbx2

2 + pbx2

3 .
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

noncomputable section

/-- The three-point sample space `{a, b, c}` from Example 12.1.1, represented
as `Fin 3`. -/
abbrev ex_12_1_1_space := Fin 3

/-- The point `a` in the three-point sample space. -/
abbrev ex_12_1_1_a : ex_12_1_1_space := ⟨0, by decide⟩

/-- The point `b` in the three-point sample space. -/
abbrev ex_12_1_1_b : ex_12_1_1_space := ⟨1, by decide⟩

/-- The point `c` in the three-point sample space. -/
abbrev ex_12_1_1_c : ex_12_1_1_space := ⟨2, by decide⟩

/-- The point masses arranged as a function on the three-point space. -/
def ex_12_1_1_weight (pa pb pc : NNReal) : ex_12_1_1_space → ENNReal
  | 0 => (pa : ENNReal)
  | 1 => (pb : ENNReal)
  | 2 => (pc : ENNReal)

/-- A probability measure on the three-point space with masses `pa`, `pb`,
and `pc` at `a`, `b`, and `c`. -/
noncomputable def ex_12_1_1_measure (pa pb pc : NNReal) :
    Measure ex_12_1_1_space :=
  Measure.sum fun i => ex_12_1_1_weight pa pb pc i • Measure.dirac i

/-- The total mass is the sum of the three point masses. -/
theorem ex_12_1_1_measure_univ (pa pb pc : NNReal) :
    ex_12_1_1_measure pa pb pc Set.univ =
      (pa : ENNReal) + (pb : ENNReal) + (pc : ENNReal) := by
  simp [ex_12_1_1_measure, ex_12_1_1_weight, Fin.sum_univ_three,
    ENNReal.smul_def, add_assoc]

/-- Thus the measure is a probability measure when the three masses sum to one. -/
theorem ex_12_1_1_measure_univ_of_sum_one {pa pb pc : NNReal}
    (hsum : pa + pb + pc = 1) :
    ex_12_1_1_measure pa pb pc Set.univ = 1 := by
  have hsum' : ((pa : ENNReal) + (pb : ENNReal) + (pc : ENNReal)) = 1 := by
    exact_mod_cast hsum
  simpa [ex_12_1_1_measure_univ] using hsum'

/-- A real vector `(x₁, x₂, x₃)` is the same data as a random variable on the
three-point sample space. -/
def ex_12_1_1_randomVariableOfVector (x : Fin 3 → ℝ) :
    ex_12_1_1_space → ℝ :=
  x

/-- Conversely, every real-valued random variable on the three-point space is
represented by its three values. -/
theorem ex_12_1_1_vector_correspondence (X : ex_12_1_1_space → ℝ) :
    ex_12_1_1_randomVariableOfVector (fun i => X i) = X :=
  rfl

/-- The weighted inner product formula in Example 12.1.1. -/
theorem ex_12_1_1_inner_formula (pa pb pc : NNReal)
    (X Y : ex_12_1_1_space → ℝ)
    (hX : L2Function (ex_12_1_1_measure pa pb pc) X)
    (hY : L2Function (ex_12_1_1_measure pa pb pc) Y) :
    l2Inner (ex_12_1_1_measure pa pb pc) X Y hX hY =
      (pa : ℝ) * X ex_12_1_1_a * Y ex_12_1_1_a +
        (pb : ℝ) * X ex_12_1_1_b * Y ex_12_1_1_b +
          (pc : ℝ) * X ex_12_1_1_c * Y ex_12_1_1_c := by
  rw [l2Inner, ex_12_1_1_measure]
  have hfinite : ∀ i, ex_12_1_1_weight pa pb pc i ≠ ⊤ := by
    intro i
    fin_cases i <;> simp [ex_12_1_1_weight]
  rw [integral_sum_dirac (x := fun i : ex_12_1_1_space => i)
    (c := ex_12_1_1_weight pa pb pc) hfinite]
  simp [ex_12_1_1_weight, ex_12_1_1_a, ex_12_1_1_b, ex_12_1_1_c,
    Fin.sum_univ_three, mul_assoc, add_assoc]

/-- The second moment is the weighted sum of squares of the three coordinates. -/
theorem ex_12_1_1_second_moment_formula (pa pb pc : NNReal)
    (X : ex_12_1_1_space → ℝ)
    (hX : L2Function (ex_12_1_1_measure pa pb pc) X) :
    l2Inner (ex_12_1_1_measure pa pb pc) X X hX hX =
      (pa : ℝ) * (X ex_12_1_1_a) ^ 2 +
        (pb : ℝ) * (X ex_12_1_1_b) ^ 2 +
          (pc : ℝ) * (X ex_12_1_1_c) ^ 2 := by
  simpa [pow_two, mul_assoc] using
    ex_12_1_1_inner_formula pa pb pc X X hX hX

/-- Example 12.1.1: on a three-point probability space, random variables are
three-dimensional vectors and the `L²` inner product is the weighted dot
product. -/
theorem ex_12_1_1 (pa pb pc : NNReal) (X Y : ex_12_1_1_space → ℝ)
    (hX : L2Function (ex_12_1_1_measure pa pb pc) X)
    (hY : L2Function (ex_12_1_1_measure pa pb pc) Y) :
    ex_12_1_1_measure pa pb pc Set.univ =
      (pa : ENNReal) + (pb : ENNReal) + (pc : ENNReal) ∧
      l2Inner (ex_12_1_1_measure pa pb pc) X Y hX hY =
        (pa : ℝ) * X ex_12_1_1_a * Y ex_12_1_1_a +
          (pb : ℝ) * X ex_12_1_1_b * Y ex_12_1_1_b +
            (pc : ℝ) * X ex_12_1_1_c * Y ex_12_1_1_c ∧
        l2Inner (ex_12_1_1_measure pa pb pc) X X hX hX =
          (pa : ℝ) * (X ex_12_1_1_a) ^ 2 +
            (pb : ℝ) * (X ex_12_1_1_b) ^ 2 +
              (pc : ℝ) * (X ex_12_1_1_c) ^ 2 := by
  exact ⟨ex_12_1_1_measure_univ pa pb pc,
    ex_12_1_1_inner_formula pa pb pc X Y hX hY,
    ex_12_1_1_second_moment_formula pa pb pc X hX⟩
