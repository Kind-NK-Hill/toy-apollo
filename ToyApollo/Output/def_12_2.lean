import Mathlib
import ToyApollo.Output.def_7_3
import ToyApollo.Output.def_12_1

/-
TASK ID: def_12_2
TYPE: Definition
SOURCE PLAN: chapter12-l2-norm-inner-product
TASK CONTENT:
\begin{defbox}{12.2}
\end{defbox}

Let (\Omega, \mathcal{F},P) be a probability space. We define the inner product of two real-

valued random variables in L2(P) by

\langleX, Y\rangle\coloneqqE[XY ].

We define the L2-norm of X by

X2 \coloneqq

\sqrt

\langleX, X\rangle=

\sqrt

E[X2].

Two random variables X and Y are said to be orthogonal if \langleX, Y\rangle= 0. We will

sometime write Xwithout the subscript 2 to simplify notation.

This notion of orthogonality is analogous to the concept of perpendicularity in

Euclidean geometry. When random variables X and Y have zero mean, then they

are orthogonal iff they are uncorrelated.

Complex Inner Product For complex random variables, the inner product is

defined as E [X*Y], where X* denotes the complex conjugate of X.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

/-- Textbook real `L²(P)` inner product, defined as `E[XY]` for
square-integrable random variables. -/
noncomputable def l2Inner {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ)
    (hX : L2Function P X) (hY : L2Function P Y) : ℝ :=
  P[fun ω => X ω * Y ω]

/-- The product in the real `L²` inner product is integrable for
square-integrable random variables. -/
theorem l2Inner_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ℝ} (hX : L2Function P X) (hY : L2Function P Y) :
    Integrable (fun ω => X ω * Y ω) P :=
  L2Function.integrable_mul hX hY

/-- Textbook `L²` norm, `sqrt(<X, X>) = sqrt(E[X^2])`. -/
noncomputable def l2Norm {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (hX : L2Function P X) : ℝ :=
  Real.sqrt (l2Inner P X X hX hX)

theorem l2Norm_eq_sqrt_expectation_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (hX : L2Function P X) :
    l2Norm P X hX = Real.sqrt (P[fun ω => X ω ^ 2]) := by
  simp [l2Norm, l2Inner, pow_two]

/-- Textbook orthogonality in `L²(P)`. -/
def L2Orthogonal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ)
    (hX : L2Function P X) (hY : L2Function P Y) : Prop :=
  l2Inner P X Y hX hY = 0

/-- For zero-mean random variables, textbook orthogonality is the same as the
Chapter 7 notion of being uncorrelated. -/
theorem l2Orthogonal_iff_uncorrelated_of_mean_zero {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ}
    (hX : L2Function P X) (hY : L2Function P Y)
    (hX0 : P[X] = 0) (hY0 : P[Y] = 0) :
    L2Orthogonal P X Y hX hY ↔ Uncorrelated P X Y := by
  rw [L2Orthogonal, l2Inner, Uncorrelated, hX0, hY0, mul_zero]

/-- Complex `L²(P)` membership for the complex inner-product clause. -/
def ComplexL2Function {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℂ) : Prop :=
  MemLp X (2 : ENNReal) P

/-- Textbook complex `L²(P)` inner product, `E[X*Y]`. -/
noncomputable def complexL2Inner {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℂ)
    (_hX : ComplexL2Function P X) (_hY : ComplexL2Function P Y) : ℂ :=
  ∫ ω, star (X ω) * Y ω ∂P

/-- Exported real inner product definition for Definition 12.2. -/
noncomputable def def_12_2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ)
    (hX : L2Function P X) (hY : L2Function P Y) : ℝ :=
  l2Inner P X Y hX hY
