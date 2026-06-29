import Mathlib
import ToyApollo.Output.def_12_4
import ToyApollo.Output.def_12_5

/-
TASK ID: ex_12_2_3
TYPE: Example_Proof
SOURCE PLAN: chapter12-closed-subspace-projection
TASK CONTENT:
\textbf{Example 12.2.3 (Linear Regression as Projection)} \\

Given n data points .(xi,yi),f o r i = 1, 2,...,n , the problem of linear regression is to find

coefficients a and b that minimize the mean-squared error .

\sumn

i=1(yi - axi - b)2T of o r m u l a t e

this problem as a projection, we can consider a finite sample space \Omega ={ 1, 2,...,n } equipped

with the discrete\sigma-field and the uniform distribution P The data are represented by two functions

X, Y : \Omega \to R,d e fi n e db yX(i) = xi andY(i) = yi ,f o ri = 1, 2,...,n Let I denote the all-one

function on. \Omega .

The mean square error can be expressed as

nE[(Y - aX - bI) 2]= nY - aX - bI2

2.

Define a subspace of L2(P) by

W ={ aX + bI : a \inR,b \inR}.

This subspace is closed because it has finite dimension. We can interpret the optimal choice of a

and b as the projection of the random variable Y onto the closed subspace W .
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

open scoped InnerProductSpace BigOperators

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
  [IsProbabilityMeasure P]

/-- The fitted linear-regression random variable `aX + bI`. -/
def ex_12_2_3_fit (X I : Ω →₂[P] ℝ) (a b : ℝ) : Ω →₂[P] ℝ :=
  a • X + b • I

/-- The regression subspace `W = {aX + bI : a,b ∈ ℝ}`. -/
def ex_12_2_3_W (X I : Ω →₂[P] ℝ) : Submodule ℝ (Ω →₂[P] ℝ) :=
  Submodule.span ℝ ({X, I} : Set (Ω →₂[P] ℝ))

instance ex_12_2_3_W_finiteDimensional (X I : Ω →₂[P] ℝ) :
    FiniteDimensional ℝ (ex_12_2_3_W (P := P) X I) := by
  exact Module.Finite.of_fg
    (Submodule.fg_span
      (show ({X, I} : Set (Ω →₂[P] ℝ)).Finite by simp))

theorem ex_12_2_3_fit_mem (X I : Ω →₂[P] ℝ) (a b : ℝ) :
    ex_12_2_3_fit (P := P) X I a b ∈ ex_12_2_3_W (P := P) X I := by
  unfold ex_12_2_3_fit ex_12_2_3_W
  exact Submodule.add_mem _
    (Submodule.smul_mem _ a (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ b (Submodule.subset_span (by simp)))

/-- The regression subspace is closed because it is finite-dimensional. -/
theorem ex_12_2_3_W_closed (X I : Ω →₂[P] ℝ) :
    IsClosed ((ex_12_2_3_W (P := P) X I : Submodule ℝ (Ω →₂[P] ℝ)) :
      Set (Ω →₂[P] ℝ)) := by
  exact finiteDimensional_submodule_isClosed (ex_12_2_3_W (P := P) X I)

/-- The regression subspace as a closed submodule, so Definition 12.5 can be
applied. -/
def ex_12_2_3_closedW (X I : Ω →₂[P] ℝ) : ClosedSubmodule ℝ (Ω →₂[P] ℝ) :=
  ClosedSubmodule.mk (ex_12_2_3_W (P := P) X I)
    (ex_12_2_3_W_closed (P := P) X I)

/-- The mean-square regression objective in `L²(P)` norm form. -/
def ex_12_2_3_meanSquareError (Y X I : Ω →₂[P] ℝ) (a b : ℝ) : ℝ :=
  ‖Y - ex_12_2_3_fit (P := P) X I a b‖ ^ 2

/-- The projection of `Y` onto the regression subspace. -/
def ex_12_2_3_projection (Y X I : Ω →₂[P] ℝ) :
    ex_12_2_3_closedW (P := P) X I :=
  def_12_5 P (ex_12_2_3_closedW (P := P) X I) Y

theorem ex_12_2_3_projection_minimizes (Y X I : Ω →₂[P] ℝ) :
    ‖Y - (ex_12_2_3_projection (P := P) Y X I : Ω →₂[P] ℝ)‖ =
      ⨅ Z : ex_12_2_3_closedW (P := P) X I,
        ‖Y - (Z : Ω →₂[P] ℝ)‖ := by
  exact def_12_5_minimizes P (ex_12_2_3_closedW (P := P) X I) Y

/-- Example 12.2.3: linear regression is projection of `Y` onto the closed
subspace spanned by `X` and the all-one regressor `I`. -/
theorem ex_12_2_3 (Y X I : Ω →₂[P] ℝ) :
    (∀ a b : ℝ,
        ex_12_2_3_fit (P := P) X I a b ∈ ex_12_2_3_W (P := P) X I) ∧
      IsClosed ((ex_12_2_3_W (P := P) X I : Submodule ℝ (Ω →₂[P] ℝ)) :
        Set (Ω →₂[P] ℝ)) ∧
      ‖Y - (ex_12_2_3_projection (P := P) Y X I : Ω →₂[P] ℝ)‖ =
        ⨅ Z : ex_12_2_3_closedW (P := P) X I,
          ‖Y - (Z : Ω →₂[P] ℝ)‖ := by
  exact ⟨fun a b => ex_12_2_3_fit_mem (P := P) X I a b,
    ex_12_2_3_W_closed (P := P) X I,
    ex_12_2_3_projection_minimizes (P := P) Y X I⟩
