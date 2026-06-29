import Mathlib
import ToyApollo.Output.thm_12_4
import ToyApollo.Output.def_12_5
import ToyApollo.Output.def_12_2

/-
TASK ID: thm_12_5
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter12-orthogonality-principle
TASK CONTENT:
\begin{thmbox}{12.5 (Orthogonality Principle)}
\end{thmbox}

Given a random variable Y in L2(P) and a closed subspace W in L2(P) ,t h e

projection of Y onto W is characterized by

X* =Proj W (Y) X * \inW and \langleY- X *,X \rangle= 0 X\in W.

\textit{Proof} ( . ) Suppose. X* is the random variable in W that minimizes Y- X over

all X\in W We need to show that \langleY- X *,X \rangle= 0 for all X\in W We proceed by

contradiction. Suppose there exists a random variable X0 in W such that Y- X * is

not orthogonal to X0, ie.,\langleY- X *,X 0\rangle /=0 We can then deduce that X* is not the

minimizer.

One way to see this by completing the square. Consider

Y- (X * -uX 0)2

as a function of u Since X* minimizes Y- X over all X\in W , this function is

minimized atu= 0 Expanding it as a polynomial in u ,we have

uX0 +Y - X *2 =u 2X02 +2 u\langleX0,Y - X *\rangle+ Y- X *2.

Since it is assumed that \langleX0,Y - X *\rangle /=0 ,t h e. L2 normX02 should be nonzero.

We complete the square and write the above expression as

X02

(

u+ \langleX0,Y - X *\rangle

X02

) 2

- \langleX0,Y - X *\rangle2

X02 + Y- X *2.

We can pick the value of u such that the square in the first term is zero. Then,

- \langleX0,Y - X *\rangle2

X02 + Y- X *2

is strictly less than Y- X *2. This contradicts the minimality of Y- X *2, and

hence, we must have \langleY- X *,X 0\rangle= 0.

(. ) Suppose. X is a random variable such that

\langleY- X,X \rangle= 0 for allX \in W. (12.2)

We want to show that X coincides with ProjW (Y) We havej u s tp r o v e di nt h e

previous paragraph that ProjW (Y)= X * satisfies

\langleY- Proj W (Y), X\rangle= 0 for allX \in W. (12.3)

By subtracting (12.3) from (12.2), we get

\langleProjW (Y)- X,X \rangle= 0 for allX \in W. (12.4)

Moreover,ProjW (Y)- X is a random variable in W because both ProjW (Y) and. X

are in W and W is a subspace. Hence, in (12.4), we can substitute X by. ProjW (Y)-

X to getProj W (Y)- X2 =0 This proves that ProjW (Y)= X almost surely. \hfill $\square$

In view of the Orthogonality Principle, we can interpret the minimum mean-

squared error (MMSE) estimator geometrically as a projection operator.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- The projection from Definition 12.5 has an error vector orthogonal to the
closed subspace. This is the forward implication in the textbook orthogonality
principle. -/
theorem thm_12_5_projection_orthogonal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ClosedSubmodule ℝ (Ω →₂[P] ℝ))
    (Y : Ω →₂[P] ℝ) :
    ∀ X : W,
      ⟪Y - (def_12_5 P W Y : Ω →₂[P] ℝ),
        (X : Ω →₂[P] ℝ)⟫_ℝ = 0 := by
  have hmin := def_12_5_minimizes P W Y
  have horth := (W.norm_eq_iInf_iff_inner_eq_zero (def_12_5 P W Y).2).1 hmin
  intro X
  exact horth X X.2

/-- Conversely, any point of `W` whose error vector is orthogonal to `W` is the
projection of `Y` onto `W`. -/
theorem thm_12_5_orthogonal_unique {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ClosedSubmodule ℝ (Ω →₂[P] ℝ))
    (Y : Ω →₂[P] ℝ) (X : W)
    (horth : ∀ Z : W,
      ⟪Y - (X : Ω →₂[P] ℝ), (Z : Ω →₂[P] ℝ)⟫_ℝ = 0) :
    X = def_12_5 P W Y := by
  have hmin : ‖Y - (X : Ω →₂[P] ℝ)‖ =
      ⨅ Z : W, ‖Y - (Z : Ω →₂[P] ℝ)‖ := by
    refine (W.norm_eq_iInf_iff_inner_eq_zero X.2).2 ?_
    intro Z hZ
    exact horth ⟨Z, hZ⟩
  exact def_12_5_unique P W Y X hmin

/-- Theorem 12.5, Orthogonality Principle: a point of the closed subspace is the
projection iff the projection error is orthogonal to every point of the subspace. -/
theorem thm_12_5 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ClosedSubmodule ℝ (Ω →₂[P] ℝ))
    (Y : Ω →₂[P] ℝ) (X : W) :
    X = def_12_5 P W Y ↔
      ∀ Z : W,
        ⟪Y - (X : Ω →₂[P] ℝ), (Z : Ω →₂[P] ℝ)⟫_ℝ = 0 := by
  constructor
  · intro hX
    subst X
    exact thm_12_5_projection_orthogonal P W Y
  · exact thm_12_5_orthogonal_unique P W Y X
