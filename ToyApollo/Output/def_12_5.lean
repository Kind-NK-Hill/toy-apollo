import Mathlib
import ToyApollo.Output.thm_12_4

/-
TASK ID: def_12_5
TYPE: Definition
SOURCE PLAN: chapter12-closed-subspace-projection
TASK CONTENT:
\begin{defbox}{12.5}
\end{defbox}

(Projection function) Given a closed subspace W inL2(P) and a random variable

Y \in L2(P) , the unique random variable X that minimizes Y - X2 is called

the projection of Y onto W We denote this minimizer as

ProjW (Y) \coloneqqarg min

X\inW

Y - X2.

Many estimation problems can be formulated as projection onto a closed

subspace. The basic linear regression is an example.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- Definition 12.5, projection of `Y` onto a closed subspace `W` of real
`L²(P)`. The value is the unique minimizer supplied by Theorem 12.4. -/
def def_12_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (W : ClosedSubmodule ℝ (Ω →₂[P] ℝ)) (Y : Ω →₂[P] ℝ) : W :=
  Classical.choose (thm_12_4 P W Y)

/-- The projection from Definition 12.5 attains the minimum distance. -/
theorem def_12_5_minimizes {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (W : ClosedSubmodule ℝ (Ω →₂[P] ℝ)) (Y : Ω →₂[P] ℝ) :
    ‖Y - (def_12_5 P W Y : Ω →₂[P] ℝ)‖ =
      ⨅ Z : W, ‖Y - (Z : Ω →₂[P] ℝ)‖ :=
  (Classical.choose_spec (thm_12_4 P W Y)).1

/-- The projection from Definition 12.5 is the only point of `W` attaining the
minimum distance. -/
theorem def_12_5_unique {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (W : ClosedSubmodule ℝ (Ω →₂[P] ℝ)) (Y : Ω →₂[P] ℝ)
    (X : W)
    (hX : ‖Y - (X : Ω →₂[P] ℝ)‖ =
      ⨅ Z : W, ‖Y - (Z : Ω →₂[P] ℝ)‖) :
    X = def_12_5 P W Y :=
  (Classical.choose_spec (thm_12_4 P W Y)).2 X hX
