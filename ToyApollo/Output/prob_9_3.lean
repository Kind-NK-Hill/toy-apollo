import ToyApollo.Output.prob_9_3_proof_support

/-
TASK ID: prob_9_3
TYPE: Problem
SOURCE PLAN: chapter9-problems
TASK CONTENT:
\textbf{Problem 9.3} By using characteristic function, show that the sum of two
independent Gamma random variables with distributions $\Gamma(\alpha_1,\beta)$
and $\Gamma(\alpha_2,\beta)$ has distribution
$\Gamma(\alpha_1+\alpha_2,\beta)$.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

noncomputable section

/-- Problem 9.3: by characteristic functions, the sum of two independent Gamma
random variables with the same source scale parameter is Gamma with the summed
shape and the same scale. -/
theorem prob_9_3
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X Y : Omega -> ℝ} {alpha1 alpha2 beta : ℝ}
    (halpha1 : 0 < alpha1) (halpha2 : 0 < alpha2) (hbeta : 0 < beta)
    (hX : HasSourceScaleGammaLaw P X alpha1 beta)
    (hY : HasSourceScaleGammaLaw P Y alpha2 beta)
    (hXY : X ⟂ᵢ[P] Y) :
    HasSourceScaleGammaLaw P (fun omega => X omega + Y omega)
      (alpha1 + alpha2) beta :=
  prob_9_3_support_result halpha1 halpha2 hbeta hX hY hXY
