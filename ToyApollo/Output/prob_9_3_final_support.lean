import ToyApollo.Output.prob_9_3_law_support

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

noncomputable section

/-- Problem 9.3: by characteristic functions, the sum of two independent Gamma
random variables with the same source scale parameter is Gamma with the summed
shape and the same scale. -/
theorem prob_9_3_support_result
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X Y : Omega -> ℝ} {alpha1 alpha2 beta : ℝ}
    (halpha1 : 0 < alpha1) (halpha2 : 0 < alpha2) (hbeta : 0 < beta)
    (hX : HasSourceScaleGammaLaw P X alpha1 beta)
    (hY : HasSourceScaleGammaLaw P Y alpha2 beta)
    (hXY : X ⟂ᵢ[P] Y) :
    HasSourceScaleGammaLaw P (fun omega => X omega + Y omega)
      (alpha1 + alpha2) beta :=
  prob_9_3_of_sourceScaleGammaCharacteristicFunctionInterface
    halpha1 halpha2 hbeta
    sourceScaleGammaCharacteristicFunctionInterface_proved hX hY hXY
