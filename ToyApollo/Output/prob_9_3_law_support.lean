/-
TASK ID: prob_9_3_law_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.prob_9_3_fourier_support

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

noncomputable section

def HasSourceScaleGammaLaw
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega) (X : Omega -> ℝ)
    (alpha beta : ℝ) : Prop :=
  HasLaw X (sourceScaleGammaMeasure alpha beta) P

def HasGammaCharacteristicFunction
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega) (X : Omega -> ℝ)
    (alpha beta : ℝ) : Prop :=
  ∀ t : ℝ, characteristicFunction (P.map X) t =
    gammaCharacteristicFunctionFormula alpha beta t

def SourceScaleGammaCharacteristicFunctionInterface : Prop :=
  ∀ {alpha beta : ℝ}, 0 < alpha -> 0 < beta -> ∀ t : ℝ,
    charFun (sourceScaleGammaMeasure alpha beta) t =
      gammaCharacteristicFunctionFormula alpha beta t

theorem sourceScaleGammaCharacteristicFunctionInterface_of_gammaMeasure_charFun_rate
    (hcf_rate : ∀ {alpha r : ℝ}, 0 < alpha -> 0 < r -> ∀ t : ℝ,
      charFun (gammaMeasure alpha r) t =
        gammaCharacteristicFunctionRateFormula alpha r t) :
    SourceScaleGammaCharacteristicFunctionInterface := by
  intro alpha beta halpha hbeta t
  calc
    charFun (sourceScaleGammaMeasure alpha beta) t =
        gammaCharacteristicFunctionRateFormula alpha beta⁻¹ t := by
      simpa [sourceScaleGammaMeasure] using
        hcf_rate halpha (inv_pos.mpr hbeta) t
    _ = gammaCharacteristicFunctionFormula alpha beta t :=
      gammaCharacteristicFunctionRateFormula_inv_eq_scale hbeta.ne'

theorem sourceScaleGammaCharacteristicFunctionInterface_of_gammaPDFReal_fourier_integral
    (hpdf : ∀ {alpha r : ℝ}, 0 < alpha -> 0 < r -> ∀ t : ℝ,
      ∫ x : ℝ,
          Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) *
            (ProbabilityTheory.gammaPDFReal alpha r x : ℂ) =
        gammaCharacteristicFunctionRateFormula alpha r t) :
    SourceScaleGammaCharacteristicFunctionInterface :=
  sourceScaleGammaCharacteristicFunctionInterface_of_gammaMeasure_charFun_rate
    (gammaMeasure_charFun_rate_of_gammaPDFReal_fourier_integral hpdf)

theorem sourceScaleGammaCharacteristicFunctionInterface_proved :
    SourceScaleGammaCharacteristicFunctionInterface :=
  sourceScaleGammaCharacteristicFunctionInterface_of_gammaMeasure_charFun_rate
    (fun halpha hr t => gammaMeasure_charFun_rate halpha hr t)

theorem gammaCharacteristicFunctionFormula_mul_same_scale
    (alpha1 alpha2 beta t : ℝ) :
    gammaCharacteristicFunctionFormula alpha1 beta t *
        gammaCharacteristicFunctionFormula alpha2 beta t =
      gammaCharacteristicFunctionFormula (alpha1 + alpha2) beta t := by
  unfold gammaCharacteristicFunctionFormula
  rw [← Complex.exp_add]
  congr 1
  norm_num [Complex.ofReal_add]
  ring_nf

theorem hasGammaCharacteristicFunction_of_sourceScaleGammaLaw
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : Omega -> ℝ} {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hcf : SourceScaleGammaCharacteristicFunctionInterface)
    (hX : HasSourceScaleGammaLaw P X alpha beta) :
    HasGammaCharacteristicFunction P X alpha beta := by
  intro t
  calc
    characteristicFunction (P.map X) t = charFun (P.map X) t := by
      exact characteristicFunction_law_eq_charFun hX.aemeasurable t
    _ = charFun (sourceScaleGammaMeasure alpha beta) t := by
      rw [hX.map_eq]
    _ = gammaCharacteristicFunctionFormula alpha beta t :=
      hcf halpha hbeta t

theorem independent_sum_has_gamma_characteristic_function
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} [IsFiniteMeasure P]
    {X Y : Omega -> ℝ} {alpha1 alpha2 beta : ℝ}
    (hXmeas : AEMeasurable X P) (hYmeas : AEMeasurable Y P)
    (hXY : X ⟂ᵢ[P] Y)
    (hX : HasGammaCharacteristicFunction P X alpha1 beta)
    (hY : HasGammaCharacteristicFunction P Y alpha2 beta) :
    HasGammaCharacteristicFunction P (fun omega => X omega + Y omega)
      (alpha1 + alpha2) beta := by
  intro t
  rw [characteristicFunction_indep_add_eq_mul hXmeas hYmeas hXY t]
  rw [hX t, hY t]
  exact gammaCharacteristicFunctionFormula_mul_same_scale alpha1 alpha2 beta t

theorem independent_sum_has_gamma_characteristic_function_of_source_laws
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X Y : Omega -> ℝ} {alpha1 alpha2 beta : ℝ}
    (halpha1 : 0 < alpha1) (halpha2 : 0 < alpha2) (hbeta : 0 < beta)
    (hcf : SourceScaleGammaCharacteristicFunctionInterface)
    (hX : HasSourceScaleGammaLaw P X alpha1 beta)
    (hY : HasSourceScaleGammaLaw P Y alpha2 beta)
    (hXY : X ⟂ᵢ[P] Y) :
    HasGammaCharacteristicFunction P (fun omega => X omega + Y omega)
      (alpha1 + alpha2) beta := by
  haveI : IsProbabilityMeasure (sourceScaleGammaMeasure alpha1 beta) :=
    sourceScaleGammaMeasure_isProbabilityMeasure halpha1 hbeta
  haveI : IsFiniteMeasure P :=
    hX.isFiniteMeasure
  exact independent_sum_has_gamma_characteristic_function
    hX.aemeasurable hY.aemeasurable hXY
    (hasGammaCharacteristicFunction_of_sourceScaleGammaLaw
      halpha1 hbeta hcf hX)
    (hasGammaCharacteristicFunction_of_sourceScaleGammaLaw
      halpha2 hbeta hcf hY)

theorem sourceScaleGammaMeasure_conv_same_scale_of_charFun_interface
    {alpha1 alpha2 beta : ℝ}
    (halpha1 : 0 < alpha1) (halpha2 : 0 < alpha2) (hbeta : 0 < beta)
    (hcf : SourceScaleGammaCharacteristicFunctionInterface) :
    sourceScaleGammaMeasure alpha1 beta ∗
        sourceScaleGammaMeasure alpha2 beta =
      sourceScaleGammaMeasure (alpha1 + alpha2) beta := by
  haveI : IsProbabilityMeasure (sourceScaleGammaMeasure alpha1 beta) :=
    sourceScaleGammaMeasure_isProbabilityMeasure halpha1 hbeta
  haveI : IsProbabilityMeasure (sourceScaleGammaMeasure alpha2 beta) :=
    sourceScaleGammaMeasure_isProbabilityMeasure halpha2 hbeta
  haveI : IsProbabilityMeasure (sourceScaleGammaMeasure (alpha1 + alpha2) beta) :=
    sourceScaleGammaMeasure_isProbabilityMeasure (add_pos halpha1 halpha2) hbeta
  refine Measure.ext_of_charFun ?_
  ext t
  calc
    charFun
        (sourceScaleGammaMeasure alpha1 beta ∗
          sourceScaleGammaMeasure alpha2 beta) t
        = charFun (sourceScaleGammaMeasure alpha1 beta) t *
            charFun (sourceScaleGammaMeasure alpha2 beta) t := by
          rw [charFun_conv]
    _ = gammaCharacteristicFunctionFormula alpha1 beta t *
          gammaCharacteristicFunctionFormula alpha2 beta t := by
          rw [hcf halpha1 hbeta t, hcf halpha2 hbeta t]
    _ = gammaCharacteristicFunctionFormula (alpha1 + alpha2) beta t :=
          gammaCharacteristicFunctionFormula_mul_same_scale alpha1 alpha2 beta t
    _ = charFun (sourceScaleGammaMeasure (alpha1 + alpha2) beta) t := by
          rw [hcf (add_pos halpha1 halpha2) hbeta t]

theorem prob_9_3_of_sourceScaleGammaCharacteristicFunctionInterface
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X Y : Omega -> ℝ} {alpha1 alpha2 beta : ℝ}
    (halpha1 : 0 < alpha1) (halpha2 : 0 < alpha2) (hbeta : 0 < beta)
    (hcf : SourceScaleGammaCharacteristicFunctionInterface)
    (hX : HasSourceScaleGammaLaw P X alpha1 beta)
    (hY : HasSourceScaleGammaLaw P Y alpha2 beta)
    (hXY : X ⟂ᵢ[P] Y) :
    HasSourceScaleGammaLaw P (fun omega => X omega + Y omega)
      (alpha1 + alpha2) beta := by
  haveI : IsProbabilityMeasure (sourceScaleGammaMeasure alpha1 beta) :=
    sourceScaleGammaMeasure_isProbabilityMeasure halpha1 hbeta
  haveI : IsProbabilityMeasure (sourceScaleGammaMeasure alpha2 beta) :=
    sourceScaleGammaMeasure_isProbabilityMeasure halpha2 hbeta
  have hconv :=
    sourceScaleGammaMeasure_conv_same_scale_of_charFun_interface
      halpha1 halpha2 hbeta hcf
  have hsum :
      HasLaw (fun omega => X omega + Y omega)
        (sourceScaleGammaMeasure alpha1 beta ∗
          sourceScaleGammaMeasure alpha2 beta) P :=
    hXY.hasLaw_fun_add hX hY
  simpa [HasSourceScaleGammaLaw, hconv] using hsum

theorem sourceScaleGammaMeasure_conv_same_scale
    {alpha1 alpha2 beta : ℝ}
    (halpha1 : 0 < alpha1) (halpha2 : 0 < alpha2) (hbeta : 0 < beta) :
    sourceScaleGammaMeasure alpha1 beta ∗
        sourceScaleGammaMeasure alpha2 beta =
      sourceScaleGammaMeasure (alpha1 + alpha2) beta :=
  sourceScaleGammaMeasure_conv_same_scale_of_charFun_interface
    halpha1 halpha2 hbeta
    sourceScaleGammaCharacteristicFunctionInterface_proved
