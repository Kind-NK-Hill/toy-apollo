/-
TASK ID: prob_14_2
TYPE: Problem
SOURCE PLAN: chapter14-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_09.prob_9_3
import ProbabilityTheory.chapter_14.thm_14_7




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal BigOperators

noncomputable section



def prob_14_2_gammaScaleCharacteristic
    (shape scale t : ℝ) : ℂ :=
  gammaCharacteristicFunctionFormula shape scale t



def prob_14_2_isGammaShapeScaleLaw
    (law : ProbabilityMeasure ℝ) (shape scale : ℝ) : Prop :=
  ∀ t : ℝ,
    thm_14_1_characteristicFunction law t =
      prob_14_2_gammaScaleCharacteristic shape scale t



def prob_14_2_iidGammaSumRepresentation
    (alpha beta : ℝ) (gammaLaws : ℕ → ProbabilityMeasure ℝ) : Prop :=
  ∀ n : ℕ, ∀ t : ℝ,
    thm_14_1_characteristicFunction (gammaLaws n) t =
      (prob_14_2_gammaScaleCharacteristic alpha beta t) ^ (n + 1)

 
theorem prob_14_2_gammaScaleCharacteristic_pow
    (alpha beta t : ℝ) :
    ∀ n : ℕ,
      prob_14_2_gammaScaleCharacteristic ((n + 1 : ℝ) * alpha) beta t =
        (prob_14_2_gammaScaleCharacteristic alpha beta t) ^ (n + 1)
  | 0 => by
      simp [prob_14_2_gammaScaleCharacteristic]
  | n + 1 => by
      have hmul := gammaCharacteristicFunctionFormula_mul_same_scale
        alpha (((n + 1 : ℕ) : ℝ) * alpha) beta t
      have hmul' :
          prob_14_2_gammaScaleCharacteristic alpha beta t *
              prob_14_2_gammaScaleCharacteristic
                (((n + 1 : ℕ) : ℝ) * alpha) beta t =
            prob_14_2_gammaScaleCharacteristic
              (alpha + ((n + 1 : ℕ) : ℝ) * alpha) beta t := by
        simpa [prob_14_2_gammaScaleCharacteristic] using hmul
      have hind := prob_14_2_gammaScaleCharacteristic_pow alpha beta t n
      have hprev :
          prob_14_2_gammaScaleCharacteristic
              (((n + 1 : ℕ) : ℝ) * alpha) beta t =
            (prob_14_2_gammaScaleCharacteristic alpha beta t) ^ (n + 1) := by
        simpa [Nat.cast_add, Nat.cast_one] using hind
      have hshape :
          (((n + 1 : ℕ) : ℝ) + 1) * alpha =
            alpha + ((n + 1 : ℕ) : ℝ) * alpha := by
        ring
      rw [hshape, ← hmul', hprev]
      ring_nf



theorem prob_14_2_iidGammaSumRepresentation_of_shapeScale
    (alpha beta : ℝ) (gammaLaws : ℕ → ProbabilityMeasure ℝ)
    (hgamma :
      ∀ n : ℕ,
        prob_14_2_isGammaShapeScaleLaw (gammaLaws n)
          ((n + 1 : ℝ) * alpha) beta) :
    prob_14_2_iidGammaSumRepresentation alpha beta gammaLaws := by
  intro n t
  rw [hgamma n t]
  exact prob_14_2_gammaScaleCharacteristic_pow alpha beta t n



theorem prob_14_2_gamma_iid_sum_representation
    (alpha beta : ℝ) (gammaLaws : ℕ → ProbabilityMeasure ℝ)
    (hgamma :
      ∀ n : ℕ,
        prob_14_2_isGammaShapeScaleLaw (gammaLaws n)
          ((n + 1 : ℝ) * alpha) beta) :
    prob_14_2_iidGammaSumRepresentation alpha beta gammaLaws :=
  prob_14_2_iidGammaSumRepresentation_of_shapeScale alpha beta gammaLaws hgamma

 
theorem prob_14_2_measurable_gammaPDF (alpha rate : ℝ) :
    Measurable (ProbabilityTheory.gammaPDF alpha rate) := by
  change Measurable (fun x : ℝ =>
    ENNReal.ofReal (ProbabilityTheory.gammaPDFReal alpha rate x))
  exact ENNReal.measurable_ofReal.comp
    (ProbabilityTheory.measurable_gammaPDFReal alpha rate)

 
theorem prob_14_2_gammaPDF_lt_top_ae (alpha rate : ℝ) :
    ∀ᵐ x ∂(volume : Measure ℝ), ProbabilityTheory.gammaPDF alpha rate x < ⊤ := by
  filter_upwards with x
  simp [ProbabilityTheory.gammaPDF]



theorem prob_14_2_toReal_gammaPDF
    {alpha rate x : ℝ} (halpha : 0 < alpha) (hrate : 0 < rate) :
    (ProbabilityTheory.gammaPDF alpha rate x).toReal =
      ProbabilityTheory.gammaPDFReal alpha rate x := by
  simp [ProbabilityTheory.gammaPDF,
    ENNReal.toReal_ofReal,
    ProbabilityTheory.gammaPDFReal_nonneg halpha hrate x]

 
theorem prob_14_2_integral_id_mul_gammaPDFReal
    {alpha rate : ℝ} (halpha : 0 < alpha) (hrate : 0 < rate) :
    (∫ x : ℝ, x * ProbabilityTheory.gammaPDFReal alpha rate x) =
      alpha / rate := by
  calc
    (∫ x : ℝ, x * ProbabilityTheory.gammaPDFReal alpha rate x) =
        ∫ x : ℝ in Set.Ioi 0,
          x * ProbabilityTheory.gammaPDFReal alpha rate x := by
      rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      by_cases hx : 0 < x
      · simp [Set.indicator, hx]
      · have hxle : x ≤ 0 := le_of_not_gt hx
        rcases lt_or_eq_of_le hxle with hxneg | rfl
        · have hxnot : ¬ 0 ≤ x := not_le.mpr hxneg
          simp [Set.indicator, hx, ProbabilityTheory.gammaPDFReal, hxnot]
        · simp [Set.indicator]
    _ = ∫ x : ℝ in Set.Ioi 0,
          (rate ^ alpha / Real.Gamma alpha) *
            (x ^ ((alpha + 1) - 1) * Real.exp (-(rate * x))) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
      intro x hx
      have hxpos : 0 < x := hx
      have hpow :
          x * x ^ (alpha - 1) = x ^ ((alpha + 1) - 1) := by
        calc
          x * x ^ (alpha - 1) =
              x ^ (1 : ℝ) * x ^ (alpha - 1) := by rw [Real.rpow_one]
          _ = x ^ ((1 : ℝ) + (alpha - 1)) :=
            (Real.rpow_add hxpos 1 (alpha - 1)).symm
          _ = x ^ ((alpha + 1) - 1) := by
            congr 1
            ring
      simp only [ProbabilityTheory.gammaPDFReal, if_pos hxpos.le]
      calc
        x * (rate ^ alpha / Real.Gamma alpha * x ^ (alpha - 1) *
              Real.exp (-(rate * x))) =
            (rate ^ alpha / Real.Gamma alpha) *
              ((x * x ^ (alpha - 1)) * Real.exp (-(rate * x))) := by ring
        _ = (rate ^ alpha / Real.Gamma alpha) *
              (x ^ ((alpha + 1) - 1) * Real.exp (-(rate * x))) := by
            rw [hpow]
    _ = (rate ^ alpha / Real.Gamma alpha) *
          ∫ x : ℝ in Set.Ioi 0,
            x ^ ((alpha + 1) - 1) * Real.exp (-(rate * x)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = (rate ^ alpha / Real.Gamma alpha) *
          ((1 / rate) ^ (alpha + 1) * Real.Gamma (alpha + 1)) := by
      rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (add_pos halpha zero_lt_one) hrate]
    _ = alpha / rate := by
      have hGamma : Real.Gamma alpha ≠ 0 :=
        (Real.Gamma_pos_of_pos halpha).ne'
      have hratePow : rate ^ alpha ≠ 0 :=
        (Real.rpow_pos_of_pos hrate alpha).ne'
      have hInvRate : 0 < (1 / rate : ℝ) := one_div_pos.mpr hrate
      rw [Real.Gamma_add_one halpha.ne', Real.rpow_add hInvRate,
        Real.rpow_one, one_div, Real.inv_rpow hrate.le]
      field_simp [hGamma, hratePow, hrate.ne']
      <;> ring

 
theorem prob_14_2_integral_sq_mul_gammaPDFReal
    {alpha rate : ℝ} (halpha : 0 < alpha) (hrate : 0 < rate) :
    (∫ x : ℝ, x ^ 2 * ProbabilityTheory.gammaPDFReal alpha rate x) =
      alpha * (alpha + 1) / rate ^ 2 := by
  calc
    (∫ x : ℝ, x ^ 2 * ProbabilityTheory.gammaPDFReal alpha rate x) =
        ∫ x : ℝ in Set.Ioi 0,
          x ^ 2 * ProbabilityTheory.gammaPDFReal alpha rate x := by
      rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      by_cases hx : 0 < x
      · simp [Set.indicator, hx]
      · have hxle : x ≤ 0 := le_of_not_gt hx
        rcases lt_or_eq_of_le hxle with hxneg | rfl
        · have hxnot : ¬ 0 ≤ x := not_le.mpr hxneg
          simp [Set.indicator, hx, ProbabilityTheory.gammaPDFReal, hxnot]
        · simp [Set.indicator]
    _ = ∫ x : ℝ in Set.Ioi 0,
          (rate ^ alpha / Real.Gamma alpha) *
            (x ^ ((alpha + 2) - 1) * Real.exp (-(rate * x))) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
      intro x hx
      have hxpos : 0 < x := hx
      have hpow :
          x ^ 2 * x ^ (alpha - 1) = x ^ ((alpha + 2) - 1) := by
        calc
          x ^ 2 * x ^ (alpha - 1) =
              x ^ (2 : ℝ) * x ^ (alpha - 1) := by rw [Real.rpow_two]
          _ = x ^ ((2 : ℝ) + (alpha - 1)) :=
            (Real.rpow_add hxpos 2 (alpha - 1)).symm
          _ = x ^ ((alpha + 2) - 1) := by
            congr 1
            ring
      simp only [ProbabilityTheory.gammaPDFReal, if_pos hxpos.le]
      calc
        x ^ 2 * (rate ^ alpha / Real.Gamma alpha * x ^ (alpha - 1) *
              Real.exp (-(rate * x))) =
            (rate ^ alpha / Real.Gamma alpha) *
              ((x ^ 2 * x ^ (alpha - 1)) * Real.exp (-(rate * x))) := by ring
        _ = (rate ^ alpha / Real.Gamma alpha) *
              (x ^ ((alpha + 2) - 1) * Real.exp (-(rate * x))) := by
            rw [hpow]
    _ = (rate ^ alpha / Real.Gamma alpha) *
          ∫ x : ℝ in Set.Ioi 0,
            x ^ ((alpha + 2) - 1) * Real.exp (-(rate * x)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = (rate ^ alpha / Real.Gamma alpha) *
          ((1 / rate) ^ (alpha + 2) * Real.Gamma (alpha + 2)) := by
      rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hrate]
    _ = alpha * (alpha + 1) / rate ^ 2 := by
      have hGamma : Real.Gamma alpha ≠ 0 :=
        (Real.Gamma_pos_of_pos halpha).ne'
      have hratePow : rate ^ alpha ≠ 0 :=
        (Real.rpow_pos_of_pos hrate alpha).ne'
      have hInvRate : 0 < (1 / rate : ℝ) := one_div_pos.mpr hrate
      have halphaOne : alpha + 1 ≠ 0 := by linarith
      rw [show alpha + 2 = (alpha + 1) + 1 by ring,
        Real.Gamma_add_one halphaOne, Real.Gamma_add_one halpha.ne',
        Real.rpow_add hInvRate, Real.rpow_add hInvRate,
        Real.rpow_one, one_div, Real.inv_rpow hrate.le]
      field_simp [hGamma, hratePow, hrate.ne']
      <;> ring



theorem prob_14_2_integrable_id_gammaMeasure
    {alpha rate : ℝ} (halpha : 0 < alpha) (hrate : 0 < rate) :
    Integrable (fun x : ℝ => x) (ProbabilityTheory.gammaMeasure alpha rate) := by
  change Integrable (fun x : ℝ => x)
    ((volume : Measure ℝ).withDensity (ProbabilityTheory.gammaPDF alpha rate))
  rw [MeasureTheory.integrable_withDensity_iff_integrable_smul'
    (prob_14_2_measurable_gammaPDF alpha rate)
    (prob_14_2_gammaPDF_lt_top_ae alpha rate)]
  have hLebesgue :
      Integrable
        (fun x : ℝ => x * ProbabilityTheory.gammaPDFReal alpha rate x)
        (volume : Measure ℝ) := by
    apply Integrable.of_integral_ne_zero
    rw [prob_14_2_integral_id_mul_gammaPDFReal halpha hrate]
    exact (div_pos halpha hrate).ne'
  simpa [prob_14_2_toReal_gammaPDF halpha hrate, smul_eq_mul, mul_comm] using
    hLebesgue



theorem prob_14_2_integrable_sq_gammaMeasure
    {alpha rate : ℝ} (halpha : 0 < alpha) (hrate : 0 < rate) :
    Integrable (fun x : ℝ => x ^ 2)
      (ProbabilityTheory.gammaMeasure alpha rate) := by
  change Integrable (fun x : ℝ => x ^ 2)
    ((volume : Measure ℝ).withDensity (ProbabilityTheory.gammaPDF alpha rate))
  rw [MeasureTheory.integrable_withDensity_iff_integrable_smul'
    (prob_14_2_measurable_gammaPDF alpha rate)
    (prob_14_2_gammaPDF_lt_top_ae alpha rate)]
  have hLebesgue :
      Integrable
        (fun x : ℝ => x ^ 2 * ProbabilityTheory.gammaPDFReal alpha rate x)
        (volume : Measure ℝ) := by
    apply Integrable.of_integral_ne_zero
    rw [prob_14_2_integral_sq_mul_gammaPDFReal halpha hrate]
    positivity
  simpa [prob_14_2_toReal_gammaPDF halpha hrate, smul_eq_mul, mul_comm] using
    hLebesgue

 
theorem prob_14_2_integral_id_gammaMeasure
    {alpha rate : ℝ} (halpha : 0 < alpha) (hrate : 0 < rate) :
    (∫ x : ℝ, x ∂ProbabilityTheory.gammaMeasure alpha rate) = alpha / rate := by
  calc
    (∫ x : ℝ, x ∂ProbabilityTheory.gammaMeasure alpha rate) =
        ∫ x : ℝ, (ProbabilityTheory.gammaPDF alpha rate x).toReal * x := by
      change (∫ x : ℝ, x ∂(volume : Measure ℝ).withDensity
        (ProbabilityTheory.gammaPDF alpha rate)) = _
      simpa [smul_eq_mul] using
        (integral_withDensity_eq_integral_toReal_smul
          (μ := (volume : Measure ℝ))
          (f := ProbabilityTheory.gammaPDF alpha rate)
          (g := fun x : ℝ => x)
          (prob_14_2_measurable_gammaPDF alpha rate)
          (prob_14_2_gammaPDF_lt_top_ae alpha rate))
    _ = ∫ x : ℝ, x * ProbabilityTheory.gammaPDFReal alpha rate x := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [prob_14_2_toReal_gammaPDF halpha hrate]
      ring
    _ = alpha / rate :=
      prob_14_2_integral_id_mul_gammaPDFReal halpha hrate

 
theorem prob_14_2_integral_sq_gammaMeasure
    {alpha rate : ℝ} (halpha : 0 < alpha) (hrate : 0 < rate) :
    (∫ x : ℝ, x ^ 2 ∂ProbabilityTheory.gammaMeasure alpha rate) =
      alpha * (alpha + 1) / rate ^ 2 := by
  calc
    (∫ x : ℝ, x ^ 2 ∂ProbabilityTheory.gammaMeasure alpha rate) =
        ∫ x : ℝ, (ProbabilityTheory.gammaPDF alpha rate x).toReal * x ^ 2 := by
      change (∫ x : ℝ, x ^ 2 ∂(volume : Measure ℝ).withDensity
        (ProbabilityTheory.gammaPDF alpha rate)) = _
      simpa [smul_eq_mul] using
        (integral_withDensity_eq_integral_toReal_smul
          (μ := (volume : Measure ℝ))
          (f := ProbabilityTheory.gammaPDF alpha rate)
          (g := fun x : ℝ => x ^ 2)
          (prob_14_2_measurable_gammaPDF alpha rate)
          (prob_14_2_gammaPDF_lt_top_ae alpha rate))
    _ = ∫ x : ℝ, x ^ 2 * ProbabilityTheory.gammaPDFReal alpha rate x := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [prob_14_2_toReal_gammaPDF halpha hrate]
      ring
    _ = alpha * (alpha + 1) / rate ^ 2 :=
      prob_14_2_integral_sq_mul_gammaPDFReal halpha hrate

 
theorem prob_14_2_integrable_id_sourceScaleGammaMeasure
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    Integrable (fun x : ℝ => x) (sourceScaleGammaMeasure alpha beta) := by
  simpa [sourceScaleGammaMeasure] using
    prob_14_2_integrable_id_gammaMeasure halpha (inv_pos.mpr hbeta)



theorem prob_14_2_integrable_sq_sourceScaleGammaMeasure
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    Integrable (fun x : ℝ => x ^ 2) (sourceScaleGammaMeasure alpha beta) := by
  simpa [sourceScaleGammaMeasure] using
    prob_14_2_integrable_sq_gammaMeasure halpha (inv_pos.mpr hbeta)

 
theorem prob_14_2_sourceScaleGammaMeasure_mean
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    (∫ x : ℝ, x ∂sourceScaleGammaMeasure alpha beta) = alpha * beta := by
  calc
    (∫ x : ℝ, x ∂sourceScaleGammaMeasure alpha beta) = alpha / beta⁻¹ := by
      simpa [sourceScaleGammaMeasure] using
        prob_14_2_integral_id_gammaMeasure halpha (inv_pos.mpr hbeta)
    _ = alpha * beta := by field_simp [hbeta.ne']



theorem prob_14_2_sourceScaleGammaMeasure_secondMoment
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    (∫ x : ℝ, x ^ 2 ∂sourceScaleGammaMeasure alpha beta) =
      alpha * (alpha + 1) * beta ^ 2 := by
  calc
    (∫ x : ℝ, x ^ 2 ∂sourceScaleGammaMeasure alpha beta) =
        alpha * (alpha + 1) / (beta⁻¹) ^ 2 := by
      simpa [sourceScaleGammaMeasure] using
        prob_14_2_integral_sq_gammaMeasure halpha (inv_pos.mpr hbeta)
    _ = alpha * (alpha + 1) * beta ^ 2 := by
      field_simp [hbeta.ne']
      <;> ring



theorem prob_14_2_sourceScaleGammaMeasure_variance
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    ProbabilityTheory.variance (fun x : ℝ => x)
        (sourceScaleGammaMeasure alpha beta) =
      (beta * Real.sqrt alpha) ^ 2 := by
  letI : IsProbabilityMeasure (sourceScaleGammaMeasure alpha beta) :=
    sourceScaleGammaMeasure_isProbabilityMeasure halpha hbeta
  have hMemLp :
      MemLp (fun x : ℝ => x) 2 (sourceScaleGammaMeasure alpha beta) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2
      (prob_14_2_integrable_sq_sourceScaleGammaMeasure halpha hbeta)
  calc
    ProbabilityTheory.variance (fun x : ℝ => x)
        (sourceScaleGammaMeasure alpha beta) =
        (∫ x : ℝ, x ^ 2 ∂sourceScaleGammaMeasure alpha beta) -
          (∫ x : ℝ, x ∂sourceScaleGammaMeasure alpha beta) ^ 2 := by
      simpa [Pi.pow_apply] using
        (ProbabilityTheory.variance_eq_sub hMemLp)
    _ = alpha * beta ^ 2 := by
      rw [prob_14_2_sourceScaleGammaMeasure_secondMoment halpha hbeta,
        prob_14_2_sourceScaleGammaMeasure_mean halpha hbeta]
      ring
    _ = (beta * Real.sqrt alpha) ^ 2 := by
      calc
        alpha * beta ^ 2 = beta ^ 2 * (Real.sqrt alpha) ^ 2 := by
          rw [Real.sq_sqrt halpha.le]
          ring
        _ = (beta * Real.sqrt alpha) ^ 2 := by ring



theorem prob_14_2_integrable_of_hasSourceScaleGammaLaw
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : Omega → ℝ} {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hX : HasSourceScaleGammaLaw P X alpha beta) :
    Integrable X P := by
  have hLaw : HasLaw X (sourceScaleGammaMeasure alpha beta) P := hX
  have hMap :
      Integrable (fun x : ℝ => x) (Measure.map X P) := by
    rw [hLaw.map_eq]
    exact prob_14_2_integrable_id_sourceScaleGammaMeasure halpha hbeta
  simpa [Function.comp_def] using
    (MeasureTheory.integrable_map_measure
      (g := fun x : ℝ => x) (by fun_prop) hLaw.aemeasurable).1 hMap



theorem prob_14_2_integrable_sq_of_hasSourceScaleGammaLaw
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : Omega → ℝ} {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hX : HasSourceScaleGammaLaw P X alpha beta) :
    Integrable (fun omega => X omega ^ 2) P := by
  have hLaw : HasLaw X (sourceScaleGammaMeasure alpha beta) P := hX
  have hMap :
      Integrable (fun x : ℝ => x ^ 2) (Measure.map X P) := by
    rw [hLaw.map_eq]
    exact prob_14_2_integrable_sq_sourceScaleGammaMeasure halpha hbeta
  simpa [Function.comp_def] using
    (MeasureTheory.integrable_map_measure
      (g := fun x : ℝ => x ^ 2) (by fun_prop) hLaw.aemeasurable).1 hMap

 
theorem prob_14_2_mean_of_hasSourceScaleGammaLaw
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : Omega → ℝ} {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hX : HasSourceScaleGammaLaw P X alpha beta) :
    P[X] = alpha * beta := by
  have hLaw : HasLaw X (sourceScaleGammaMeasure alpha beta) P := hX
  calc
    P[X] = ∫ x : ℝ, x ∂sourceScaleGammaMeasure alpha beta := hLaw.integral_eq
    _ = alpha * beta :=
      prob_14_2_sourceScaleGammaMeasure_mean halpha hbeta

 
theorem prob_14_2_variance_of_hasSourceScaleGammaLaw
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : Omega → ℝ} {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hX : HasSourceScaleGammaLaw P X alpha beta) :
    ProbabilityTheory.variance X P = (beta * Real.sqrt alpha) ^ 2 := by
  have hLaw : HasLaw X (sourceScaleGammaMeasure alpha beta) P := hX
  calc
    ProbabilityTheory.variance X P =
        ProbabilityTheory.variance id (sourceScaleGammaMeasure alpha beta) :=
      hLaw.variance_eq
    _ = (beta * Real.sqrt alpha) ^ 2 := by
      change ProbabilityTheory.variance (fun x : ℝ => x)
          (sourceScaleGammaMeasure alpha beta) = _
      exact prob_14_2_sourceScaleGammaMeasure_variance halpha hbeta

 
def prob_14_2_partialSum
    {Omega : Type*} (X : ℕ → Omega → ℝ) (n : ℕ) : Omega → ℝ :=
  fun omega => ∑ k : Fin (n + 1), X k.val omega

theorem prob_14_2_partialSum_aemeasurable
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    (X : ℕ → Omega → ℝ) (hX : ∀ k, AEMeasurable (X k) P) (n : ℕ) :
    AEMeasurable (prob_14_2_partialSum X n) P := by
  unfold prob_14_2_partialSum
  fun_prop

theorem prob_14_2_partialSum_eq_range
    {Omega : Type*} (X : ℕ → Omega → ℝ) (n : ℕ) :
    prob_14_2_partialSum X n =
      ∑ k ∈ Finset.range (n + 1), X k := by
  funext omega
  unfold prob_14_2_partialSum
  simpa using Fin.sum_univ_eq_sum_range (fun k => X k omega) (n + 1)

theorem prob_14_2_partialSum_succ
    {Omega : Type*} (X : ℕ → Omega → ℝ) (n : ℕ) :
    prob_14_2_partialSum X (n + 1) =
      fun omega => prob_14_2_partialSum X n omega + X (n + 1) omega := by
  rw [prob_14_2_partialSum_eq_range X (n + 1),
    prob_14_2_partialSum_eq_range X n]
  funext omega
  simp [Finset.sum_range_succ]

theorem prob_14_2_partialSum_indep_next
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : ℕ → Omega → ℝ}
    (hX : ∀ k, AEMeasurable (X k) P)
    (hIndep : ProbabilityTheory.iIndepFun X P) (n : ℕ) :
    prob_14_2_partialSum X n ⟂ᵢ[P] X (n + 1) := by
  have hRange :
      (∑ k ∈ Finset.range (n + 1), X k) ⟂ᵢ[P] X (n + 1) := by
    simpa using hIndep.indepFun_finsetSum_of_notMem₀ hX
      (s := Finset.range (n + 1)) (i := n + 1) (by simp)
  exact hRange.congr
    (by rw [prob_14_2_partialSum_eq_range X n]) Filter.EventuallyEq.rfl



theorem prob_14_2_partialSum_hasSourceScaleGammaLaw
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : ℕ → Omega → ℝ} {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hGamma : ∀ k, HasSourceScaleGammaLaw P (X k) alpha beta)
    (hIndep : ProbabilityTheory.iIndepFun X P) :
    ∀ n : ℕ,
      HasSourceScaleGammaLaw P (prob_14_2_partialSum X n)
        ((n + 1 : ℝ) * alpha) beta := by
  have hMeas : ∀ k, AEMeasurable (X k) P := fun k => (hGamma k).aemeasurable
  intro n
  induction n with
  | zero =>
      have hsum : prob_14_2_partialSum X 0 = X 0 := by
        funext omega
        simp [prob_14_2_partialSum]
      simpa [hsum] using hGamma 0
  | succ n ih =>
      have hInd : prob_14_2_partialSum X n ⟂ᵢ[P] X (n + 1) :=
        prob_14_2_partialSum_indep_next hMeas hIndep n
      have ih' :
          HasSourceScaleGammaLaw P (prob_14_2_partialSum X n)
            (((n + 1 : ℕ) : ℝ) * alpha) beta := by
        simpa [Nat.cast_add, Nat.cast_one] using ih
      have hAdd :
          HasSourceScaleGammaLaw P
            (fun omega => prob_14_2_partialSum X n omega + X (n + 1) omega)
            (((n + 1 : ℕ) : ℝ) * alpha + alpha) beta :=
        prob_9_3 (mul_pos (by positivity) halpha) halpha hbeta ih'
          (hGamma (n + 1)) hInd
      rw [prob_14_2_partialSum_succ]
      simpa [Nat.cast_add, Nat.cast_one, add_mul] using hAdd

 
def prob_14_2_gammaSumLaws
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ) (hX : ∀ k, AEMeasurable (X k) P) :
    ℕ → ProbabilityMeasure ℝ :=
  fun n => thm_14_7_law P (prob_14_2_partialSum X n)
    (prob_14_2_partialSum_aemeasurable X hX n)



def prob_14_2_standardizedGammaSum
    {Omega : Type*} (X : ℕ → Omega → ℝ)
    (alpha beta : ℝ) (n : ℕ) : Omega → ℝ :=
  fun omega =>
    (prob_14_2_partialSum X n omega -
        ((n : ℝ) + 1) * alpha * beta) /
      (beta * Real.sqrt (((n : ℝ) + 1) * alpha))

theorem prob_14_2_standardizedGammaSum_aemeasurable
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    (X : ℕ → Omega → ℝ) (alpha beta : ℝ)
    (hX : ∀ k, AEMeasurable (X k) P) (n : ℕ) :
    AEMeasurable (prob_14_2_standardizedGammaSum X alpha beta n) P := by
  unfold prob_14_2_standardizedGammaSum
  exact ((prob_14_2_partialSum_aemeasurable X hX n).sub_const _).div_const _

 
def prob_14_2_standardizedGammaSumLaws
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ) (alpha beta : ℝ)
    (hX : ∀ k, AEMeasurable (X k) P) :
    ℕ → ProbabilityMeasure ℝ :=
  fun n => thm_14_7_law P
    (prob_14_2_standardizedGammaSum X alpha beta n)
    (prob_14_2_standardizedGammaSum_aemeasurable X alpha beta hX n)



theorem prob_14_2_standardizedGammaSum_eq_thm_14_7
    {Omega : Type*} (X : ℕ → Omega → ℝ)
    (alpha beta : ℝ) (n : ℕ) :
    prob_14_2_standardizedGammaSum X alpha beta n =
      thm_14_7_standardizedSum X (alpha * beta)
        (beta * Real.sqrt alpha) n := by
  funext omega
  unfold prob_14_2_standardizedGammaSum thm_14_7_standardizedSum
    prob_14_2_partialSum
  rw [Real.sqrt_mul (by positivity : 0 ≤ (n : ℝ) + 1)]
  congr 1 <;> ring



theorem prob_14_2_standardizedGammaSumLaws_eq_thm_14_7
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ) (alpha beta : ℝ)
    (hX : ∀ k, AEMeasurable (X k) P) :
    prob_14_2_standardizedGammaSumLaws P X alpha beta hX =
      thm_14_7_standardizedSumLaws P X (alpha * beta)
        (beta * Real.sqrt alpha) hX := by
  funext n
  apply Subtype.ext
  change Measure.map (prob_14_2_standardizedGammaSum X alpha beta n) P =
    Measure.map
      (thm_14_7_standardizedSum X (alpha * beta)
        (beta * Real.sqrt alpha) n) P
  rw [prob_14_2_standardizedGammaSum_eq_thm_14_7]



theorem prob_14_2
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℕ → Omega → ℝ) {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hGamma : ∀ k, HasSourceScaleGammaLaw P (X k) alpha beta)
    (hIndep : ProbabilityTheory.iIndepFun X P) :
    (∀ n : ℕ,
        HasSourceScaleGammaLaw P (prob_14_2_partialSum X n)
          ((n + 1 : ℝ) * alpha) beta) ∧
      Tendsto (prob_14_2_standardizedGammaSumLaws P X alpha beta
          (fun k => (hGamma k).aemeasurable))
        atTop (𝓝 thm_14_7_standardNormalLaw) := by
  have hMeas : ∀ k, AEMeasurable (X k) P :=
    fun k => (hGamma k).aemeasurable
  have hIdent : ∀ k, IdentDistrib (X k) (X 0) P P :=
    fun k => (hGamma k).identDistrib (hGamma 0)
  have hIntegrable : Integrable (X 0) P :=
    prob_14_2_integrable_of_hasSourceScaleGammaLaw halpha hbeta (hGamma 0)
  have hSquareIntegrable : Integrable (fun omega => X 0 omega ^ 2) P :=
    prob_14_2_integrable_sq_of_hasSourceScaleGammaLaw halpha hbeta (hGamma 0)
  have hMean : P[X 0] = alpha * beta :=
    prob_14_2_mean_of_hasSourceScaleGammaLaw halpha hbeta (hGamma 0)
  have hVariance :
      ProbabilityTheory.variance (X 0) P =
        (beta * Real.sqrt alpha) ^ 2 :=
    prob_14_2_variance_of_hasSourceScaleGammaLaw halpha hbeta (hGamma 0)
  have hsigma : 0 < beta * Real.sqrt alpha :=
    mul_pos hbeta (Real.sqrt_pos.2 halpha)
  refine ⟨prob_14_2_partialSum_hasSourceScaleGammaLaw
      halpha hbeta hGamma hIndep, ?_⟩
  rw [prob_14_2_standardizedGammaSumLaws_eq_thm_14_7]
  exact thm_14_7 P X (alpha * beta) (beta * Real.sqrt alpha)
    hMeas hIndep hIdent hIntegrable hSquareIntegrable hMean hVariance hsigma
