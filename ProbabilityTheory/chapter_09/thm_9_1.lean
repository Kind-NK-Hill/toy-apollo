/-
TASK ID: thm_9_1
TYPE: Theorem_Statement
SOURCE PLAN: chapter9-moments-mgf
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_09.def_9_1




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory Set

noncomputable abbrev densityMomentFormula (ρ : ℝ → NNReal) (r : ℕ) : ℝ :=
  ∫ x, x ^ r * (ρ x : ℝ)

noncomputable abbrev densityCentralMomentFormula
    (ρ : ℝ → NNReal) (mean : ℝ) (r : ℕ) : ℝ :=
  ∫ x, (x - mean) ^ r * (ρ x : ℝ)



theorem StieltjesFunction.change_of_variables_of_map_eq_measure
    (F : StieltjesFunction ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X : Ω → ℝ} {g : ℝ → ℝ}
    (hX : Measurable X) (hg : Measurable g)
    (hMap : Measure.map X P = F.measure) :
    ∫ ω, g (X ω) ∂P = ∫ x, g x ∂F.measure := by
  calc
    ∫ ω, g (X ω) ∂P = ∫ x, g x ∂Measure.map X P := by
      exact
        (MeasureTheory.integral_map
          (μ := P) (φ := X) (f := g) hX.aemeasurable hg.aestronglyMeasurable).symm
    _ = ∫ x, g x ∂F.measure := by rw [hMap]



theorem StieltjesFunction.measurable_nnreal_of_hasDerivAt
    (F : StieltjesFunction ℝ) (ρ : ℝ → NNReal)
    (hderiv : ∀ x, HasDerivAt (fun t : ℝ => (F t : ℝ)) (ρ x : ℝ) x) :
    Measurable ρ := by
  rw [← measurable_coe_nnreal_real_iff]
  have hfun :
      (fun x : ℝ => (ρ x : ℝ)) = deriv (fun t : ℝ => (F t : ℝ)) := by
    funext x
    exact (hderiv x).deriv.symm
  rw [hfun]
  exact measurable_deriv _



theorem StieltjesFunction.measure_eq_withDensity_of_hasDerivAt
    (F : StieltjesFunction ℝ) (ρ : ℝ → NNReal)
    (hderiv : ∀ x, HasDerivAt (fun t : ℝ => (F t : ℝ)) (ρ x : ℝ) x) :
    F.measure = volume.withDensity (fun x => (ρ x : ENNReal)) := by
  refine
    Measure.ext_of_Ioc F.measure
      (volume.withDensity (fun x => (ρ x : ENNReal))) ?_
  intro a b hab
  rw [F.measure_Ioc, withDensity_apply _ measurableSet_Ioc]
  have hInterval :
      IntervalIntegrable (fun x : ℝ => (ρ x : ℝ)) volume a b := by
    exact
      intervalIntegral.intervalIntegrable_deriv_of_nonneg
        (g := fun t : ℝ => (F t : ℝ))
        (g' := fun x : ℝ => (ρ x : ℝ))
        (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
        (fun x _ => hderiv x)
        (fun x _ => NNReal.coe_nonneg (ρ x))
  have hFTC :
      (∫ x in a..b, (ρ x : ℝ)) = (F b : ℝ) - (F a : ℝ) := by
    exact
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun t : ℝ => (F t : ℝ))
        (f' := fun x : ℝ => (ρ x : ℝ))
        (fun x _ => hderiv x) hInterval
  have hIoc :
      IntegrableOn (fun x : ℝ => (ρ x : ℝ)) (Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).1 hInterval
  rw [← hFTC, intervalIntegral.integral_of_le hab.le]
  simpa only [ENNReal.ofReal_coe_nnreal] using
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIoc
      (Filter.Eventually.of_forall fun x => NNReal.coe_nonneg (ρ x)))

theorem thm_9_1 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (ρ : ℝ → NNReal) (r : PositiveOrder)
    (hX : FiniteAbsMoment μ X r.1)
    (hCDF : ∀ x,
      HasDerivAt
        (fun t : ℝ => (cdf (Measure.map X μ) t : ℝ))
        (ρ x : ℝ) x) :
    rthMoment μ X r hX = densityMomentFormula ρ r.1 ∧
      rthCentralMoment μ X r hX =
        densityCentralMomentFormula ρ
          (rthMoment μ X positiveOrderOne (hX.mono r.property)) r.1 := by
  letI : IsProbabilityMeasure (Measure.map X μ) :=
    Measure.isProbabilityMeasure_map hX.1.aemeasurable
  let F : StieltjesFunction ℝ := cdf (Measure.map X μ)
  have hFDeriv :
      ∀ x, HasDerivAt (fun t : ℝ => (F t : ℝ)) (ρ x : ℝ) x := by
    simpa [F] using hCDF
  have hρ : Measurable ρ :=
    F.measurable_nnreal_of_hasDerivAt ρ hFDeriv
  have hFDensity :
      F.measure = volume.withDensity (fun x => (ρ x : ENNReal)) :=
    F.measure_eq_withDensity_of_hasDerivAt ρ hFDeriv
  have hStieltjes : Measure.map X μ = F.measure := by
    simpa [F] using (ProbabilityTheory.measure_cdf (Measure.map X μ)).symm
  have hMap :
      Measure.map X μ = volume.withDensity (fun x => (ρ x : ENNReal)) :=
    hStieltjes.trans hFDensity
  constructor
  · unfold rthMoment generalMoment densityMomentFormula moment
    change (∫ x, X x ^ r.1 ∂μ) = ∫ x, x ^ r.1 * (ρ x : ℝ)
    have hpow : Measurable (fun y : ℝ => y ^ r.1) :=
      measurable_id.pow_const r.1
    calc
      ∫ x, X x ^ r.1 ∂μ = ∫ y, y ^ r.1 ∂F.measure := by
        exact
          F.change_of_variables_of_map_eq_measure
            μ hX.1 hpow hStieltjes
      _ =
          ∫ y, y ^ r.1
            ∂(volume.withDensity (fun x => (ρ x : ENNReal))) := by
        rw [← hStieltjes, hMap]
      _ = ∫ x, x ^ r.1 * (ρ x : ℝ) := by
        rw [integral_withDensity_eq_integral_smul hρ]
        simp [NNReal.smul_def, mul_comm]
  · unfold rthCentralMoment densityCentralMomentFormula centralMoment
    have hmean :
        rthMoment μ X positiveOrderOne (hX.mono r.property) =
          ∫ x, X x ∂μ := by
      unfold rthMoment generalMoment positiveOrderOne moment
      simp
    rw [hmean]
    change
      (∫ x, (X x - ∫ x, X x ∂μ) ^ r.1 ∂μ) =
        ∫ x, (x - ∫ x, X x ∂μ) ^ r.1 * (ρ x : ℝ)
    have hCenteredPow :
        Measurable (fun y : ℝ => (y - ∫ x, X x ∂μ) ^ r.1) :=
      (measurable_id.sub measurable_const).pow_const r.1
    calc
      ∫ x, (X x - ∫ x, X x ∂μ) ^ r.1 ∂μ =
          ∫ y, (y - ∫ x, X x ∂μ) ^ r.1 ∂F.measure := by
        exact
          F.change_of_variables_of_map_eq_measure
            μ hX.1 hCenteredPow hStieltjes
      _ =
          ∫ y, (y - ∫ x, X x ∂μ) ^ r.1
            ∂(volume.withDensity (fun x => (ρ x : ENNReal))) := by
        rw [← hStieltjes, hMap]
      _ = ∫ x, (x - ∫ x, X x ∂μ) ^ r.1 * (ρ x : ℝ) := by
        rw [integral_withDensity_eq_integral_smul hρ]
        simp [NNReal.smul_def, mul_comm]
