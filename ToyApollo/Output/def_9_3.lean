/-
TASK ID: def_9_3
TYPE: Definition
SOURCE PLAN: chapter9-characteristic-functions
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped BigOperators

noncomputable def characteristicFunction (law : Measure ℝ) : ℝ → ℂ :=
  charFun law

@[simp]
theorem characteristicFunction_apply (law : Measure ℝ) (t : ℝ) :
    characteristicFunction law t = charFun law t :=
  rfl

theorem characteristicFunction_map_apply
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : AEMeasurable X P) (t : ℝ) :
    characteristicFunction (P.map X) t =
      ∫ ω, Complex.exp (Complex.I * (X ω : ℂ) * (t : ℂ)) ∂P := by
  rw [characteristicFunction, charFun_apply_real]
  rw [integral_map hX.aestronglyMeasurable.aemeasurable (by fun_prop)]
  simp [mul_comm, mul_left_comm]

theorem characteristicFunction_eq_integral_of_pdf
    (law : Measure ℝ) [IsProbabilityMeasure law] (f : ℝ → ℝ)
    (hf : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hLaw : law = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (t : ℝ) :
    characteristicFunction law t =
      ∫ x : ℝ,
        Complex.exp (Complex.I * (x : ℂ) * (t : ℂ)) * (f x : ℂ) := by
  rw [characteristicFunction, charFun_apply_real, hLaw]
  rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal (by simp)]
  apply integral_congr_ae
  filter_upwards with x
  simp [ENNReal.toReal_ofReal (hf_nonneg x), mul_comm, mul_left_comm]

theorem characteristicFunction_eq_tsum_of_pmf
    {ι : Type*} [Countable ι] (law : Measure ℝ) [IsProbabilityMeasure law]
    (x : ι → ℝ) (p : ι → ℝ) (hp_nonneg : ∀ n, 0 ≤ p n)
    (_hp_sum : HasSum p 1)
    (hLaw :
      law =
        Measure.sum
          (fun n => ENNReal.ofReal (p n) • Measure.dirac (x n)))
    (t : ℝ) :
    characteristicFunction law t =
      ∑' n : ι,
        Complex.exp (Complex.I * (x n : ℂ) * (t : ℂ)) * (p n : ℂ) := by
  rw [characteristicFunction, charFun_apply_real, hLaw]
  rw [integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top)]
  apply tsum_congr
  intro n
  simp [ENNReal.toReal_ofReal (hp_nonneg n), mul_comm, mul_left_comm]
