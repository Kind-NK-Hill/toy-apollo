/-
TASK ID: prob_9_10
TYPE: Problem
SOURCE PLAN: chapter9-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_9_3
import ToyApollo.Output.thm_9_7
import ToyApollo.Output.def_9_1

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory Complex ENNReal
open scoped Nat ENNReal

noncomputable def chiSquareCharacteristicFunction (k : ℝ) (t : ℝ) : ℂ :=
  ((1 : ℂ) - 2 * Complex.I * (t : ℂ)) ^ (-(k : ℂ) / 2)

noncomputable def chiSquareCharacteristicDerivative (k : ℝ) (t : ℝ) : ℂ :=
  (-(k : ℂ) / 2) *
    (((1 : ℂ) - 2 * Complex.I * (t : ℂ)) ^ (-(k : ℂ) / 2 - 1)) *
      (-2 * Complex.I)

lemma chiSquare_base_hasDerivAt_complex (z : ℂ) :
    HasDerivAt (fun w : ℂ => (1 : ℂ) - 2 * Complex.I * w) (-2 * Complex.I) z := by
  have hterm : HasDerivAt (fun w : ℂ => (2 * Complex.I) * w) (2 * Complex.I) z := by
    simpa using (hasDerivAt_id z).const_mul (2 * Complex.I)
  have hconst : HasDerivAt (fun _ : ℂ => (1 : ℂ)) (0 : ℂ) z := hasDerivAt_const z 1
  convert hconst.sub hterm using 1
  · ring

lemma chiSquare_base_mem_slit_ofReal (t : ℝ) :
    ((1 : ℂ) - 2 * Complex.I * (t : ℂ)) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  simp

lemma chiSquareCharacteristicFunction_hasDerivAt (k t : ℝ) :
    HasDerivAt (chiSquareCharacteristicFunction k)
      (chiSquareCharacteristicDerivative k t) t := by
  unfold chiSquareCharacteristicFunction chiSquareCharacteristicDerivative
  have hcomplex : HasDerivAt
      (fun z : ℂ => ((1 : ℂ) - 2 * Complex.I * z) ^ (-(k : ℂ) / 2))
      ((-(k : ℂ) / 2) *
        (((1 : ℂ) - 2 * Complex.I * (t : ℂ)) ^ (-(k : ℂ) / 2 - 1)) *
          (-2 * Complex.I)) (t : ℂ) := by
    exact (chiSquare_base_hasDerivAt_complex (t : ℂ)).cpow_const
      (chiSquare_base_mem_slit_ofReal t)
  simpa using hcomplex.comp_ofReal

lemma chiSquareCharacteristicFunction_deriv (k t : ℝ) :
    deriv (chiSquareCharacteristicFunction k) t = chiSquareCharacteristicDerivative k t :=
  (chiSquareCharacteristicFunction_hasDerivAt k t).deriv

lemma chiSquareCharacteristicFunction_hasDerivAt_zero (k : ℝ) :
    HasDerivAt (chiSquareCharacteristicFunction k) ((k : ℂ) * Complex.I) 0 := by
  have h := chiSquareCharacteristicFunction_hasDerivAt k 0
  convert h using 1
  unfold chiSquareCharacteristicDerivative
  simp [Complex.one_cpow]
  ring

lemma chiSquareCharacteristicFunction_iteratedDeriv_one (k : ℝ) :
    iteratedDeriv 1 (chiSquareCharacteristicFunction k) 0 = (k : ℂ) * Complex.I := by
  rw [iteratedDeriv_one]
  exact (chiSquareCharacteristicFunction_hasDerivAt_zero k).deriv

lemma chiSquareCharacteristicDerivative_hasDerivAt_zero (k : ℝ) :
    HasDerivAt (chiSquareCharacteristicDerivative k) (-((k * (k + 2) : ℝ) : ℂ)) 0 := by
  unfold chiSquareCharacteristicDerivative
  have hcomplex : HasDerivAt
      (fun z : ℂ => (-(k : ℂ) / 2) *
        (((1 : ℂ) - 2 * Complex.I * z) ^ (-(k : ℂ) / 2 - 1)) *
          (-2 * Complex.I))
      (-((k * (k + 2) : ℝ) : ℂ)) 0 := by
    have hpow := (chiSquare_base_hasDerivAt_complex 0).cpow_const
      (c := (-(k : ℂ) / 2 - 1)) (by
        rw [Complex.mem_slitPlane_iff]
        left
        simp)
    have h := (hpow.const_mul (-(k : ℂ) / 2)).mul_const (-2 * Complex.I)
    convert h using 1
    · simp [Complex.one_cpow]
      ring_nf
      rw [Complex.I_sq]
      ring
  simpa using hcomplex.comp_ofReal

lemma chiSquareCharacteristicFunction_iteratedDeriv_two (k : ℝ) :
    iteratedDeriv 2 (chiSquareCharacteristicFunction k) 0 =
      -((k * (k + 2) : ℝ) : ℂ) := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  rw [show deriv (chiSquareCharacteristicFunction k) = chiSquareCharacteristicDerivative k by
    funext t
    exact chiSquareCharacteristicFunction_deriv k t]
  exact (chiSquareCharacteristicDerivative_hasDerivAt_zero k).deriv

noncomputable def chiSquareMean (k : ℝ) : ℝ := k

noncomputable def chiSquareSecondMoment (k : ℝ) : ℝ := k * (k + 2)

noncomputable def chiSquareVariance (k : ℝ) : ℝ := 2 * k

lemma chiSquareVariance_eq_secondMoment_sub_mean_sq (k : ℝ) :
    chiSquareVariance k = chiSquareSecondMoment k - chiSquareMean k ^ 2 := by
  unfold chiSquareVariance chiSquareSecondMoment chiSquareMean
  ring

theorem prob_9_10
    (k : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hMoment1 : MemLp id ((1 : ℕ) : ℝ≥0∞) μ)
    (hMoment2 : MemLp id ((2 : ℕ) : ℝ≥0∞) μ)
    (hCF : charFun μ = chiSquareCharacteristicFunction k) :
    (∫ x : ℝ, x ∂μ = chiSquareMean k) ∧
      (∫ x : ℝ, x ^ 2 ∂μ = chiSquareSecondMoment k) ∧
        (∫ x : ℝ, x ^ 2 ∂μ - (∫ x : ℝ, x ∂μ) ^ 2 = chiSquareVariance k) := by
  have hMeanC := characteristicFunction_moment_from_derivative_law (μ := μ) (n := 1) hMoment1
  have hSecondC := characteristicFunction_moment_from_derivative_law (μ := μ) (n := 2) hMoment2
  have hMeanCast : ((∫ x : ℝ, x ∂μ : ℝ) : ℂ) = (chiSquareMean k : ℂ) := by
    rw [hCF, chiSquareCharacteristicFunction_iteratedDeriv_one] at hMeanC
    unfold chiSquareMean
    calc
      ((∫ x : ℝ, x ∂μ : ℝ) : ℂ) =
          (Complex.I ^ 1)⁻¹ * ((k : ℂ) * Complex.I) := by
        simpa [pow_one] using hMeanC
      _ = (k : ℂ) := by
        rw [pow_one, Complex.inv_I]
        ring_nf
        rw [Complex.I_sq]
        ring
  have hSecondCast : ((∫ x : ℝ, x ^ 2 ∂μ : ℝ) : ℂ) =
      (chiSquareSecondMoment k : ℂ) := by
    rw [hCF, chiSquareCharacteristicFunction_iteratedDeriv_two] at hSecondC
    unfold chiSquareSecondMoment
    calc
      ((∫ x : ℝ, x ^ 2 ∂μ : ℝ) : ℂ) =
          (Complex.I ^ 2)⁻¹ * (-((k * (k + 2) : ℝ) : ℂ)) := by
        simpa using hSecondC
      _ = ((k * (k + 2) : ℝ) : ℂ) := by
        rw [Complex.I_sq]
        ring
  have hMean : ∫ x : ℝ, x ∂μ = chiSquareMean k := Complex.ofReal_injective hMeanCast
  have hSecond : ∫ x : ℝ, x ^ 2 ∂μ = chiSquareSecondMoment k :=
    Complex.ofReal_injective hSecondCast
  refine ⟨hMean, hSecond, ?_⟩
  rw [hMean, hSecond]
  unfold chiSquareVariance chiSquareSecondMoment chiSquareMean
  ring
