/-
TASK ID: ex_7_4_2
TYPE: Example_Proof
SOURCE PLAN: 28_chap7_pushforward_change_of_variable
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_7_12

open MeasureTheory ProbabilityTheory Set

noncomputable section

private lemma measurable_gammaPDF (a r : ℝ) :
    Measurable (ProbabilityTheory.gammaPDF a r) := by
  change Measurable
    (ENNReal.ofReal ∘ ProbabilityTheory.gammaPDFReal a r)
  exact ENNReal.measurable_ofReal.comp
    (ProbabilityTheory.measurable_gammaPDFReal a r)

private lemma gammaPDF_lt_top_ae (a r : ℝ) :
    ∀ᵐ x ∂(volume : Measure ℝ), ProbabilityTheory.gammaPDF a r x < ⊤ := by
  filter_upwards with x
  simp [ProbabilityTheory.gammaPDF]

private lemma toReal_gammaPDF {a r x : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (ProbabilityTheory.gammaPDF a r x).toReal = ProbabilityTheory.gammaPDFReal a r x := by
  simp [ProbabilityTheory.gammaPDF,
    ENNReal.toReal_ofReal, ProbabilityTheory.gammaPDFReal_nonneg ha hr x]

private lemma sqrt_half_mul_sqrt_two :
    ((1 / 2 : ℝ) ^ (1 / 2 : ℝ)) * Real.sqrt 2 = 1 := by
  have hsqrt_mul :
      Real.sqrt (1 / 2 : ℝ) * Real.sqrt (2 : ℝ) = Real.sqrt ((1 / 2 : ℝ) * 2) := by
    symm
    exact Real.sqrt_mul (by positivity : 0 ≤ (1 / 2 : ℝ)) (2 : ℝ)
  rw [Real.sqrt_eq_rpow] at hsqrt_mul
  simpa using hsqrt_mul

private lemma sqrt_two_mul_half_rpow (a : ℝ) :
    Real.sqrt 2 * ((1 / 2 : ℝ) ^ (a + 1 / 2 : ℝ)) = (1 / 2 : ℝ) ^ a := by
  rw [show (a + (1 / 2 : ℝ)) = a + (1 / 2 : ℝ) by ring]
  rw [Real.rpow_add (by norm_num : 0 < (1 / 2 : ℝ))]
  calc
    Real.sqrt 2 * (((1 / 2 : ℝ) ^ a) * ((1 / 2 : ℝ) ^ (1 / 2 : ℝ)))
        = ((1 / 2 : ℝ) ^ a) * (((1 / 2 : ℝ) ^ (1 / 2 : ℝ)) * Real.sqrt 2) := by ring
    _ = (1 / 2 : ℝ) ^ a := by rw [sqrt_half_mul_sqrt_two, mul_one]

private lemma sqrt_mul_gammaPDFReal_on_pos {a x : ℝ} (hx : 0 < x) :
    Real.sqrt x * ProbabilityTheory.gammaPDFReal a (1 / 2) x =
      (((1 / 2 : ℝ) ^ a) / Real.Gamma a) *
        (x ^ (a - 1 / 2) * Real.exp (-((1 / 2 : ℝ) * x ^ (1 : ℝ)))) := by
  rw [ProbabilityTheory.gammaPDFReal, if_pos hx.le, Real.sqrt_eq_rpow]
  have hpow : x ^ (1 / 2 : ℝ) * x ^ (a - 1) = x ^ (a - 1 / 2) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  rw [show Real.exp (-(1 / 2 * x)) = Real.exp (-((1 / 2 : ℝ) * x ^ (1 : ℝ))) by
        rw [Real.rpow_one]]
  calc
    x ^ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(1 / 2 * x ^ (1 : ℝ))))
        = (x ^ (1 / 2 : ℝ) * x ^ (a - 1)) *
            (((1 / 2 : ℝ) ^ a / Real.Gamma a) * Real.exp (-(1 / 2 * x ^ (1 : ℝ)))) := by
              ring
    _ = x ^ (a - 1 / 2) * (((1 / 2 : ℝ) ^ a / Real.Gamma a) * Real.exp (-(1 / 2 * x ^ (1 : ℝ)))) := by
          rw [hpow]
    _ = (((1 / 2 : ℝ) ^ a) / Real.Gamma a) *
          (x ^ (a - 1 / 2) * Real.exp (-(1 / 2 * x ^ (1 : ℝ)))) := by
            ring

private lemma integral_gammaPDFReal_eq_one {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ, ProbabilityTheory.gammaPDFReal a (1 / 2) x = 1 := by
  have hnonneg :
      0 ≤ᵐ[volume] fun x : ℝ => ProbabilityTheory.gammaPDFReal a (1 / 2) x := by
    exact Filter.Eventually.of_forall fun x =>
      ProbabilityTheory.gammaPDFReal_nonneg ha (by positivity : 0 < (1 / 2 : ℝ)) x
  calc
    ∫ x : ℝ, ProbabilityTheory.gammaPDFReal a (1 / 2) x
        = ENNReal.toReal (∫⁻ x, ENNReal.ofReal (ProbabilityTheory.gammaPDFReal a (1 / 2) x)) := by
            exact integral_eq_lintegral_of_nonneg_ae hnonneg
              (ProbabilityTheory.measurable_gammaPDFReal a (1 / 2)).aestronglyMeasurable
    _ = ENNReal.toReal (∫⁻ x, ProbabilityTheory.gammaPDF a (1 / 2) x) := by
          simp [ProbabilityTheory.gammaPDF]
    _ = 1 := by
          rw [ProbabilityTheory.lintegral_gammaPDF_eq_one ha (by positivity : 0 < (1 / 2 : ℝ))]
          simp

private lemma integral_Ioi_sqrt_mul_gammaPDFReal {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ in Ioi 0, Real.sqrt x * ProbabilityTheory.gammaPDFReal a (1 / 2) x =
      Real.sqrt 2 * Real.Gamma (a + 1 / 2) / Real.Gamma a := by
  have hEq :
      ∫ x : ℝ in Ioi 0, Real.sqrt x * ProbabilityTheory.gammaPDFReal a (1 / 2) x =
        ∫ x : ℝ in Ioi 0,
          (((1 / 2 : ℝ) ^ a) / Real.Gamma a) *
            (x ^ (a - 1 / 2) * Real.exp (-((1 / 2 : ℝ) * x ^ (1 : ℝ)))) := by
          refine setIntegral_congr_fun measurableSet_Ioi ?_
          intro x hx
          exact sqrt_mul_gammaPDFReal_on_pos hx
  rw [hEq, integral_const_mul]
  have hGammaA : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hInt :
      ∫ x : ℝ in Ioi 0, x ^ (a - 1 / 2) * Real.exp (-((1 / 2 : ℝ) * x ^ (1 : ℝ))) =
        ((1 / 2 : ℝ) ^ (-(a + 1 / 2))) * (1 : ℝ) * Real.Gamma (a + 1 / 2) := by
          calc
            ∫ x : ℝ in Ioi 0, x ^ (a - 1 / 2) * Real.exp (-((1 / 2 : ℝ) * x ^ (1 : ℝ)))
                = (1 / 2 : ℝ) ^ (-1 + (1 / 2 - a)) * Real.Gamma (a - 1 / 2 + 1) := by
                    simpa using
                      (integral_rpow_mul_exp_neg_mul_rpow
                        (p := (1 : ℝ)) (q := a - 1 / 2) (b := (1 / 2 : ℝ))
                        (by norm_num) (by linarith) (by norm_num))
            _ = ((1 / 2 : ℝ) ^ (-(a + 1 / 2))) * (1 : ℝ) * Real.Gamma (a + 1 / 2) := by
                  ring
  calc
    (((1 / 2 : ℝ) ^ a) / Real.Gamma a) *
        ∫ x : ℝ in Ioi 0, x ^ (a - 1 / 2) * Real.exp (-((1 / 2 : ℝ) * x ^ (1 : ℝ)))
        =
          (((1 / 2 : ℝ) ^ a) / Real.Gamma a) *
            (((1 / 2 : ℝ) ^ (-(a + 1 / 2))) * (1 : ℝ) * Real.Gamma (a + 1 / 2)) := by
              rw [hInt]
    _ = Real.sqrt 2 * Real.Gamma (a + 1 / 2) / Real.Gamma a := by
          have hpow :
              ((1 / 2 : ℝ) ^ a) * ((1 / 2 : ℝ) ^ (-((2 * a + 1) / 2))) = Real.sqrt 2 := by
                calc
                  ((1 / 2 : ℝ) ^ a) * ((1 / 2 : ℝ) ^ (-((2 * a + 1) / 2)))
                      = (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
                          rw [← Real.rpow_add (by norm_num : 0 < (1 / 2 : ℝ))]
                          congr 1
                          ring
                  _ = Real.sqrt 2 := by
                        simpa using (sqrt_two_mul_half_rpow (-(1 / 2 : ℝ))).symm
          field_simp [hGammaA]
          rw [hpow]

private lemma integral_sqrt_mul_gammaPDFReal {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ, Real.sqrt x * ProbabilityTheory.gammaPDFReal a (1 / 2) x =
      Real.sqrt 2 * Real.Gamma (a + 1 / 2) / Real.Gamma a := by
  calc
    ∫ x : ℝ, Real.sqrt x * ProbabilityTheory.gammaPDFReal a (1 / 2) x
        = ∫ x : ℝ in Ioi 0, Real.sqrt x * ProbabilityTheory.gammaPDFReal a (1 / 2) x := by
            rw [← integral_indicator measurableSet_Ioi]
            apply integral_congr_ae
            filter_upwards with x
            by_cases hx : 0 < x
            · simp [hx, Set.indicator]
            · have hxle : x ≤ 0 := le_of_not_gt hx
              simp [hx, Set.indicator, Real.sqrt_eq_zero_of_nonpos hxle]
    _ = Real.sqrt 2 * Real.Gamma (a + 1 / 2) / Real.Gamma a :=
          integral_Ioi_sqrt_mul_gammaPDFReal ha

private lemma integral_sqrt_gammaMeasure {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ, Real.sqrt x ∂ProbabilityTheory.gammaMeasure a (1 / 2) =
      ∫ x : ℝ, Real.sqrt x * ProbabilityTheory.gammaPDFReal a (1 / 2) x := by
  calc
    ∫ x : ℝ, Real.sqrt x ∂ProbabilityTheory.gammaMeasure a (1 / 2)
        = ∫ x : ℝ, (ProbabilityTheory.gammaPDF a (1 / 2) x).toReal * Real.sqrt x := by
            simpa [ProbabilityTheory.gammaMeasure, smul_eq_mul, mul_comm] using
              (integral_withDensity_eq_integral_toReal_smul
                (μ := (volume : Measure ℝ))
                (f := ProbabilityTheory.gammaPDF a (1 / 2))
                (g := fun x : ℝ => Real.sqrt x)
                (measurable_gammaPDF a (1 / 2))
                (gammaPDF_lt_top_ae a (1 / 2)))
    _ = ∫ x : ℝ, Real.sqrt x * ProbabilityTheory.gammaPDFReal a (1 / 2) x := by
          apply integral_congr_ae
          filter_upwards with x
          rw [toReal_gammaPDF ha (by positivity : 0 < (1 / 2 : ℝ))]
          ring

theorem ex_7_4_2 {k : ℝ} (hk : 0 < k) :
    let a : ℝ := k / 2
    let mean : ℝ := Real.sqrt 2 * Real.Gamma ((k + 1) / 2) / Real.Gamma (k / 2)
    (∫ x : ℝ in Ioi 0, Real.sqrt x * ProbabilityTheory.gammaPDFReal a (1 / 2) x) = mean ∧
      (∫ x : ℝ, Real.sqrt x ∂ProbabilityTheory.gammaMeasure a (1 / 2)) = mean := by
  dsimp
  have ha : 0 < k / 2 := by positivity
  have hshape : (k / 2 : ℝ) + 1 / 2 = (k + 1) / 2 := by ring
  have hIoi :
      ∫ x : ℝ in Ioi 0, Real.sqrt x * ProbabilityTheory.gammaPDFReal (k / 2) (1 / 2) x =
        Real.sqrt 2 * Real.Gamma ((k + 1) / 2) / Real.Gamma (k / 2) := by
    rw [← hshape]
    exact integral_Ioi_sqrt_mul_gammaPDFReal ha
  have hOrd :
      ∫ x : ℝ, Real.sqrt x * ProbabilityTheory.gammaPDFReal (k / 2) (1 / 2) x =
        Real.sqrt 2 * Real.Gamma ((k + 1) / 2) / Real.Gamma (k / 2) := by
    rw [← hshape]
    exact integral_sqrt_mul_gammaPDFReal ha
  have hMeas :
      ∫ x : ℝ, Real.sqrt x ∂ProbabilityTheory.gammaMeasure (k / 2) (1 / 2) =
        Real.sqrt 2 * Real.Gamma ((k + 1) / 2) / Real.Gamma (k / 2) := by
    rw [integral_sqrt_gammaMeasure ha]
    exact hOrd
  exact ⟨hIoi, hMeas⟩
