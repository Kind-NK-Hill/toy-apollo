/-
TASK ID: prob_9_1
TYPE: Problem
SOURCE PLAN: chapter9-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_09.def_9_2
import ProbabilityTheory.chapter_09.thm_9_2




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators

noncomputable section

private lemma measurable_exponentialPDF (rate : ℝ) :
    Measurable (ProbabilityTheory.exponentialPDF rate) := by
  change Measurable
    (ENNReal.ofReal ∘ ProbabilityTheory.exponentialPDFReal rate)
  exact ENNReal.measurable_ofReal.comp
    (ProbabilityTheory.measurable_exponentialPDFReal rate)

private lemma expMeasure_eq_withDensity_exponentialPDF (rate : ℝ) :
    ProbabilityTheory.expMeasure rate =
      (volume : Measure ℝ).withDensity
        (ProbabilityTheory.exponentialPDF rate) := by
  rfl

private lemma exponentialPDF_lt_top_ae (rate : ℝ) :
    ∀ᵐ x ∂(volume : Measure ℝ), ProbabilityTheory.exponentialPDF rate x < ⊤ := by
  filter_upwards with x
  simp [ProbabilityTheory.exponentialPDF]

private lemma toReal_exponentialPDF {rate x : ℝ} (hrate : 0 < rate) :
    (ProbabilityTheory.exponentialPDF rate x).toReal =
      ProbabilityTheory.exponentialPDFReal rate x := by
  simp [ProbabilityTheory.exponentialPDF, ENNReal.toReal_ofReal,
    ProbabilityTheory.exponentialPDFReal_nonneg hrate x]

private lemma exponentialPDF_mul_exp_ae_eq_indicator
    {lam t : ℝ} (hlam : 0 < lam) :
    (fun x : ℝ =>
        (ProbabilityTheory.exponentialPDF lam x).toReal * Real.exp (t * x))
      =ᵐ[(volume : Measure ℝ)]
    (Ioi (0 : ℝ)).indicator
      (fun x : ℝ => lam * Real.exp ((t - lam) * x)) := by
  filter_upwards
    [measure_eq_zero_iff_ae_notMem.mp (measure_singleton (0 : ℝ))] with x hx0
  rcases lt_or_gt_of_ne hx0 with hxlt | hxgt
  · have hxnot : ¬ 0 ≤ x := not_le_of_gt hxlt
    have hxnot' : x ∉ Ioi (0 : ℝ) := by
      simpa using not_lt_of_ge hxlt.le
    simp [toReal_exponentialPDF hlam, ProbabilityTheory.exponentialPDFReal,
      ProbabilityTheory.gammaPDFReal, hxnot, hxnot']
  · have hxnonneg : 0 ≤ x := le_of_lt hxgt
    have hxmem : x ∈ Ioi (0 : ℝ) := hxgt
    simp [toReal_exponentialPDF hlam, ProbabilityTheory.exponentialPDFReal,
      ProbabilityTheory.gammaPDFReal, hxnonneg, hxmem, Real.Gamma_one]
    calc
      lam * Real.exp (-(lam * x)) * Real.exp (t * x)
          = lam * (Real.exp (-(lam * x)) * Real.exp (t * x)) := by ring
      _ = lam * Real.exp (-(lam * x) + t * x) := by rw [Real.exp_add]
      _ = lam * Real.exp ((t - lam) * x) := by
            congr 1
            ring

private theorem exponential_exp_integrable
    {lam t : ℝ} (hlam : 0 < lam) (ht : t < lam) :
    Integrable (fun x : ℝ => Real.exp (t * x))
      (ProbabilityTheory.expMeasure lam) := by
  rw [expMeasure_eq_withDensity_exponentialPDF lam]
  rw [integrable_withDensity_iff
    (measurable_exponentialPDF lam) (exponentialPDF_lt_top_ae lam)]
  have hIoi :
      IntegrableOn (fun x : ℝ => lam * Real.exp ((t - lam) * x))
        (Ioi (0 : ℝ)) (volume : Measure ℝ) :=
    (integrableOn_exp_mul_Ioi (a := t - lam) (sub_neg.mpr ht) 0).const_mul lam
  have hIndicator :
      Integrable
        ((Ioi (0 : ℝ)).indicator
          (fun x : ℝ => lam * Real.exp ((t - lam) * x)))
        (volume : Measure ℝ) :=
    hIoi.integrable_indicator measurableSet_Ioi
  refine hIndicator.congr ?_
  filter_upwards [exponentialPDF_mul_exp_ae_eq_indicator
    (lam := lam) (t := t) hlam] with x hx
  simpa [mul_comm] using hx.symm

private theorem exponential_exp_integral_eq_formula
    {lam t : ℝ} (hlam : 0 < lam) (ht : t < lam)
    (_hInt : Integrable (fun x : ℝ => Real.exp (t * x))
      (ProbabilityTheory.expMeasure lam)) :
    ∫ x : ℝ, Real.exp (t * x) ∂ProbabilityTheory.expMeasure lam =
      lam / (lam - t) := by
  calc
    ∫ x : ℝ, Real.exp (t * x) ∂ProbabilityTheory.expMeasure lam
        = ∫ x : ℝ,
            (ProbabilityTheory.exponentialPDF lam x).toReal * Real.exp (t * x) := by
          rw [expMeasure_eq_withDensity_exponentialPDF lam]
          simpa [smul_eq_mul, mul_comm] using
            (integral_withDensity_eq_integral_toReal_smul
              (μ := (volume : Measure ℝ))
              (f := ProbabilityTheory.exponentialPDF lam)
              (g := fun x : ℝ => Real.exp (t * x))
              (measurable_exponentialPDF lam)
              (exponentialPDF_lt_top_ae lam))
    _ = ∫ x : ℝ,
          (Ioi (0 : ℝ)).indicator
            (fun x : ℝ => lam * Real.exp ((t - lam) * x)) x := by
          exact integral_congr_ae
            (exponentialPDF_mul_exp_ae_eq_indicator (lam := lam) (t := t) hlam)
    _ = ∫ x in Ioi (0 : ℝ), lam * Real.exp ((t - lam) * x) := by
          rw [integral_indicator measurableSet_Ioi]
    _ = lam * ∫ x in Ioi (0 : ℝ), Real.exp ((t - lam) * x) := by
          rw [integral_const_mul]
    _ = lam * (-Real.exp ((t - lam) * 0) / (t - lam)) := by
          rw [integral_exp_mul_Ioi (a := t - lam) (sub_neg.mpr ht) 0]
    _ = lam / (lam - t) := by
          have htlam : t - lam ≠ 0 := (sub_neg.mpr ht).ne
          have hlamt : lam - t ≠ 0 := (sub_pos.mpr ht).ne'
          simp only [mul_zero, Real.exp_zero]
          field_simp [htlam, hlamt]
          <;> ring

theorem exponential_momentGeneratingFunction_eq_formula
    {lam t : ℝ} (hlam : 0 < lam) (ht : t < lam) :
    @momentGeneratingFunction ℝ _ (ProbabilityTheory.expMeasure lam)
      (ProbabilityTheory.isProbabilityMeasure_expMeasure hlam) id
      (aemeasurable_id (μ := ProbabilityTheory.expMeasure lam)) t =
        ENNReal.ofReal (lam / (lam - t)) := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure lam) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hlam
  have hInt :
      Integrable (fun x : ℝ => Real.exp (t * x))
        (ProbabilityTheory.expMeasure lam) :=
    exponential_exp_integrable hlam ht
  have hNonneg :
      0 ≤ᵐ[ProbabilityTheory.expMeasure lam]
        fun x : ℝ => Real.exp (t * x) :=
    Filter.Eventually.of_forall fun _ => Real.exp_nonneg _
  change (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (t * x))
    ∂ProbabilityTheory.expMeasure lam) = ENNReal.ofReal (lam / (lam - t))
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hNonneg]
  congr 1
  exact exponential_exp_integral_eq_formula hlam ht hInt

theorem exponential_hasMomentGeneratingFunction
    {lam : ℝ} (hlam : 0 < lam) :
    @HasMomentGeneratingFunction ℝ _ (ProbabilityTheory.expMeasure lam)
      (ProbabilityTheory.isProbabilityMeasure_expMeasure hlam) id
      (aemeasurable_id (μ := ProbabilityTheory.expMeasure lam)) := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure lam) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hlam
  refine ⟨lam, hlam, ?_⟩
  intro t ht
  have htlam : t < lam := (le_abs_self t).trans_lt ht
  rw [exponential_momentGeneratingFunction_eq_formula hlam htlam]
  exact ENNReal.ofReal_lt_top

private theorem exponential_real_mgf_eq_formula_of_lt
    {lam t : ℝ} (hlam : 0 < lam) (ht : t < lam) :
    mgf id (ProbabilityTheory.expMeasure lam) t = lam / (lam - t) := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure lam) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hlam
  have hInt :
      Integrable (fun x : ℝ => Real.exp (t * x))
        (ProbabilityTheory.expMeasure lam) :=
    exponential_exp_integrable hlam ht
  have hBridge :
      (momentGeneratingFunction (ProbabilityTheory.expMeasure lam) id
        (aemeasurable_id (μ := ProbabilityTheory.expMeasure lam)) t).toReal =
        mgf id (ProbabilityTheory.expMeasure lam) t := by
    exact thm_9_2_momentGeneratingFunction_toReal_eq_mgf_of_integrable
      (aemeasurable_id (μ := ProbabilityTheory.expMeasure lam))
      (by simpa using hInt)
  calc
    mgf id (ProbabilityTheory.expMeasure lam) t =
        (momentGeneratingFunction (ProbabilityTheory.expMeasure lam) id
          (aemeasurable_id (μ := ProbabilityTheory.expMeasure lam)) t).toReal :=
      hBridge.symm
    _ = (ENNReal.ofReal (lam / (lam - t))).toReal := by
          rw [exponential_momentGeneratingFunction_eq_formula hlam ht]
    _ = lam / (lam - t) :=
      ENNReal.toReal_ofReal
        (div_nonneg hlam.le (sub_nonneg.mpr ht.le))

private theorem exponential_mgf_eq_formula_near_zero
    {lam : ℝ} (hlam : 0 < lam) :
    (mgf id (ProbabilityTheory.expMeasure lam))
      =ᶠ[nhds (0 : ℝ)] (fun t : ℝ => lam / (lam - t)) := by
  have hNear : ∀ᶠ t : ℝ in nhds 0, t ∈ Iio lam :=
    isOpen_Iio.eventually_mem hlam
  filter_upwards [hNear] with t ht
  exact exponential_real_mgf_eq_formula_of_lt hlam ht

theorem iteratedDeriv_exponential_mgf_formula_zero
    {lam : ℝ} (hlam : 0 < lam) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => lam / (lam - t)) 0 =
      k.factorial / lam ^ k := by
  have hInv :
      iteratedDeriv k (fun y : ℝ => 1 / y) lam =
        (-1 : ℝ) ^ k * k.factorial * lam ^ (-1 - k : ℤ) := by
    simpa only [iteratedDerivWithin_univ] using
      (iteratedDerivWithin_one_div (𝕜 := ℝ) (s := Set.univ) k isOpen_univ
        (Set.mem_univ lam))
  have hShift :
      iteratedDeriv k (fun t : ℝ => 1 / (lam - t)) 0 =
        (-1 : ℝ) ^ k * iteratedDeriv k (fun y : ℝ => 1 / y) lam := by
    have h := congrFun
      (iteratedDeriv_comp_const_sub k (fun y : ℝ => 1 / y) lam) 0
    simpa [smul_eq_mul] using h
  have hSign : ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) = 1 := by
    rw [← mul_pow]
    norm_num
  have hSignCancel (a b : ℝ) :
      (-1 : ℝ) ^ k * ((-1 : ℝ) ^ k * a * b) = a * b := by
    calc
      (-1 : ℝ) ^ k * ((-1 : ℝ) ^ k * a * b) =
          (((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k)) * a * b := by ring
      _ = a * b := by rw [hSign]; ring
  calc
    iteratedDeriv k (fun t : ℝ => lam / (lam - t)) 0 =
        lam * iteratedDeriv k (fun t : ℝ => 1 / (lam - t)) 0 := by
          simpa [div_eq_mul_inv] using
            (iteratedDeriv_const_mul_field
              (n := k) (x := (0 : ℝ)) lam
              (fun t : ℝ => 1 / (lam - t)))
    _ = lam * ((-1 : ℝ) ^ k *
          ((-1 : ℝ) ^ k * k.factorial * lam ^ (-1 - k : ℤ))) := by
          rw [hShift, hInv]
    _ = lam * (k.factorial * lam ^ (-1 - k : ℤ)) := by
          rw [hSignCancel]
    _ = k.factorial / lam ^ k := by
          have hExp : (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) := by omega
          rw [hExp, zpow_neg, zpow_natCast]
          field_simp [hlam.ne', pow_succ] <;> ring

theorem exponential_kth_moment_eq_formula
    {lam : ℝ} (hlam : 0 < lam) (k : ℕ) :
    ∫ x : ℝ, x ^ k ∂ProbabilityTheory.expMeasure lam =
      k.factorial / lam ^ k := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure lam) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hlam
  let hId : AEMeasurable (id : ℝ → ℝ) (ProbabilityTheory.expMeasure lam) :=
    aemeasurable_id
  have hHas :
      HasMomentGeneratingFunction (ProbabilityTheory.expMeasure lam) id hId := by
    simpa [hId] using exponential_hasMomentGeneratingFunction hlam
  have hRecover :=
    (thm_9_2 (μ := ProbabilityTheory.expMeasure lam) (X := id)
      measurable_id hId hHas k).2
  have hMomentDerivative :
      (∫ x : ℝ, x ^ k ∂ProbabilityTheory.expMeasure lam) =
        iteratedDeriv k (mgf id (ProbabilityTheory.expMeasure lam)) 0 := by
    simpa [generalMoment, moment] using hRecover
  calc
    (∫ x : ℝ, x ^ k ∂ProbabilityTheory.expMeasure lam) =
        iteratedDeriv k (mgf id (ProbabilityTheory.expMeasure lam)) 0 :=
      hMomentDerivative
    _ = iteratedDeriv k (fun t : ℝ => lam / (lam - t)) 0 := by
          exact Filter.EventuallyEq.iteratedDeriv_eq k
            (exponential_mgf_eq_formula_near_zero hlam)
    _ = k.factorial / lam ^ k :=
          iteratedDeriv_exponential_mgf_formula_zero hlam k

theorem prob_9_1 {lam : ℝ} (hlam : 0 < lam) :
    @HasMomentGeneratingFunction ℝ _ (ProbabilityTheory.expMeasure lam)
        (ProbabilityTheory.isProbabilityMeasure_expMeasure hlam) id
        (aemeasurable_id (μ := ProbabilityTheory.expMeasure lam)) ∧
      (∀ t : ℝ, t < lam →
        @momentGeneratingFunction ℝ _ (ProbabilityTheory.expMeasure lam)
          (ProbabilityTheory.isProbabilityMeasure_expMeasure hlam) id
          (aemeasurable_id (μ := ProbabilityTheory.expMeasure lam)) t =
            ENNReal.ofReal (lam / (lam - t))) ∧
      (∀ k : ℕ, 1 ≤ k →
        ∫ x : ℝ, x ^ k ∂ProbabilityTheory.expMeasure lam =
          k.factorial / lam ^ k) := by
  exact ⟨exponential_hasMomentGeneratingFunction hlam,
    fun t ht => exponential_momentGeneratingFunction_eq_formula hlam ht,
    fun k _hk => exponential_kth_moment_eq_formula hlam k⟩
