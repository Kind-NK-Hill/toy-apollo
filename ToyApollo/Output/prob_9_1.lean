import Mathlib
import ToyApollo.Output.def_9_2
import ToyApollo.Output.def_9_1
import ToyApollo.Output.thm_9_2

/-
TASK ID: prob_9_1
TYPE: Problem
SOURCE PLAN: chapter9-problems
TASK CONTENT:
\textbf{Problem 9.1} Find the moment generating function of the exponential distribution with parameter $\lambda$, and use it to determine the $k$-th moment, for $k\geq 1$.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators

noncomputable section

noncomputable def exponentialMGFFormula (lam t : ℝ) : ℝ :=
  lam / (lam - t)

noncomputable def exponentialMomentFormula (lam : ℝ) (k : ℕ) : ℝ :=
  k.factorial / lam ^ k

noncomputable def exponentialFiniteMGF
    (lam : ℝ) (hlam : 0 < lam) (t : ℝ) : ℝ :=
  @finiteMomentGeneratingFunction ℝ _ (ProbabilityTheory.expMeasure lam)
    (ProbabilityTheory.isProbabilityMeasure_expMeasure hlam) id
    (aemeasurable_id (μ := ProbabilityTheory.expMeasure lam)) t

private lemma measurable_exponentialPDF (rate : ℝ) :
    Measurable (ProbabilityTheory.exponentialPDF rate) := by
  simpa [ProbabilityTheory.exponentialPDF] using
    ENNReal.measurable_ofReal.comp (ProbabilityTheory.measurable_exponentialPDFReal rate)

private lemma exponentialPDF_lt_top_ae (rate : ℝ) :
    ∀ᵐ x ∂(volume : Measure ℝ), ProbabilityTheory.exponentialPDF rate x < ⊤ := by
  filter_upwards with x
  simp [ProbabilityTheory.exponentialPDF]

private lemma toReal_exponentialPDF {rate x : ℝ} (hrate : 0 < rate) :
    (ProbabilityTheory.exponentialPDF rate x).toReal =
      ProbabilityTheory.exponentialPDFReal rate x := by
  simp [ProbabilityTheory.exponentialPDF, ENNReal.toReal_ofReal,
    ProbabilityTheory.exponentialPDFReal_nonneg hrate x]

private lemma gamma_nat_shift (k : ℕ) :
    Real.Gamma ((k : ℝ) + 1) = k.factorial := by
  simpa [Nat.cast_add, Nat.cast_one] using Real.Gamma_nat_eq_factorial k

private lemma exponential_mgf_integral_formula {lam t : ℝ}
    (hlt : 0 < lam - t) :
    ∫ x : ℝ in Ioi (0 : ℝ), Real.exp (-(lam - t) * x) =
      (lam - t) ^ (-1 : ℝ) * Real.Gamma (1 / (1 : ℝ) + 1) := by
  have hfun :
      (fun x : ℝ => Real.exp (-(lam - t) * x ^ (1 : ℝ))) =
        fun x : ℝ => Real.exp (-(lam - t) * x) := by
    funext x
    rw [Real.rpow_one]
  rw [← hfun]
  simpa using integral_exp_neg_mul_rpow
    (p := 1) (b := lam - t) zero_lt_one hlt

private lemma exponential_moment_integral_formula {lam : ℝ}
    (hlam : 0 < lam) (k : ℕ) :
    ∫ x : ℝ in Ioi (0 : ℝ), x ^ k * Real.exp (-(lam * x)) =
      (1 / lam) ^ ((k : ℝ) + 1) * Real.Gamma ((k : ℝ) + 1) := by
  have hfun :
      (fun x : ℝ => x ^ ((k : ℝ) + 1 - 1) * Real.exp (-(lam * x))) =
        fun x : ℝ => x ^ k * Real.exp (-(lam * x)) := by
    funext x
    congr 1
    rw [show (k : ℝ) + 1 - 1 = (k : ℝ) by ring]
    exact Real.rpow_natCast x k
  rw [← hfun]
  exact Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (k : ℝ) + 1) (r := lam) (by positivity) hlam

private lemma exponential_moment_algebra {lam : ℝ}
    (hlam : 0 < lam) (k : ℕ) :
    lam * ((1 / lam) ^ ((k : ℝ) + 1) * Real.Gamma ((k : ℝ) + 1)) =
      exponentialMomentFormula lam k := by
  rw [gamma_nat_shift k]
  rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by norm_num]
  rw [Real.rpow_natCast]
  change lam * ((1 / lam) ^ (k + 1) * (k.factorial : ℝ)) =
    (k.factorial : ℝ) / lam ^ k
  field_simp [hlam.ne']
  rw [one_div, inv_pow]
  rw [pow_succ]
  field_simp [hlam.ne']

private lemma exponential_mgf_algebra {lam t : ℝ} :
    lam * ((lam - t) ^ (-1 : ℝ) * Real.Gamma (1 / (1 : ℝ) + 1)) =
      exponentialMGFFormula lam t := by
  norm_num [exponentialMGFFormula, Real.Gamma_two, Real.rpow_neg_one,
    div_eq_mul_inv]

theorem exponential_real_mgf_eq_formula
    {lam t : ℝ} (hlam : 0 < lam) (ht : t < lam) :
    mgf id (ProbabilityTheory.expMeasure lam) t =
      exponentialMGFFormula lam t := by
  have hlt : 0 < lam - t := sub_pos.mpr ht
  change ∫ x : ℝ, Real.exp (t * x) ∂ProbabilityTheory.expMeasure lam =
    exponentialMGFFormula lam t
  calc
    ∫ x : ℝ, Real.exp (t * x) ∂ProbabilityTheory.expMeasure lam
        = ∫ x : ℝ,
            (ProbabilityTheory.exponentialPDF lam x).toReal * Real.exp (t * x) := by
          simpa [ProbabilityTheory.expMeasure, smul_eq_mul, mul_comm] using
            (integral_withDensity_eq_integral_toReal_smul
              (μ := (volume : Measure ℝ))
              (f := ProbabilityTheory.exponentialPDF lam)
              (g := fun x : ℝ => Real.exp (t * x))
              (measurable_exponentialPDF lam)
              (exponentialPDF_lt_top_ae lam))
    _ = ∫ x in Ioi (0 : ℝ), lam * Real.exp (-(lam - t) * x) := by
          rw [← integral_indicator measurableSet_Ioi]
          refine integral_congr_ae ?_
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
    _ = lam * ∫ x in Ioi (0 : ℝ), Real.exp (-(lam - t) * x) := by
          rw [integral_const_mul]
    _ = lam * ((lam - t) ^ (-1 : ℝ) * Real.Gamma (1 / (1 : ℝ) + 1)) := by
          rw [exponential_mgf_integral_formula hlt]
    _ = exponentialMGFFormula lam t := exponential_mgf_algebra

theorem exponential_mgf_eq_formula
    {lam t : ℝ} (hlam : 0 < lam) (ht : t < lam) :
    exponentialFiniteMGF lam hlam t = exponentialMGFFormula lam t := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure lam) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hlam
  haveI : NeZero (ProbabilityTheory.expMeasure lam) :=
    ⟨IsProbabilityMeasure.ne_zero (ProbabilityTheory.expMeasure lam)⟩
  have hFormulaPos : 0 < exponentialMGFFormula lam t := by
    have hlt : 0 < lam - t := sub_pos.mpr ht
    unfold exponentialMGFFormula
    exact div_pos hlam hlt
  have hMgfPos : 0 < mgf id (ProbabilityTheory.expMeasure lam) t := by
    rw [exponential_real_mgf_eq_formula hlam ht]
    exact hFormulaPos
  have hInt :
      Integrable (fun x : ℝ => Real.exp (t * id x))
        (ProbabilityTheory.expMeasure lam) :=
    (mgf_pos_iff (X := id) (μ := ProbabilityTheory.expMeasure lam)
      (t := t)).mp hMgfPos
  calc
    exponentialFiniteMGF lam hlam t =
        mgf id (ProbabilityTheory.expMeasure lam) t := by
          unfold exponentialFiniteMGF
          exact thm_9_2_finiteMomentGeneratingFunction_eq_mgf_of_integrable
            (aemeasurable_id (μ := ProbabilityTheory.expMeasure lam)) hInt
    _ = exponentialMGFFormula lam t :=
          exponential_real_mgf_eq_formula hlam ht

theorem exponential_kth_moment_eq_formula
    {lam : ℝ} (hlam : 0 < lam) (k : ℕ) :
    ∫ x : ℝ, x ^ k ∂ProbabilityTheory.expMeasure lam =
      exponentialMomentFormula lam k := by
  calc
    ∫ x : ℝ, x ^ k ∂ProbabilityTheory.expMeasure lam
        = ∫ x : ℝ, (ProbabilityTheory.exponentialPDF lam x).toReal * x ^ k := by
          simpa [ProbabilityTheory.expMeasure, smul_eq_mul, mul_comm] using
            (integral_withDensity_eq_integral_toReal_smul
              (μ := (volume : Measure ℝ))
              (f := ProbabilityTheory.exponentialPDF lam)
              (g := fun x : ℝ => x ^ k)
              (measurable_exponentialPDF lam)
              (exponentialPDF_lt_top_ae lam))
    _ = ∫ x in Ioi (0 : ℝ), lam * x ^ k * Real.exp (-(lam * x)) := by
          rw [← integral_indicator measurableSet_Ioi]
          refine integral_congr_ae ?_
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
            ring
    _ = lam * ∫ x in Ioi (0 : ℝ), x ^ k * Real.exp (-(lam * x)) := by
          rw [show (fun x : ℝ => lam * x ^ k * Real.exp (-(lam * x))) =
              fun x : ℝ => lam * (x ^ k * Real.exp (-(lam * x))) by
                funext x
                ring]
          rw [integral_const_mul]
    _ = lam * ((1 / lam) ^ ((k : ℝ) + 1) * Real.Gamma ((k : ℝ) + 1)) := by
          rw [exponential_moment_integral_formula hlam k]
    _ = exponentialMomentFormula lam k := exponential_moment_algebra hlam k

theorem prob_9_1 {lam : ℝ} (hlam : 0 < lam) :
    (∀ t : ℝ, t < lam →
        exponentialFiniteMGF lam hlam t =
          exponentialMGFFormula lam t) ∧
      (∀ k : ℕ, 1 ≤ k →
        ∫ x : ℝ, x ^ k ∂ProbabilityTheory.expMeasure lam =
          exponentialMomentFormula lam k) := by
  exact ⟨fun t ht => exponential_mgf_eq_formula hlam ht,
    fun k _hk => exponential_kth_moment_eq_formula hlam k⟩
