/-
TASK ID: prob_14_1
TYPE: Problem
SOURCE PLAN: chapter14-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_13.prob_13_11
import ProbabilityTheory.chapter_14.def_14_1
import ProbabilityTheory.chapter_14.thm_14_2




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators ENNReal Asymptotics

noncomputable section

 
def prob_14_1_risingFactorial (a : ℝ) (n : ℕ) : ℝ :=
  Finset.prod (Finset.range n) (fun j : ℕ => a + j)

@[simp]
theorem prob_14_1_risingFactorial_zero (a : ℝ) :
    prob_14_1_risingFactorial a 0 = 1 := by
  simp [prob_14_1_risingFactorial]

theorem prob_14_1_risingFactorial_succ (a : ℝ) (n : ℕ) :
    prob_14_1_risingFactorial a (n + 1) =
      prob_14_1_risingFactorial a n * (a + n) := by
  simp [prob_14_1_risingFactorial, Finset.prod_range_succ]

theorem prob_14_1_risingFactorial_pos_of_pos {a : ℝ}
    (ha : 0 < a) (n : ℕ) :
    0 < prob_14_1_risingFactorial a n := by
  rw [prob_14_1_risingFactorial]
  exact Finset.prod_pos fun j _ =>
    add_pos_of_pos_of_nonneg ha (by exact_mod_cast Nat.zero_le j)

theorem prob_14_1_risingFactorial_eq_gamma_ratio
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    prob_14_1_risingFactorial a n =
      Real.Gamma (a + n) / Real.Gamma a := by
  induction n with
  | zero =>
      have hΓa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
      simp [hΓa]
  | succ n ih =>
      have han_pos : 0 < a + (n : ℝ) :=
        add_pos_of_pos_of_nonneg ha (by exact_mod_cast Nat.zero_le n)
      have han_ne : a + (n : ℝ) ≠ 0 := han_pos.ne'
      rw [prob_14_1_risingFactorial_succ, ih]
      calc
        Real.Gamma (a + ↑n) / Real.Gamma a * (a + ↑n)
            = Real.Gamma ((a + ↑n) + 1) / Real.Gamma a := by
                rw [Real.Gamma_add_one han_ne]
                ring_nf
        _ = Real.Gamma (a + ↑(n + 1)) / Real.Gamma a := by
                norm_num [Nat.cast_add, Nat.cast_one, add_assoc]

theorem prob_14_1_gammaSeq_eq_factorial_div_risingFactorial_succ
    (a : ℝ) (n : ℕ) :
    Real.GammaSeq a n =
      (n : ℝ) ^ a * (n.factorial : ℝ) /
        prob_14_1_risingFactorial a (n + 1) := by
  simp [Real.GammaSeq, prob_14_1_risingFactorial]

theorem prob_14_1_risingFactorial_one_eq_factorial
    (n : ℕ) :
    prob_14_1_risingFactorial 1 n = (n.factorial : ℝ) := by
  rw [prob_14_1_risingFactorial_eq_gamma_ratio zero_lt_one n]
  have hΓ1 : Real.Gamma (1 : ℝ) = 1 := Real.Gamma_one
  have hΓn : Real.Gamma (1 + (n : ℝ)) = (n.factorial : ℝ) := by
    rw [add_comm]
    exact Real.Gamma_nat_eq_factorial n
  rw [hΓn, hΓ1, div_one]

theorem prob_14_1_factorial_isEquivalent_stirling :
    (fun n : ℕ => (n.factorial : ℝ)) ~[atTop]
      (fun n : ℕ =>
        Real.sqrt (2 * n * Real.pi) * (n / Real.exp 1) ^ n) :=
  Stirling.factorial_isEquivalent_stirling

theorem prob_14_1_gammaSeq_eq_factorial_div_gamma_ratio
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Real.GammaSeq a n =
      (n : ℝ) ^ a * (n.factorial : ℝ) /
        (Real.Gamma (a + (n + 1 : ℕ)) / Real.Gamma a) := by
  rw [Real.GammaSeq]
  rw [← prob_14_1_risingFactorial_eq_gamma_ratio ha (n + 1)]
  simp [prob_14_1_risingFactorial]

theorem prob_14_1_shifted_gammaSeq_ratio_identity
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) {n : ℕ} (hn : n ≠ 0) :
    (Real.Gamma (a + (n + 1 : ℕ)) / Real.Gamma (c + (n + 1 : ℕ))) /
        (n : ℝ) ^ (a - c) =
      (Real.Gamma a / Real.Gamma c) *
        (Real.GammaSeq c n / Real.GammaSeq a n) := by
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hnpow_a : (n : ℝ) ^ a ≠ 0 := (Real.rpow_pos_of_pos hnpos a).ne'
  have hnpow_c : (n : ℝ) ^ c ≠ 0 := (Real.rpow_pos_of_pos hnpos c).ne'
  have hnpow_ac : (n : ℝ) ^ (a - c) ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos (a - c)).ne'
  have hfact : (n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hΓa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hΓc : Real.Gamma c ≠ 0 := (Real.Gamma_pos_of_pos hc).ne'
  have hΓan : Real.Gamma (a + (n + 1 : ℕ)) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos
      (add_pos_of_pos_of_nonneg ha (by exact_mod_cast Nat.zero_le (n + 1)))).ne'
  have hΓcn : Real.Gamma (c + (n + 1 : ℕ)) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos
      (add_pos_of_pos_of_nonneg hc (by exact_mod_cast Nat.zero_le (n + 1)))).ne'
  rw [prob_14_1_gammaSeq_eq_factorial_div_gamma_ratio hc n]
  rw [prob_14_1_gammaSeq_eq_factorial_div_gamma_ratio ha n]
  rw [Real.rpow_sub hnpos]
  field_simp [hΓa, hΓc, hΓan, hΓcn, hnpow_a, hnpow_c, hnpow_ac, hfact]

theorem prob_14_1_shifted_gammaSeq_ratio_tendsto
    {a c : ℝ} (ha : 0 < a) :
    Tendsto
      (fun n : ℕ => Real.GammaSeq c n / Real.GammaSeq a n)
      atTop
      (𝓝 (Real.Gamma c / Real.Gamma a)) := by
  have hΓa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  exact (Real.GammaSeq_tendsto_Gamma c).div
    (Real.GammaSeq_tendsto_Gamma a) hΓa

theorem prob_14_1_shifted_gamma_ratio_succ_isEquivalent
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    (fun n : ℕ =>
        Real.Gamma (a + (n + 1 : ℕ)) /
          Real.Gamma (c + (n + 1 : ℕ))) ~[atTop]
      (fun n : ℕ => (n : ℝ) ^ (a - c)) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  have hΓa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hΓc : Real.Gamma c ≠ 0 := (Real.Gamma_pos_of_pos hc).ne'
  have hconst :
      (Real.Gamma a / Real.Gamma c) * (Real.Gamma c / Real.Gamma a) = 1 := by
    field_simp [hΓa, hΓc]
  have htend :
      Tendsto
        (fun n : ℕ =>
          (Real.Gamma a / Real.Gamma c) *
            (Real.GammaSeq c n / Real.GammaSeq a n))
        atTop
        (𝓝 1) := by
    have hconst_tend :
        Tendsto (fun _ : ℕ => Real.Gamma a / Real.Gamma c) atTop
          (𝓝 (Real.Gamma a / Real.Gamma c)) :=
      tendsto_const_nhds
    simpa [hconst] using
      (hconst_tend.mul
        (prob_14_1_shifted_gammaSeq_ratio_tendsto (a := a) (c := c) ha))
  refine Tendsto.congr' ?_ htend
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (prob_14_1_shifted_gammaSeq_ratio_identity ha hc hn).symm

theorem prob_14_1_shifted_gamma_ratio_unshift_step
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) {n : ℕ} (hn : n ≠ 0) :
    (Real.Gamma (a + n) / Real.Gamma (c + n)) /
        (n : ℝ) ^ (a - c) =
      ((c + n) / (a + n)) *
        ((Real.Gamma (a + (n + 1 : ℕ)) /
            Real.Gamma (c + (n + 1 : ℕ))) /
          (n : ℝ) ^ (a - c)) := by
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn
  have hnnonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hapos : 0 < a + (n : ℝ) := add_pos_of_pos_of_nonneg ha hnnonneg
  have hcpos : 0 < c + (n : ℝ) := add_pos_of_pos_of_nonneg hc hnnonneg
  have hane : a + (n : ℝ) ≠ 0 := hapos.ne'
  have hcne : c + (n : ℝ) ≠ 0 := hcpos.ne'
  have hΓan : Real.Gamma (a + n) ≠ 0 :=
    (Real.Gamma_pos_of_pos hapos).ne'
  have hΓcn : Real.Gamma (c + n) ≠ 0 :=
    (Real.Gamma_pos_of_pos hcpos).ne'
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hpow : (n : ℝ) ^ (a - c) ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos (a - c)).ne'
  have hGa_succ :
      Real.Gamma (a + (n + 1 : ℕ)) =
        (a + n) * Real.Gamma (a + n) := by
    have harg : a + (n + 1 : ℕ) = (a + n) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
      ring
    rw [harg, Real.Gamma_add_one hane]
  have hGc_succ :
      Real.Gamma (c + (n + 1 : ℕ)) =
        (c + n) * Real.Gamma (c + n) := by
    have harg : c + (n + 1 : ℕ) = (c + n) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
      ring
    rw [harg, Real.Gamma_add_one hcne]
  rw [hGa_succ, hGc_succ]
  field_simp [hane, hcne, hΓan, hΓcn, hpow]

theorem prob_14_1_shifted_gamma_ratio_isEquivalent
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    (fun n : ℕ => Real.Gamma (a + n) / Real.Gamma (c + n)) ~[atTop]
      (fun n : ℕ => (n : ℝ) ^ (a - c)) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  have hpow_ne :
      ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (a - c) ≠ 0 := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    exact (Real.rpow_pos_of_pos hnpos (a - c)).ne'
  have hsucc_tend :
      Tendsto
        ((fun n : ℕ =>
          Real.Gamma (a + (n + 1 : ℕ)) /
            Real.Gamma (c + (n + 1 : ℕ))) /
          fun n : ℕ => (n : ℝ) ^ (a - c))
        atTop
        (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hpow_ne).mp
      (prob_14_1_shifted_gamma_ratio_succ_isEquivalent ha hc)
  have hlin :
      Tendsto (fun n : ℕ => (c + n) / (a + n)) atTop (𝓝 1) := by
    have hlin0 :
        Tendsto (fun n : ℕ => (c + (1 : ℝ) * n) / (a + (1 : ℝ) * n))
          atTop (𝓝 ((1 : ℝ) / 1)) :=
      tendsto_add_mul_div_add_mul_atTop_nhds
        (a := c) (b := a) (c := (1 : ℝ)) (d := (1 : ℝ)) one_ne_zero
    simpa using hlin0
  have hprod :
      Tendsto
        (fun n : ℕ =>
          ((c + n) / (a + n)) *
            ((Real.Gamma (a + (n + 1 : ℕ)) /
                Real.Gamma (c + (n + 1 : ℕ))) /
              (n : ℝ) ^ (a - c)))
        atTop
        (𝓝 1) := by
    simpa using hlin.mul hsucc_tend
  refine Tendsto.congr' ?_ hprod
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (prob_14_1_shifted_gamma_ratio_unshift_step ha hc hn).symm



theorem prob_14_1_risingFactorial_succ_left (a : ℝ) :
    ∀ n : ℕ,
      prob_14_1_risingFactorial a (n + 1) =
        a * prob_14_1_risingFactorial (a + 1) n := by
  intro n
  induction n with
  | zero =>
      simp [prob_14_1_risingFactorial]
  | succ n ih =>
      rw [prob_14_1_risingFactorial_succ, ih, prob_14_1_risingFactorial_succ]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring



def prob_14_1_polyaWhiteMassFormula (w b : ℝ) (i k : ℕ) : ℝ :=
  (Nat.choose i k : ℝ) *
      prob_14_1_risingFactorial w k *
        prob_14_1_risingFactorial b (i - k) /
    prob_14_1_risingFactorial (b + w) i

theorem prob_14_1_polyaWhiteMassFormula_nonneg {w b : ℝ} {i k : ℕ}
    (hw : 0 < w) (hb : 0 < b) (_hk : k ≤ i) :
    0 ≤ prob_14_1_polyaWhiteMassFormula w b i k := by
  have hchoose : 0 ≤ (Nat.choose i k : ℝ) := by exact_mod_cast Nat.zero_le _
  have hwprod : 0 ≤ prob_14_1_risingFactorial w k :=
    (prob_14_1_risingFactorial_pos_of_pos hw k).le
  have hbprod : 0 ≤ prob_14_1_risingFactorial b (i - k) :=
    (prob_14_1_risingFactorial_pos_of_pos hb (i - k)).le
  have hden : 0 ≤ prob_14_1_risingFactorial (b + w) i :=
    (prob_14_1_risingFactorial_pos_of_pos (add_pos hb hw) i).le
  exact div_nonneg (mul_nonneg (mul_nonneg hchoose hwprod) hbprod) hden



def prob_14_1_betaDensity (w b C x : ℝ) : ℝ :=
  if x ∈ Set.Ioo (0 : ℝ) 1 then C * x ^ (w - 1) * (1 - x) ^ (b - 1) else 0



structure prob_14_1_BetaLawData (w b : ℝ) where
  law : ProbabilityMeasure ℝ
  normalizingConstant : ℝ
  normalizingConstant_pos : 0 < normalizingConstant
  density_represents_law :
    ∀ s : Set ℝ, MeasurableSet s →
      (law : Measure ℝ) s =
        ∫⁻ x, s.indicator
          (fun y : ℝ =>
            ENNReal.ofReal (prob_14_1_betaDensity w b normalizingConstant y)) x



theorem prob_14_1_betaDensity_eq_betaPDFReal
    (w b x : ℝ) :
    prob_14_1_betaDensity w b (1 / ProbabilityTheory.beta w b) x =
      ProbabilityTheory.betaPDFReal w b x := by
  by_cases hx : x ∈ Set.Ioo (0 : ℝ) 1
  · have hx' : 0 < x ∧ x < 1 := by
      simpa [Set.mem_Ioo] using hx
    simp [prob_14_1_betaDensity, ProbabilityTheory.betaPDFReal, hx, hx']
  · have hx' : ¬ (0 < x ∧ x < 1) := by
      simpa [Set.mem_Ioo] using hx
    simp [prob_14_1_betaDensity, ProbabilityTheory.betaPDFReal, hx, hx']

 
def prob_14_1_standardBetaLawData
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b) :
    prob_14_1_BetaLawData w b where
  law := ⟨ProbabilityTheory.betaMeasure w b,
    ProbabilityTheory.isProbabilityMeasureBeta hw hb⟩
  normalizingConstant := 1 / ProbabilityTheory.beta w b
  normalizingConstant_pos := one_div_pos.mpr (ProbabilityTheory.beta_pos hw hb)
  density_represents_law := by
    intro s hs
    change ProbabilityTheory.betaMeasure w b s = _
    rw [ProbabilityTheory.betaMeasure, withDensity_apply _ hs]
    rw [lintegral_indicator hs]
    apply setLIntegral_congr_fun hs
    intro x _hx
    simp only [ProbabilityTheory.betaPDF]
    simpa [one_div] using
      congrArg ENNReal.ofReal
        (prob_14_1_betaDensity_eq_betaPDFReal w b x).symm

 
theorem prob_14_1_one_div_beta_eq_gamma_ratio
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b) :
    1 / ProbabilityTheory.beta w b =
      Real.Gamma (w + b) / (Real.Gamma w * Real.Gamma b) := by
  have hgwgb_pos : 0 < Real.Gamma w * Real.Gamma b :=
    mul_pos (Real.Gamma_pos_of_pos hw) (Real.Gamma_pos_of_pos hb)
  have hgwgb_ne : Real.Gamma w * Real.Gamma b ≠ 0 := hgwgb_pos.ne'
  have hgwb : Real.Gamma (w + b) ≠ 0 :=
    (Real.Gamma_pos_of_pos (add_pos hw hb)).ne'
  rw [ProbabilityTheory.beta]
  calc
    1 / (Real.Gamma w * Real.Gamma b / Real.Gamma (w + b))
        = Real.Gamma (w + b) / (Real.Gamma w * Real.Gamma b) := by
          field_simp [hgwgb_ne, hgwb]
    _ = Real.Gamma (w + b) / (Real.Gamma w * Real.Gamma b) := rfl



theorem prob_14_1_gammaSeq_beta_normalization_tendsto
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b) :
    Tendsto
      (fun n : ℕ =>
        Real.GammaSeq (w + b) n / (Real.GammaSeq w n * Real.GammaSeq b n))
      atTop
      (𝓝 (Real.Gamma (w + b) / (Real.Gamma w * Real.Gamma b))) := by
  exact
    (Real.GammaSeq_tendsto_Gamma (w + b)).div
      ((Real.GammaSeq_tendsto_Gamma w).mul (Real.GammaSeq_tendsto_Gamma b))
      (mul_ne_zero (Real.Gamma_pos_of_pos hw).ne'
        (Real.Gamma_pos_of_pos hb).ne')



theorem prob_14_1_gammaSeq_beta_normalization_tendsto_one_div_beta
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b) :
    Tendsto
      (fun n : ℕ =>
        Real.GammaSeq (w + b) n / (Real.GammaSeq w n * Real.GammaSeq b n))
      atTop
      (𝓝 (1 / ProbabilityTheory.beta w b)) := by
  simpa [prob_14_1_one_div_beta_eq_gamma_ratio hw hb] using
    prob_14_1_gammaSeq_beta_normalization_tendsto (w := w) (b := b) hw hb

 
theorem prob_14_1_betaDensity_gamma_ratio_eq_betaPDFReal_of_mem
    {w b x : ℝ} (hw : 0 < w) (hb : 0 < b)
    (_hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    prob_14_1_betaDensity w b
        (Real.Gamma (w + b) / (Real.Gamma w * Real.Gamma b)) x =
      ProbabilityTheory.betaPDFReal w b x := by
  rw [← prob_14_1_one_div_beta_eq_gamma_ratio hw hb]
  exact prob_14_1_betaDensity_eq_betaPDFReal w b x

theorem prob_14_1_polyaWhiteMassFormula_eq_gamma_ratio
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b) (i k : ℕ) :
    prob_14_1_polyaWhiteMassFormula w b i k =
      (Nat.choose i k : ℝ) *
          (Real.Gamma (w + k) / Real.Gamma w) *
          (Real.Gamma (b + ((i - k : ℕ) : ℝ)) / Real.Gamma b) /
        (Real.Gamma (b + w + i) / Real.Gamma (b + w)) := by
  rw [prob_14_1_polyaWhiteMassFormula]
  rw [prob_14_1_risingFactorial_eq_gamma_ratio hw k]
  rw [prob_14_1_risingFactorial_eq_gamma_ratio hb (i - k)]
  rw [prob_14_1_risingFactorial_eq_gamma_ratio (add_pos hb hw) i]

theorem prob_14_1_polyaWhiteMassFormula_eq_gamma_product
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b) (i k : ℕ) :
    prob_14_1_polyaWhiteMassFormula w b i k =
      (Nat.choose i k : ℝ) *
          Real.Gamma (w + k) *
          Real.Gamma (b + ((i - k : ℕ) : ℝ)) *
          Real.Gamma (b + w) /
        (Real.Gamma w * Real.Gamma b *
          Real.Gamma (b + w + i)) := by
  have hΓw : Real.Gamma w ≠ 0 := (Real.Gamma_pos_of_pos hw).ne'
  have hΓb : Real.Gamma b ≠ 0 := (Real.Gamma_pos_of_pos hb).ne'
  have hΓbw : Real.Gamma (b + w) ≠ 0 :=
    (Real.Gamma_pos_of_pos (add_pos hb hw)).ne'
  have hΓwk : Real.Gamma (w + k) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos
      (add_pos_of_pos_of_nonneg hw (by exact_mod_cast Nat.zero_le k))).ne'
  have hΓbik : Real.Gamma (b + ((i - k : ℕ) : ℝ)) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos
      (add_pos_of_pos_of_nonneg hb
        (by exact_mod_cast Nat.zero_le (i - k : ℕ)))).ne'
  have hΓbwi : Real.Gamma (b + w + i) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos
      (add_pos_of_pos_of_nonneg (add_pos hb hw)
        (by exact_mod_cast Nat.zero_le i))).ne'
  rw [prob_14_1_polyaWhiteMassFormula_eq_gamma_ratio hw hb i k]
  field_simp [hΓw, hΓb, hΓbw, hΓwk, hΓbik, hΓbwi]

theorem prob_14_1_polyaWhiteMassFormula_eq_beta_gamma_product
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b) (i k : ℕ) :
    prob_14_1_polyaWhiteMassFormula w b i k =
      (Nat.choose i k : ℝ) *
          (1 / ProbabilityTheory.beta w b) *
          Real.Gamma (w + k) *
          Real.Gamma (b + ((i - k : ℕ) : ℝ)) /
        Real.Gamma (b + w + i) := by
  have hΓw : Real.Gamma w ≠ 0 := (Real.Gamma_pos_of_pos hw).ne'
  have hΓb : Real.Gamma b ≠ 0 := (Real.Gamma_pos_of_pos hb).ne'
  have hΓwb : Real.Gamma (w + b) ≠ 0 :=
    (Real.Gamma_pos_of_pos (add_pos hw hb)).ne'
  have hΓbwi : Real.Gamma (b + w + i) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos
      (add_pos_of_pos_of_nonneg (add_pos hb hw)
        (by exact_mod_cast Nat.zero_le i))).ne'
  rw [prob_14_1_polyaWhiteMassFormula_eq_gamma_product hw hb i k]
  rw [prob_14_1_one_div_beta_eq_gamma_ratio hw hb]
  field_simp [hΓw, hΓb, hΓwb, hΓbwi]
  ring_nf

theorem prob_14_1_choose_cast_eq_gamma_ratio
    {i k : ℕ} (hk : k ≤ i) :
    (Nat.choose i k : ℝ) =
      Real.Gamma ((i : ℝ) + 1) /
        (Real.Gamma ((k : ℝ) + 1) *
          Real.Gamma (((i - k : ℕ) : ℝ) + 1)) := by
  have hchoose :=
    Nat.choose_mul_factorial_mul_factorial hk
  have hchoose_real :
      (Nat.choose i k : ℝ) * (k.factorial : ℝ) *
          ((i - k).factorial : ℝ) = (i.factorial : ℝ) := by
    exact_mod_cast hchoose
  have hkfact : (k.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  have hikfact : ((i - k).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (i - k)
  have hΓi : Real.Gamma ((i : ℝ) + 1) = (i.factorial : ℝ) :=
    Real.Gamma_nat_eq_factorial i
  have hΓk : Real.Gamma ((k : ℝ) + 1) = (k.factorial : ℝ) :=
    Real.Gamma_nat_eq_factorial k
  have hΓik :
      Real.Gamma (((i - k : ℕ) : ℝ) + 1) =
        ((i - k).factorial : ℝ) :=
    Real.Gamma_nat_eq_factorial (i - k)
  calc
    (Nat.choose i k : ℝ)
        = (i.factorial : ℝ) /
            ((k.factorial : ℝ) * ((i - k).factorial : ℝ)) := by
            rw [← hchoose_real]
            field_simp [hkfact, hikfact]
    _ = Real.Gamma ((i : ℝ) + 1) /
        (Real.Gamma ((k : ℝ) + 1) *
          Real.Gamma (((i - k : ℕ) : ℝ) + 1)) := by
            rw [hΓi, hΓk, hΓik]

theorem prob_14_1_polyaWhiteMassFormula_eq_beta_gamma_ratio_split
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b) {i k : ℕ} (hk : k ≤ i) :
    prob_14_1_polyaWhiteMassFormula w b i k =
      (1 / ProbabilityTheory.beta w b) *
        (Real.Gamma ((i : ℝ) + 1) / Real.Gamma (b + w + i)) *
        (Real.Gamma (w + k) / Real.Gamma ((k : ℝ) + 1)) *
        (Real.Gamma (b + ((i - k : ℕ) : ℝ)) /
          Real.Gamma (((i - k : ℕ) : ℝ) + 1)) := by
  have hΓi : Real.Gamma ((i : ℝ) + 1) ≠ 0 := by
    rw [Real.Gamma_nat_eq_factorial i]
    exact_mod_cast Nat.factorial_ne_zero i
  have hΓk : Real.Gamma ((k : ℝ) + 1) ≠ 0 := by
    rw [Real.Gamma_nat_eq_factorial k]
    exact_mod_cast Nat.factorial_ne_zero k
  have hΓik :
      Real.Gamma (((i - k : ℕ) : ℝ) + 1) ≠ 0 := by
    rw [Real.Gamma_nat_eq_factorial (i - k)]
    exact_mod_cast Nat.factorial_ne_zero (i - k)
  have hΓbwi : Real.Gamma (b + w + i) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos
      (add_pos_of_pos_of_nonneg (add_pos hb hw)
        (by exact_mod_cast Nat.zero_le i))).ne'
  have hΓwk : Real.Gamma (w + k) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos
      (add_pos_of_pos_of_nonneg hw (by exact_mod_cast Nat.zero_le k))).ne'
  have hΓbik : Real.Gamma (b + ((i - k : ℕ) : ℝ)) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos
      (add_pos_of_pos_of_nonneg hb
        (by exact_mod_cast Nat.zero_le (i - k : ℕ)))).ne'
  rw [prob_14_1_polyaWhiteMassFormula_eq_beta_gamma_product hw hb i k]
  rw [prob_14_1_choose_cast_eq_gamma_ratio hk]
  field_simp [hΓi, hΓk, hΓik, hΓbwi, hΓwk, hΓbik]

theorem prob_14_1_polyaWhiteMassFormula_zero_eq
    (w b : ℝ) (i : ℕ) :
    prob_14_1_polyaWhiteMassFormula w b i 0 =
      prob_14_1_risingFactorial b i /
        prob_14_1_risingFactorial (b + w) i := by
  simp [prob_14_1_polyaWhiteMassFormula]

theorem prob_14_1_polyaWhiteMassFormula_self_eq
    (w b : ℝ) (i : ℕ) :
    prob_14_1_polyaWhiteMassFormula w b i i =
      prob_14_1_risingFactorial w i /
        prob_14_1_risingFactorial (b + w) i := by
  simp [prob_14_1_polyaWhiteMassFormula]

 
theorem prob_14_1_polyaWhiteMassFormula_reflect
    {w b : ℝ} {i k : ℕ} (hk : k ≤ i) :
    prob_14_1_polyaWhiteMassFormula w b i k =
      prob_14_1_polyaWhiteMassFormula b w i (i - k) := by
  have hsub : i - (i - k) = k := Nat.sub_sub_self hk
  rw [prob_14_1_polyaWhiteMassFormula, prob_14_1_polyaWhiteMassFormula]
  rw [Nat.choose_symm hk]
  rw [hsub]
  ring_nf

 
theorem prob_14_1_polyaWhiteMassFormula_pos
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b)
    {i k : ℕ} (hk : k ≤ i) :
    0 < prob_14_1_polyaWhiteMassFormula w b i k := by
  have hchoose : 0 < (Nat.choose i k : ℝ) := by
    exact_mod_cast Nat.choose_pos hk
  have hwprod : 0 < prob_14_1_risingFactorial w k :=
    prob_14_1_risingFactorial_pos_of_pos hw k
  have hbprod : 0 < prob_14_1_risingFactorial b (i - k) :=
    prob_14_1_risingFactorial_pos_of_pos hb (i - k)
  have hden : 0 < prob_14_1_risingFactorial (b + w) i :=
    prob_14_1_risingFactorial_pos_of_pos (add_pos hb hw) i
  exact div_pos (mul_pos (mul_pos hchoose hwprod) hbprod) hden

 
theorem prob_14_1_polyaWhiteMassFormula_succ_eq_mul_ratio
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b)
    {i k : ℕ} (hk : k + 1 ≤ i) :
    prob_14_1_polyaWhiteMassFormula w b i (k + 1) =
      prob_14_1_polyaWhiteMassFormula w b i k *
        (((i - k : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) *
        ((w + (k : ℝ)) / (b + ((i - (k + 1) : ℕ) : ℝ))) := by
  have hk1_ne : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hb_tail_pos : 0 < b + ((i - (k + 1) : ℕ) : ℝ) :=
    add_pos_of_pos_of_nonneg hb
      (by exact_mod_cast Nat.zero_le (i - (k + 1)))
  have hb_tail_ne : b + ((i - (k + 1) : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt hb_tail_pos
  have hden_ne : prob_14_1_risingFactorial (b + w) i ≠ 0 :=
    ne_of_gt (prob_14_1_risingFactorial_pos_of_pos (add_pos hb hw) i)
  have hchoose :
      (Nat.choose i (k + 1) : ℝ) =
        (Nat.choose i k : ℝ) *
          ((i - k : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) := by
    have hcast :
        (Nat.choose i (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) =
          (Nat.choose i k : ℝ) * ((i - k : ℕ) : ℝ) := by
      exact_mod_cast (Nat.choose_succ_right_eq i k)
    field_simp [hk1_ne]
    simpa [mul_comm] using hcast
  have hsub : i - k = i - (k + 1) + 1 := by
    omega
  rw [prob_14_1_polyaWhiteMassFormula, prob_14_1_polyaWhiteMassFormula]
  rw [hchoose]
  rw [prob_14_1_risingFactorial_succ]
  rw [hsub, prob_14_1_risingFactorial_succ]
  field_simp [hk1_ne, hb_tail_ne, hden_ne]

 
theorem prob_14_1_polyaWhiteMassFormula_succ_div_eq_ratio
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b)
    {i k : ℕ} (hk : k + 1 ≤ i) :
    prob_14_1_polyaWhiteMassFormula w b i (k + 1) /
        prob_14_1_polyaWhiteMassFormula w b i k =
      (((i - k : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) *
        ((w + (k : ℝ)) / (b + ((i - (k + 1) : ℕ) : ℝ))) := by
  have hk_le_i : k ≤ i := Nat.le_trans (Nat.le_succ k) hk
  have hpk_ne :
      prob_14_1_polyaWhiteMassFormula w b i k ≠ 0 :=
    ne_of_gt (prob_14_1_polyaWhiteMassFormula_pos hw hb hk_le_i)
  rw [prob_14_1_polyaWhiteMassFormula_succ_eq_mul_ratio hw hb hk]
  field_simp [hpk_ne]



theorem prob_14_1_polyaWhiteMassFormula_succ_div_eq_ratio_real_sub
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b)
    {i k : ℕ} (hk : k + 1 ≤ i) :
    prob_14_1_polyaWhiteMassFormula w b i (k + 1) /
        prob_14_1_polyaWhiteMassFormula w b i k =
      (((i - k : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) *
        ((w + (k : ℝ)) / (b + (i : ℝ) - (k : ℝ) - 1)) := by
  rw [prob_14_1_polyaWhiteMassFormula_succ_div_eq_ratio hw hb hk]
  have hden :
      b + ((i - (k + 1) : ℕ) : ℝ) =
        b + (i : ℝ) - (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk]
    norm_num
    ring
  rw [hden]

theorem prob_14_1_polyaWhiteMassFormula_zero_tendsto_zero
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b) :
    Tendsto
      (fun i : ℕ => prob_14_1_polyaWhiteMassFormula w b i 0)
      atTop (𝓝 0) := by
  have hEq :
      (fun i : ℕ => prob_14_1_polyaWhiteMassFormula w b i 0) =ᶠ[atTop]
      (fun i : ℕ =>
        (Real.Gamma (b + w) / Real.Gamma b) *
          (Real.Gamma (b + i) / Real.Gamma (b + w + i))) := by
    exact Filter.Eventually.of_forall fun i => by
      have hΓb : Real.Gamma b ≠ 0 := (Real.Gamma_pos_of_pos hb).ne'
      have hΓbw : Real.Gamma (b + w) ≠ 0 :=
        (Real.Gamma_pos_of_pos (add_pos hb hw)).ne'
      have hΓbi : Real.Gamma (b + i) ≠ 0 := by
        exact (Real.Gamma_pos_of_pos
          (add_pos_of_pos_of_nonneg hb (by exact_mod_cast Nat.zero_le i))).ne'
      have hΓbwi : Real.Gamma (b + w + i) ≠ 0 := by
        exact (Real.Gamma_pos_of_pos
          (add_pos_of_pos_of_nonneg (add_pos hb hw)
            (by exact_mod_cast Nat.zero_le i))).ne'
      change prob_14_1_polyaWhiteMassFormula w b i 0 =
        (Real.Gamma (b + w) / Real.Gamma b) *
          (Real.Gamma (b + i) / Real.Gamma (b + w + i))
      rw [prob_14_1_polyaWhiteMassFormula_zero_eq]
      rw [prob_14_1_risingFactorial_eq_gamma_ratio hb i]
      rw [prob_14_1_risingFactorial_eq_gamma_ratio (add_pos hb hw) i]
      field_simp [hΓb, hΓbw, hΓbi, hΓbwi]
  have hratio :
      (fun i : ℕ => Real.Gamma (b + i) / Real.Gamma (b + w + i)) ~[atTop]
        (fun i : ℕ => (i : ℝ) ^ (-w)) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (prob_14_1_shifted_gamma_ratio_isEquivalent
        (a := b) (c := b + w) hb (add_pos hb hw))
  have hconst :
      (fun _ : ℕ => Real.Gamma (b + w) / Real.Gamma b) ~[atTop]
        (fun _ : ℕ => Real.Gamma (b + w) / Real.Gamma b) :=
    Filter.EventuallyEq.rfl.isEquivalent
  have hmass :
      (fun i : ℕ => prob_14_1_polyaWhiteMassFormula w b i 0) ~[atTop]
        (fun i : ℕ =>
          (Real.Gamma (b + w) / Real.Gamma b) * (i : ℝ) ^ (-w)) :=
    hEq.isEquivalent.trans (hconst.mul hratio)
  have htend :
      Tendsto
        (fun i : ℕ =>
          (Real.Gamma (b + w) / Real.Gamma b) * (i : ℝ) ^ (-w))
        atTop (𝓝 0) := by
    have hrpow :
        Tendsto (fun i : ℕ => (i : ℝ) ^ (-w)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hw).comp tendsto_natCast_atTop_atTop
    simpa using
      (tendsto_const_nhds.mul hrpow)
  exact (hmass.tendsto_nhds_iff).2 htend

theorem prob_14_1_polyaWhiteMassFormula_self_tendsto_zero
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b) :
    Tendsto
      (fun i : ℕ => prob_14_1_polyaWhiteMassFormula w b i i)
      atTop (𝓝 0) := by
  have hEq :
      (fun i : ℕ => prob_14_1_polyaWhiteMassFormula w b i i) =ᶠ[atTop]
      (fun i : ℕ =>
        (Real.Gamma (b + w) / Real.Gamma w) *
          (Real.Gamma (w + i) / Real.Gamma (b + w + i))) := by
    exact Filter.Eventually.of_forall fun i => by
      have hΓw : Real.Gamma w ≠ 0 := (Real.Gamma_pos_of_pos hw).ne'
      have hΓbw : Real.Gamma (b + w) ≠ 0 :=
        (Real.Gamma_pos_of_pos (add_pos hb hw)).ne'
      have hΓwi : Real.Gamma (w + i) ≠ 0 := by
        exact (Real.Gamma_pos_of_pos
          (add_pos_of_pos_of_nonneg hw (by exact_mod_cast Nat.zero_le i))).ne'
      have hΓbwi : Real.Gamma (b + w + i) ≠ 0 := by
        exact (Real.Gamma_pos_of_pos
          (add_pos_of_pos_of_nonneg (add_pos hb hw)
            (by exact_mod_cast Nat.zero_le i))).ne'
      change prob_14_1_polyaWhiteMassFormula w b i i =
        (Real.Gamma (b + w) / Real.Gamma w) *
          (Real.Gamma (w + i) / Real.Gamma (b + w + i))
      rw [prob_14_1_polyaWhiteMassFormula_self_eq]
      rw [prob_14_1_risingFactorial_eq_gamma_ratio hw i]
      rw [prob_14_1_risingFactorial_eq_gamma_ratio (add_pos hb hw) i]
      field_simp [hΓw, hΓbw, hΓwi, hΓbwi]
  have hratio :
      (fun i : ℕ => Real.Gamma (w + i) / Real.Gamma (b + w + i)) ~[atTop]
        (fun i : ℕ => (i : ℝ) ^ (-b)) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (prob_14_1_shifted_gamma_ratio_isEquivalent
        (a := w) (c := b + w) hw (add_pos hb hw))
  have hconst :
      (fun _ : ℕ => Real.Gamma (b + w) / Real.Gamma w) ~[atTop]
        (fun _ : ℕ => Real.Gamma (b + w) / Real.Gamma w) :=
    Filter.EventuallyEq.rfl.isEquivalent
  have hmass :
      (fun i : ℕ => prob_14_1_polyaWhiteMassFormula w b i i) ~[atTop]
        (fun i : ℕ =>
          (Real.Gamma (b + w) / Real.Gamma w) * (i : ℝ) ^ (-b)) :=
    hEq.isEquivalent.trans (hconst.mul hratio)
  have htend :
      Tendsto
        (fun i : ℕ =>
          (Real.Gamma (b + w) / Real.Gamma w) * (i : ℝ) ^ (-b))
        atTop (𝓝 0) := by
    have hrpow :
        Tendsto (fun i : ℕ => (i : ℝ) ^ (-b)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hb).comp tendsto_natCast_atTop_atTop
    simpa using
      (tendsto_const_nhds.mul hrpow)
  exact (hmass.tendsto_nhds_iff).2 htend

theorem prob_14_1_polyaWhiteMassFormula_gamma_ratio_product_isEquivalent
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b)
    (kseq : ℕ → ℕ)
    (hk_le : ∀ᶠ n in atTop, kseq n ≤ n)
    (hk_top : Tendsto kseq atTop atTop)
    (hrest_top : Tendsto (fun n : ℕ => n - kseq n) atTop atTop) :
    (fun n : ℕ =>
        prob_14_1_polyaWhiteMassFormula w b n (kseq n)) ~[atTop]
      (fun n : ℕ =>
        (((1 / ProbabilityTheory.beta w b) *
          ((n : ℝ) ^ (1 - (b + w)))) *
          ((kseq n : ℝ) ^ (w - 1))) *
          (((n - kseq n : ℕ) : ℝ) ^ (b - 1))) := by
  have hEq :
      (fun n : ℕ =>
        prob_14_1_polyaWhiteMassFormula w b n (kseq n)) =ᶠ[atTop]
  (fun n : ℕ =>
        (((1 / ProbabilityTheory.beta w b) *
          (Real.Gamma ((n : ℝ) + 1) / Real.Gamma (b + w + n))) *
          (Real.Gamma (w + kseq n) /
            Real.Gamma ((kseq n : ℝ) + 1))) *
          (Real.Gamma (b + ((n - kseq n : ℕ) : ℝ)) /
            Real.Gamma (((n - kseq n : ℕ) : ℝ) + 1))) := by
    filter_upwards [hk_le] with n hn
    rw [prob_14_1_polyaWhiteMassFormula_eq_beta_gamma_ratio_split hw hb hn]
  have hconst :
      (fun _ : ℕ => 1 / ProbabilityTheory.beta w b) ~[atTop]
        (fun _ : ℕ => 1 / ProbabilityTheory.beta w b) :=
    Filter.EventuallyEq.rfl.isEquivalent
  have hA :
      (fun n : ℕ => Real.Gamma ((n : ℝ) + 1) / Real.Gamma (b + w + n)) ~[atTop]
        (fun n : ℕ => (n : ℝ) ^ (1 - (b + w))) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (prob_14_1_shifted_gamma_ratio_isEquivalent
        (a := (1 : ℝ)) (c := b + w) zero_lt_one (add_pos hb hw))
  have hB :
      (fun n : ℕ =>
        Real.Gamma (w + kseq n) / Real.Gamma ((kseq n : ℝ) + 1)) ~[atTop]
        (fun n : ℕ => (kseq n : ℝ) ^ (w - 1)) := by
    simpa [Function.comp_def, add_comm, add_left_comm, add_assoc] using
      (prob_14_1_shifted_gamma_ratio_isEquivalent
        (a := w) (c := (1 : ℝ)) hw zero_lt_one).comp_tendsto hk_top
  have hC :
      (fun n : ℕ =>
        Real.Gamma (b + ((n - kseq n : ℕ) : ℝ)) /
          Real.Gamma (((n - kseq n : ℕ) : ℝ) + 1)) ~[atTop]
        (fun n : ℕ => ((n - kseq n : ℕ) : ℝ) ^ (b - 1)) := by
    simpa [Function.comp_def, add_comm, add_left_comm, add_assoc] using
      (prob_14_1_shifted_gamma_ratio_isEquivalent
        (a := b) (c := (1 : ℝ)) hb zero_lt_one).comp_tendsto hrest_top
  exact hEq.isEquivalent.trans (((hconst.mul hA).mul hB).mul hC)

theorem prob_14_1_scaled_gamma_kernel_eq_ratio_kernel
    {C w b n k r : ℝ} (hn : 0 < n) (hk : 0 < k) (hr : 0 < r) :
    n * (((C * n ^ (1 - (b + w))) * k ^ (w - 1)) * r ^ (b - 1)) =
      C * (k / n) ^ (w - 1) * (r / n) ^ (b - 1) := by
  rw [Real.div_rpow hk.le hn.le, Real.div_rpow hr.le hn.le]
  have hnw : n ^ (w - 1) ≠ 0 := (Real.rpow_pos_of_pos hn (w - 1)).ne'
  have hnb : n ^ (b - 1) ≠ 0 := (Real.rpow_pos_of_pos hn (b - 1)).ne'
  field_simp [hnw, hnb]
  have h12 :
      n ^ (1 : ℝ) * n ^ (1 - (b + w)) =
        n ^ ((1 : ℝ) + (1 - (b + w))) := by
    exact (Real.rpow_add hn (1 : ℝ) (1 - (b + w))).symm
  have hwb :
      n ^ (w - 1) * n ^ (b - 1) =
        n ^ ((w - 1) + (b - 1)) := by
    exact (Real.rpow_add hn (w - 1) (b - 1)).symm
  have hall :
      n * n ^ (1 - (b + w)) *
          (n ^ (w - 1) * n ^ (b - 1)) = 1 := by
    calc
      n * n ^ (1 - (b + w)) *
          (n ^ (w - 1) * n ^ (b - 1))
          =
        n ^ (1 : ℝ) * n ^ (1 - (b + w)) *
          (n ^ (w - 1) * n ^ (b - 1)) := by
            rw [Real.rpow_one]
      _ = n ^ ((1 : ℝ) + (1 - (b + w))) *
          n ^ ((w - 1) + (b - 1)) := by
            rw [h12, hwb]
      _ = n ^ ((1 : ℝ) + (1 - (b + w)) + ((w - 1) + (b - 1))) := by
            exact
              (Real.rpow_add hn ((1 : ℝ) + (1 - (b + w)))
                ((w - 1) + (b - 1))).symm
      _ = 1 := by
            have hzero :
                (1 : ℝ) + (1 - (b + w)) + ((w - 1) + (b - 1)) = 0 := by
              ring
            rw [hzero, Real.rpow_zero]
  calc
    n * C * n ^ (1 - (b + w)) * n ^ (w - 1) * n ^ (b - 1)
        = C * (n * n ^ (1 - (b + w)) *
            (n ^ (w - 1) * n ^ (b - 1))) := by
          ring
    _ = C := by rw [hall, mul_one]

theorem prob_14_1_scaled_gamma_kernel_tendsto
    {w b x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (kseq : ℕ → ℕ)
    (hk_ratio :
      Tendsto (fun n : ℕ => (kseq n : ℝ) / (n : ℝ)) atTop (𝓝 x))
    (hrest_ratio :
      Tendsto
        (fun n : ℕ => ((n - kseq n : ℕ) : ℝ) / (n : ℝ))
        atTop (𝓝 (1 - x)))
    (hk_pos : ∀ᶠ n in atTop, 0 < kseq n)
    (hrest_pos : ∀ᶠ n in atTop, 0 < n - kseq n) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          ((((1 / ProbabilityTheory.beta w b) *
            ((n : ℝ) ^ (1 - (b + w)))) *
            ((kseq n : ℝ) ^ (w - 1))) *
            (((n - kseq n : ℕ) : ℝ) ^ (b - 1))))
      atTop
      (𝓝 ((1 / ProbabilityTheory.beta w b) *
        x ^ (w - 1) * (1 - x) ^ (b - 1))) := by
  have hxrest : 0 < 1 - x := sub_pos.mpr hx1
  have hratio_kernel :
      Tendsto
        (fun n : ℕ =>
          (1 / ProbabilityTheory.beta w b) *
            ((kseq n : ℝ) / (n : ℝ)) ^ (w - 1) *
            (((n - kseq n : ℕ) : ℝ) / (n : ℝ)) ^ (b - 1))
        atTop
        (𝓝 ((1 / ProbabilityTheory.beta w b) *
          x ^ (w - 1) * (1 - x) ^ (b - 1))) := by
    have hkpow :
        Tendsto
          (fun n : ℕ => ((kseq n : ℝ) / (n : ℝ)) ^ (w - 1))
          atTop (𝓝 (x ^ (w - 1))) :=
      hk_ratio.rpow tendsto_const_nhds (Or.inl hx0.ne')
    have hrpow :
        Tendsto
          (fun n : ℕ =>
            (((n - kseq n : ℕ) : ℝ) / (n : ℝ)) ^ (b - 1))
          atTop (𝓝 ((1 - x) ^ (b - 1))) :=
      hrest_ratio.rpow tendsto_const_nhds (Or.inl hxrest.ne')
    simpa [mul_assoc] using
      ((tendsto_const_nhds.mul hkpow).mul hrpow)
  refine Tendsto.congr' ?_ hratio_kernel
  filter_upwards [eventually_ne_atTop 0, hk_pos, hrest_pos] with n hn hk hnrest
  have hn_pos_nat : 0 < n := Nat.pos_of_ne_zero hn
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hk_pos_real : 0 < (kseq n : ℝ) := by exact_mod_cast hk
  have hrest_pos_real : 0 < ((n - kseq n : ℕ) : ℝ) := by
    exact_mod_cast hnrest
  exact (prob_14_1_scaled_gamma_kernel_eq_ratio_kernel
    (C := 1 / ProbabilityTheory.beta w b) (w := w) (b := b)
    (n := (n : ℝ)) (k := (kseq n : ℝ))
    (r := ((n - kseq n : ℕ) : ℝ)) hn_pos hk_pos_real hrest_pos_real).symm

theorem prob_14_1_scaled_polya_mass_tendsto_betaDensity_of_count_sequence
    {w b x : ℝ} (hw : 0 < w) (hb : 0 < b)
    (hx0 : 0 < x) (hx1 : x < 1)
    (kseq : ℕ → ℕ)
    (hk_le : ∀ᶠ n in atTop, kseq n ≤ n)
    (hk_top : Tendsto kseq atTop atTop)
    (hrest_top : Tendsto (fun n : ℕ => n - kseq n) atTop atTop)
    (hk_ratio :
      Tendsto (fun n : ℕ => (kseq n : ℝ) / (n : ℝ)) atTop (𝓝 x))
    (hrest_ratio :
      Tendsto
        (fun n : ℕ => ((n - kseq n : ℕ) : ℝ) / (n : ℝ))
        atTop (𝓝 (1 - x)))
    (hk_pos : ∀ᶠ n in atTop, 0 < kseq n)
    (hrest_pos : ∀ᶠ n in atTop, 0 < n - kseq n) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) * prob_14_1_polyaWhiteMassFormula w b n (kseq n))
      atTop
      (𝓝 (prob_14_1_betaDensity w b (1 / ProbabilityTheory.beta w b) x)) := by
  have hmain :=
    prob_14_1_polyaWhiteMassFormula_gamma_ratio_product_isEquivalent
      hw hb kseq hk_le hk_top hrest_top
  have hn_equiv :
      (fun n : ℕ => (n : ℝ)) ~[atTop] (fun n : ℕ => (n : ℝ)) :=
    Filter.EventuallyEq.rfl.isEquivalent
  have hscaled :
      (fun n : ℕ =>
        (n : ℝ) * prob_14_1_polyaWhiteMassFormula w b n (kseq n)) ~[atTop]
      (fun n : ℕ =>
        (n : ℝ) *
          ((((1 / ProbabilityTheory.beta w b) *
            ((n : ℝ) ^ (1 - (b + w)))) *
            ((kseq n : ℝ) ^ (w - 1))) *
            (((n - kseq n : ℕ) : ℝ) ^ (b - 1)))) :=
    hn_equiv.mul hmain
  have hkernel :=
    prob_14_1_scaled_gamma_kernel_tendsto
      (w := w) (b := b) hx0 hx1 kseq hk_ratio hrest_ratio hk_pos hrest_pos
  have hdensity :
      (1 / ProbabilityTheory.beta w b) *
        x ^ (w - 1) * (1 - x) ^ (b - 1) =
      prob_14_1_betaDensity w b (1 / ProbabilityTheory.beta w b) x := by
    have hxmem : x ∈ Set.Ioo (0 : ℝ) 1 := by
      exact ⟨hx0, hx1⟩
    simp [prob_14_1_betaDensity, hxmem, mul_assoc]
  rw [← hdensity]
  exact (hscaled.tendsto_nhds_iff).2 hkernel



def prob_14_1_cdfConvergence
    (laws : ℕ → ProbabilityMeasure ℝ) (limitLaw : ProbabilityMeasure ℝ) : Prop :=
  ∀ x : ℝ,
    ContinuousAt (fun y : ℝ => ((limitLaw : Measure ℝ) (Set.Iic y)).toReal) x →
      Tendsto
        (fun n : ℕ => ((laws n : Measure ℝ) (Set.Iic x)).toReal)
        atTop
        (𝓝 (((limitLaw : Measure ℝ) (Set.Iic x)).toReal))



def prob_14_1_scaledCountLaw (ν : ProbabilityMeasure ℝ) (i : ℕ) :
    ProbabilityMeasure ℝ :=
  ν.map (by fun_prop : AEMeasurable (fun x : ℝ => x / (i : ℝ)) (ν : Measure ℝ))



def prob_14_1_whiteFractionLaws
    (whiteCountLaws : ℕ → ProbabilityMeasure ℝ) :
    ℕ → ProbabilityMeasure ℝ :=
  fun i => prob_14_1_scaledCountLaw (whiteCountLaws i) i



theorem prob_14_1_scaled_count_law_atom
    (ν : ProbabilityMeasure ℝ) {i k : ℕ} (hi : 1 ≤ i) :
    (prob_14_1_scaledCountLaw ν i : Measure ℝ)
        {x : ℝ | x = (k : ℝ) / (i : ℝ)} =
      (ν : Measure ℝ) {x : ℝ | x = (k : ℝ)} := by
  have hi_pos_nat : 0 < i := Nat.succ_le_iff.mp hi
  have hi_ne : (i : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hi_pos_nat)
  have hA : MeasurableSet ({x : ℝ | x = (k : ℝ) / (i : ℝ)}) := by
    simpa only [Set.setOf_eq_eq_singleton] using
      (measurableSet_singleton ((k : ℝ) / (i : ℝ)))
  have hpre :
      (fun x : ℝ => x / (i : ℝ)) ⁻¹'
          {x : ℝ | x = (k : ℝ) / (i : ℝ)} =
        {x : ℝ | x = (k : ℝ)} := by
    ext x
    constructor
    · intro hx
      change x / (i : ℝ) = (k : ℝ) / (i : ℝ) at hx
      have hmul := congrArg (fun y : ℝ => y * (i : ℝ)) hx
      simpa [hi_ne] using hmul
    · intro hx
      change x = (k : ℝ) at hx
      change x / (i : ℝ) = (k : ℝ) / (i : ℝ)
      rw [hx]
  rw [prob_14_1_scaledCountLaw, ProbabilityMeasure.map]
  change (Measure.map (fun x : ℝ => x / (i : ℝ)) (ν : Measure ℝ))
      {x : ℝ | x = (k : ℝ) / (i : ℝ)} =
    (ν : Measure ℝ) {x : ℝ | x = (k : ℝ)}
  rw [Measure.map_apply_of_aemeasurable
    (by fun_prop : AEMeasurable (fun x : ℝ => x / (i : ℝ)) (ν : Measure ℝ)) hA]
  rw [hpre]



theorem prob_14_1_cdfConvergence_to_weak
    {laws : ℕ → ProbabilityMeasure ℝ} {limitLaw : ProbabilityMeasure ℝ}
    (h : prob_14_1_cdfConvergence laws limitLaw) :
    Tendsto laws atTop (𝓝 limitLaw) := by
  let Fseq : ℕ → thm_10_8_ProbabilityCdf := fun n : ℕ =>
    thm_10_8_probabilityCdfOfMeasure ((laws n : ProbabilityMeasure ℝ) : Measure ℝ)
  let F : thm_10_8_ProbabilityCdf :=
    thm_10_8_probabilityCdfOfMeasure ((limitLaw : ProbabilityMeasure ℝ) : Measure ℝ)
  let Yn : ℕ → ℝ → ℝ := fun n : ℕ =>
    thm_10_8_lowerQuantileVariable (Fseq n)
  let Y : ℝ → ℝ := thm_10_8_lowerQuantileVariable F
  have hCdfConv :
      ∀ x : ℝ, ContinuousAt (F.stieltjes : ℝ → ℝ) x →
        Tendsto (fun n : ℕ => (Fseq n).stieltjes x) atTop
          (𝓝 (F.stieltjes x)) := by
    have hDist : CdfConvergesInDistribution laws limitLaw := by
      intro x hcont
      have hcont_raw :
          ContinuousAt
            (fun y : ℝ => ((limitLaw : Measure ℝ) (Set.Iic y)).toReal) x := by
        change ContinuousAt (measureCdf limitLaw) x
        exact hcont
      exact h x hcont_raw
    intro x hcont
    have hcont_measure :
        ContinuousAt (measureCdf limitLaw) x := by
      have hfun :
          (fun y : ℝ => measureCdf limitLaw y) =
            (fun y : ℝ => F.stieltjes y) := by
        funext y
        simp [F, thm_10_8_probabilityCdfOfMeasure, measureCdf,
          ProbabilityTheory.cdf_eq_real]
      change ContinuousAt
        (fun y : ℝ => measureCdf limitLaw y) x
      rw [hfun]
      exact hcont
    have htendsto := hDist x hcont_measure
    simpa [Fseq, F, thm_10_8_probabilityCdfOfMeasure, measureCdf,
      ProbabilityTheory.cdf_eq_real] using htendsto
  have hAlmostSure :
      ∀ᵐ ω ∂thm_10_8_unitIntervalMeasure,
        Tendsto (fun n : ℕ => Yn n ω) atTop (nhds (Y ω)) := by
    simpa [Yn, Y, Fseq, F] using
      thm_10_8_almost_sure_lowerQuantile_tendsto Fseq F hCdfConv
  have hYnMeas : ∀ n : ℕ, Measurable (Yn n) := by
    intro n
    exact thm_10_8_lowerQuantileVariable_measurable (Fseq n)
  have hInMeasure : TendstoInMeasure thm_10_8_unitIntervalMeasure Yn atTop Y :=
    tendstoInMeasure_of_tendsto_ae
      (fun n : ℕ => (hYnMeas n).aestronglyMeasurable)
      hAlmostSure
  have hInDistribution :
      TendstoInDistribution Yn atTop Y
        (fun _ : ℕ => thm_10_8_unitIntervalMeasure)
        thm_10_8_unitIntervalMeasure :=
    hInMeasure.tendstoInDistribution
      (fun n : ℕ => (hYnMeas n).aemeasurable)
  have hYnLaw :
      ∀ n : ℕ,
        Measure.map (Yn n) thm_10_8_unitIntervalMeasure =
          ((laws n : ProbabilityMeasure ℝ) : Measure ℝ) := by
    intro n
    haveI : IsProbabilityMeasure (((laws n : ProbabilityMeasure ℝ) : Measure ℝ)) :=
      (laws n).property
    simpa [Yn, Fseq] using
      (@thm_10_8_quantile_law_preservation_of_probabilityCdfOfMeasure
        (((laws n : ProbabilityMeasure ℝ) : Measure ℝ))
        (laws n).property)
  have hYLaw :
      Measure.map Y thm_10_8_unitIntervalMeasure =
        ((limitLaw : ProbabilityMeasure ℝ) : Measure ℝ) := by
    haveI : IsProbabilityMeasure (((limitLaw : ProbabilityMeasure ℝ) : Measure ℝ)) :=
      limitLaw.property
    simpa [Y, F] using
      (@thm_10_8_quantile_law_preservation_of_probabilityCdfOfMeasure
        (((limitLaw : ProbabilityMeasure ℝ) : Measure ℝ))
        limitLaw.property)
  have hLawTendsto : Tendsto laws atTop (𝓝 limitLaw) := by
    have hPseq :
        (fun n : ℕ =>
          (⟨Measure.map (Yn n) thm_10_8_unitIntervalMeasure,
            Measure.isProbabilityMeasure_map
              (hInDistribution.forall_aemeasurable n)⟩ :
            ProbabilityMeasure ℝ)) = laws := by
      funext n
      apply Subtype.ext
      simpa using hYnLaw n
    have hP :
        (⟨Measure.map Y thm_10_8_unitIntervalMeasure,
          Measure.isProbabilityMeasure_map hInDistribution.aemeasurable_limit⟩ :
          ProbabilityMeasure ℝ) = limitLaw := by
      apply Subtype.ext
      simpa using hYLaw
    rw [← hPseq, ← hP]
    exact hInDistribution.tendsto
  exact hLawTendsto
