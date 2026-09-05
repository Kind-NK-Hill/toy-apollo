/-
TASK ID: prob_11_2
TYPE: Problem
SOURCE PLAN: chapter11-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_11.thm_11_2




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory
open scoped ENNReal



theorem prob_11_2_shifted_square_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hXm : Measurable X) (hX : MemLp X 2 P) (t : ℝ) :
    (∫ ω, (X ω - P[X] + t) ^ 2 ∂P) =
      _root_.variance P X (FiniteAbsMoment.of_memLp hXm hX) + t ^ 2 := by
  let Y : Ω → ℝ := fun ω => X ω - P[X]
  have hXint : Integrable X P := hX.integrable (by norm_num)
  have hY_mem : MemLp Y 2 P := by
    change MemLp (X - fun _ : Ω => P[X]) 2 P
    exact hX.sub (memLp_const (P[X]) : MemLp (fun _ : Ω => P[X]) 2 P)
  have hY_int : Integrable Y P := hY_mem.integrable (by norm_num)
  have hY2_int : Integrable (fun ω => Y ω ^ 2) P := hY_mem.integrable_sq
  have hLin_int : Integrable (fun ω => (2 * t) * Y ω) P :=
    hY_int.const_mul (2 * t)
  have hConst_int : Integrable (fun _ : Ω => t ^ 2) P := integrable_const (t ^ 2)
  have hY_integral : (∫ ω, Y ω ∂P) = 0 := by
    rw [show (∫ ω, Y ω ∂P) = ∫ ω, X ω - P[X] ∂P by rfl]
    rw [integral_sub hXint (integrable_const (P[X])), integral_const]
    simp
  have hvar :
      _root_.variance P X (FiniteAbsMoment.of_memLp hXm hX) =
        ∫ ω, Y ω ^ 2 ∂P := by
    rw [_root_.variance, rthCentralMoment]
    rw [ProbabilityTheory.centralMoment_two_eq_variance (μ := P) (X := X)
      hX.aemeasurable]
    rw [ProbabilityTheory.variance_eq_integral (μ := P) (X := X) hX.aemeasurable]
  calc
    (∫ ω, (X ω - P[X] + t) ^ 2 ∂P)
        = ∫ ω, (Y ω + t) ^ 2 ∂P := by rfl
    _ = ∫ ω, (Y ω ^ 2 + (2 * t) * Y ω + t ^ 2) ∂P := by
      congr with ω
      ring
    _ = ∫ ω, Y ω ^ 2 ∂P + ∫ ω, (2 * t) * Y ω ∂P + ∫ ω, t ^ 2 ∂P := by
      rw [integral_add
        (f := fun ω => Y ω ^ 2 + (2 * t) * Y ω)
        (g := fun _ : Ω => t ^ 2)
        (hY2_int.add hLin_int) hConst_int]
      rw [integral_add
        (f := fun ω => Y ω ^ 2) (g := fun ω => (2 * t) * Y ω)
        hY2_int hLin_int]
    _ = ∫ ω, Y ω ^ 2 ∂P + (2 * t) * ∫ ω, Y ω ∂P + t ^ 2 := by
      rw [integral_const_mul, integral_const]
      simp
    _ = _root_.variance P X (FiniteAbsMoment.of_memLp hXm hX) + t ^ 2 := by
      rw [hY_integral, ← hvar]
      ring



theorem prob_11_2_positive {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hXm : Measurable X) (hX : MemLp X 2 P)
    {a : ℝ} (ha : 0 < a) :
    P.real {ω | a ≤ X ω - P[X]} ≤
      _root_.variance P X (FiniteAbsMoment.of_memLp hXm hX) /
        (_root_.variance P X (FiniteAbsMoment.of_memLp hXm hX) + a ^ 2) := by
  let v : ℝ := _root_.variance P X (FiniteAbsMoment.of_memLp hXm hX)
  let t : ℝ := v / a
  have hv_nonneg : 0 ≤ v := by
    dsimp [v]
    rw [_root_.variance, rthCentralMoment]
    rw [ProbabilityTheory.centralMoment_two_eq_variance (μ := P) (X := X)
      hX.aemeasurable]
    exact ProbabilityTheory.variance_nonneg X P
  have ht_nonneg : 0 ≤ t := div_nonneg hv_nonneg ha.le
  let Z : Ω → ℝ := fun ω => (X ω - P[X] + t) ^ 2
  have hZ_nonneg : 0 ≤ᵐ[P] Z :=
    Filter.Eventually.of_forall fun ω => sq_nonneg _
  have hCentered : MemLp (fun ω => X ω - P[X]) 2 P := by
    change MemLp (X - fun _ : Ω => P[X]) 2 P
    exact hX.sub (memLp_const (P[X]) : MemLp (fun _ : Ω => P[X]) 2 P)
  have hShift : MemLp (fun ω => X ω - P[X] + t) 2 P := by
    change MemLp ((fun ω => X ω - P[X]) + fun _ : Ω => t) 2 P
    exact hCentered.add (memLp_const t : MemLp (fun _ : Ω => t) 2 P)
  have hZ_int : Integrable Z P := by
    simpa [Z] using hShift.integrable_sq
  have hbase_pos : 0 < a + t := add_pos_of_pos_of_nonneg ha ht_nonneg
  have hthreshold_pos : 0 < (a + t) ^ 2 := sq_pos_of_pos hbase_pos
  have hMarkov :
      P.real {ω | (a + t) ^ 2 ≤ Z ω} ≤ (∫ ω, Z ω ∂P) / (a + t) ^ 2 :=
    thm_10_3 P Z hZ_nonneg hZ_int hthreshold_pos
  have hsubset : {ω | a ≤ X ω - P[X]} ⊆ {ω | (a + t) ^ 2 ≤ Z ω} := by
    intro ω hω
    change a ≤ X ω - P[X] at hω
    dsimp [Z]
    have hleft_nonneg : 0 ≤ a + t := hbase_pos.le
    have hle : a + t ≤ X ω - P[X] + t := by linarith
    have hright_nonneg : 0 ≤ X ω - P[X] + t := hleft_nonneg.trans hle
    exact sq_le_sq.mpr (by
      rw [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg]
      exact hle)
  have hmeasure :
      P.real {ω | a ≤ X ω - P[X]} ≤ P.real {ω | (a + t) ^ 2 ≤ Z ω} :=
    measureReal_mono (μ := P) hsubset
  have hZint : (∫ ω, Z ω ∂P) = v + t ^ 2 := by
    dsimp [Z, v]
    exact prob_11_2_shifted_square_integral P hXm hX t
  have halg : (v + t ^ 2) / (a + t) ^ 2 = v / (v + a ^ 2) := by
    dsimp [t]
    have ha_ne : a ≠ 0 := ne_of_gt ha
    have hden_ne : v + a ^ 2 ≠ 0 := by positivity
    field_simp [ha_ne, hden_ne]
    ring
  calc
    P.real {ω | a ≤ X ω - P[X]}
        ≤ P.real {ω | (a + t) ^ 2 ≤ Z ω} := hmeasure
    _ ≤ (∫ ω, Z ω ∂P) / (a + t) ^ 2 := hMarkov
    _ = (v + t ^ 2) / (a + t) ^ 2 := by rw [hZint]
    _ = v / (v + a ^ 2) := halg



theorem prob_11_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hXm : Measurable X) (hX : MemLp X 2 P)
    {a : ℝ} (ha : 0 ≤ a)
    (hden : 0 < _root_.variance P X (FiniteAbsMoment.of_memLp hXm hX) + a ^ 2) :
    P.real {ω | a ≤ X ω - P[X]} ≤
      _root_.variance P X (FiniteAbsMoment.of_memLp hXm hX) /
        (_root_.variance P X (FiniteAbsMoment.of_memLp hXm hX) + a ^ 2) := by
  by_cases hapos : 0 < a
  · exact prob_11_2_positive P X hXm hX hapos
  · have ha0 : a = 0 := le_antisymm (le_of_not_gt hapos) ha
    have hvpos :
        0 < _root_.variance P X (FiniteAbsMoment.of_memLp hXm hX) := by
      simpa [ha0] using hden
    have hprob : P.real {ω | a ≤ X ω - P[X]} ≤ 1 := by
      have hsub : {ω | a ≤ X ω - P[X]} ⊆ (Set.univ : Set Ω) := Set.subset_univ _
      have hm := measureReal_mono (μ := P) hsub
      simpa using hm
    have hfrac :
        _root_.variance P X (FiniteAbsMoment.of_memLp hXm hX) /
            (_root_.variance P X (FiniteAbsMoment.of_memLp hXm hX) + a ^ 2) = 1 := by
      rw [ha0]
      simpa using div_self (ne_of_gt hvpos)
    simpa [hfrac] using hprob
