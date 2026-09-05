/-
TASK ID: ex_10_3_1
TYPE: Example_Proof
SOURCE PLAN: chapter10-distribution-total-variation
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_10.def_10_4
import ProbabilityTheory.chapter_10.def_10_5




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

 
def ex_10_3_1_empiricalPoint (n k : ℕ) : ℝ :=
  ((k + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)

 
def ex_10_3_1_atomFinset (n : ℕ) : Finset ℝ :=
  (Finset.range (n + 1)).image (fun k => ex_10_3_1_empiricalPoint n k)

def ex_10_3_1_atomSet (n : ℕ) : Set ℝ :=
  ↑(ex_10_3_1_atomFinset n)

 
def ex_10_3_1_empiricalCDF (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    if ex_10_3_1_empiricalPoint n k ≤ x then
      (1 : ℝ) / ((n + 1 : ℕ) : ℝ)
    else
      0

 
def ex_10_3_1_floorRatio (n : ℕ) (x : ℝ) : ℝ :=
  (⌊x * ((n + 1 : ℕ) : ℝ)⌋₊ : ℝ) / ((n + 1 : ℕ) : ℝ)

 
def ex_10_3_1_floorCDF (n : ℕ) (x : ℝ) : ℝ :=
  if x < 0 then 0 else if x ≤ 1 then ex_10_3_1_floorRatio n x else 1

 
def ex_10_3_1_uniformCDF (x : ℝ) : ℝ :=
  if x < 0 then 0 else if x ≤ 1 then x else 1

 
def ex_10_3_1_empiricalMeasure (n : ℕ) : Measure ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (ENNReal.ofReal ((1 : ℝ) / ((n + 1 : ℕ) : ℝ))) •
      Measure.dirac (ex_10_3_1_empiricalPoint n k)

 
def ex_10_3_1_uniformMeasure : Measure ℝ :=
  volume.restrict (Icc (0 : ℝ) 1)

theorem ex_10_3_1_atomSet_countable (n : ℕ) :
    (ex_10_3_1_atomSet n).Countable := by
  exact Finset.countable_toSet (ex_10_3_1_atomFinset n)

theorem ex_10_3_1_atomSet_measurable (n : ℕ) :
    MeasurableSet (ex_10_3_1_atomSet n) := by
  exact (ex_10_3_1_atomSet_countable n).measurableSet

theorem ex_10_3_1_volume_atomSet_zero (n : ℕ) :
    volume (ex_10_3_1_atomSet n) = 0 := by
  exact (ex_10_3_1_atomSet_countable n).measure_zero volume

theorem ex_10_3_1_empirical_weight_sum (n : ℕ) :
    (∑ _k ∈ Finset.range (n + 1),
      ENNReal.ofReal ((1 : ℝ) / ((n + 1 : ℕ) : ℝ))) = 1 := by
  have hpos : 0 < ((n : ℝ) + 1) := by positivity
  have hcast : ENNReal.ofReal ((n : ℝ) + 1) = (n : ENNReal) + 1 := by
    rw [ENNReal.ofReal_add]
    · rw [ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    · positivity
    · positivity
  have hneE : ((n : ENNReal) + 1) ≠ 0 := by positivity
  have htopE : ((n : ENNReal) + 1) ≠ ⊤ := by
    rw [← hcast]
    exact ENNReal.ofReal_ne_top
  simp only [Nat.cast_add, Nat.cast_one, one_div, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  rw [ENNReal.ofReal_inv_of_pos hpos]
  rw [hcast]
  exact ENNReal.mul_inv_cancel hneE htopE

theorem ex_10_3_1_empiricalCDF_of_neg (n : ℕ) {x : ℝ} (hx : x < 0) :
    ex_10_3_1_empiricalCDF n x = 0 := by
  rw [ex_10_3_1_empiricalCDF]
  refine Finset.sum_eq_zero ?_
  intro k _hk
  have hpos : 0 < ex_10_3_1_empiricalPoint n k := by
    rw [ex_10_3_1_empiricalPoint]
    positivity
  have hxp : x < ex_10_3_1_empiricalPoint n k := by linarith
  simp [not_le_of_gt hxp]

theorem ex_10_3_1_empiricalCDF_of_one_lt (n : ℕ) {x : ℝ} (hx : 1 < x) :
    ex_10_3_1_empiricalCDF n x = 1 := by
  rw [ex_10_3_1_empiricalCDF]
  calc
    (∑ k ∈ Finset.range (n + 1),
        if ex_10_3_1_empiricalPoint n k ≤ x then
          (1 : ℝ) / ((n + 1 : ℕ) : ℝ)
        else
          0)
        = ∑ _k ∈ Finset.range (n + 1), (1 : ℝ) / ((n + 1 : ℕ) : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hklt : k < n + 1 := Finset.mem_range.mp hk
          have hnumle : ((k + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.succ_le_of_lt hklt
          have hdenpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
          have hptle : ex_10_3_1_empiricalPoint n k ≤ 1 := by
            rw [ex_10_3_1_empiricalPoint]
            rw [div_le_one₀ hdenpos]
            exact hnumle
          have hle : ex_10_3_1_empiricalPoint n k ≤ x := hptle.trans hx.le
          simp [hle]
    _ = 1 := by
      have hne : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      simp
      field_simp [hne]

theorem ex_10_3_1_floorCDF_on_unit_interval
    (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ex_10_3_1_floorCDF n x = ex_10_3_1_floorRatio n x := by
  simp [ex_10_3_1_floorCDF, not_lt_of_ge hx0, hx1]

theorem ex_10_3_1_empiricalCDF_eq_floorRatio_on_unit_interval
    (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ex_10_3_1_empiricalCDF n x = ex_10_3_1_floorRatio n x := by
  let q : ℕ := ⌊x * ((n + 1 : ℕ) : ℝ)⌋₊
  have hdenpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hprod_nonneg : 0 ≤ x * ((n + 1 : ℕ) : ℝ) := by positivity
  have hq_le : q ≤ n + 1 := by
    have hreal : (q : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      have hfloor : (q : ℝ) ≤ x * ((n + 1 : ℕ) : ℝ) := by
        simpa [q] using (Nat.floor_le hprod_nonneg)
      have hxmul : x * ((n + 1 : ℕ) : ℝ) ≤
          1 * ((n + 1 : ℕ) : ℝ) := by
        exact mul_le_mul_of_nonneg_right hx1 hdenpos.le
      simpa using hfloor.trans hxmul
    exact_mod_cast hreal
  have hfilter :
      (Finset.range (n + 1)).filter
          (fun k => ex_10_3_1_empiricalPoint n k ≤ x) = Finset.range q := by
    apply Finset.ext
    intro k
    constructor
    · intro hk
      rw [Finset.mem_filter] at hk
      have hle_mul : ((k + 1 : ℕ) : ℝ) ≤ x * ((n + 1 : ℕ) : ℝ) := by
        rw [ex_10_3_1_empiricalPoint] at hk
        exact (div_le_iff₀ hdenpos).mp hk.2
      have hsucc : k + 1 ≤ q := by
        simpa [q] using (Nat.le_floor hle_mul)
      exact Finset.mem_range.mpr (Nat.lt_of_succ_le hsucc)
    · intro hk
      have hkq : k < q := Finset.mem_range.mp hk
      have hkm : k < n + 1 := lt_of_lt_of_le hkq hq_le
      rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_range.mpr hkm
      · have hsucc : k + 1 ≤ q := Nat.succ_le_of_lt hkq
        have hle_mul : ((k + 1 : ℕ) : ℝ) ≤ x * ((n + 1 : ℕ) : ℝ) := by
          have hcast : ((k + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hsucc
          exact hcast.trans (by simpa [q] using (Nat.floor_le hprod_nonneg))
        rw [ex_10_3_1_empiricalPoint]
        exact (div_le_iff₀ hdenpos).mpr hle_mul
  rw [ex_10_3_1_empiricalCDF, ex_10_3_1_floorRatio]
  calc
    (∑ k ∈ Finset.range (n + 1),
        if ex_10_3_1_empiricalPoint n k ≤ x then
          (1 : ℝ) / ((n + 1 : ℕ) : ℝ)
        else 0)
        = ∑ k ∈ (Finset.range (n + 1)).filter
            (fun k => ex_10_3_1_empiricalPoint n k ≤ x),
            (1 : ℝ) / ((n + 1 : ℕ) : ℝ) := by
          rw [Finset.sum_filter]
    _ = ∑ k ∈ Finset.range q, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) := by
          rw [hfilter]
    _ = (q : ℝ) / ((n + 1 : ℕ) : ℝ) := by
          simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    _ = (⌊x * ((n + 1 : ℕ) : ℝ)⌋₊ : ℝ) /
          ((n + 1 : ℕ) : ℝ) := by
          rfl

theorem ex_10_3_1_floorRatio_tendsto (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => ex_10_3_1_floorRatio n x) atTop (nhds x) := by
  rcases eq_or_lt_of_le hx with hxzero | hxpos
  · subst x
    simp [ex_10_3_1_floorRatio]
  · have hSucc : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
      exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hArg : Tendsto (fun n : ℕ => x * ((n + 1 : ℕ) : ℝ)) atTop atTop := by
      exact hSucc.const_mul_atTop hxpos
    have hFloor :
        Tendsto
          (fun n : ℕ => (⌊x * ((n + 1 : ℕ) : ℝ)⌋₊ : ℝ) /
            (x * ((n + 1 : ℕ) : ℝ)))
          atTop (nhds (1 : ℝ)) := by
      change Tendsto
        ((fun y : ℝ => (⌊y⌋₊ : ℝ) / y) ∘
          fun n : ℕ => x * ((n + 1 : ℕ) : ℝ))
        atTop (nhds (1 : ℝ))
      exact (tendsto_nat_floor_div_atTop (R := ℝ)).comp hArg
    have hScaled :
        Tendsto
          (fun n : ℕ => x * ((⌊x * ((n + 1 : ℕ) : ℝ)⌋₊ : ℝ) /
            (x * ((n + 1 : ℕ) : ℝ))))
          atTop (nhds (x * (1 : ℝ))) := hFloor.const_mul x
    have hTarget :
        Tendsto (fun n : ℕ => ex_10_3_1_floorRatio n x)
          atTop (nhds (x * (1 : ℝ))) := by
      refine hScaled.congr' ?_
      filter_upwards with n
      have hxne : x ≠ 0 := ne_of_gt hxpos
      have hnne : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      simp [ex_10_3_1_floorRatio]
      field_simp [hxne, hnne]
    simpa using hTarget

theorem ex_10_3_1_empiricalMeasure_atomSet (n : ℕ) :
    ex_10_3_1_empiricalMeasure n (ex_10_3_1_atomSet n) = 1 := by
  rw [ex_10_3_1_empiricalMeasure]
  rw [Measure.coe_finset_sum]
  simp only [Finset.sum_apply, Measure.smul_apply]
  calc
    (∑ k ∈ Finset.range (n + 1),
        ENNReal.ofReal (1 / ↑(n + 1)) •
          Measure.dirac (ex_10_3_1_empiricalPoint n k) (ex_10_3_1_atomSet n))
        = ∑ _k ∈ Finset.range (n + 1),
            ENNReal.ofReal (1 / ↑(n + 1 : ℕ)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hmem : ex_10_3_1_empiricalPoint n k ∈ ex_10_3_1_atomSet n := by
            exact Finset.mem_coe.mpr
              (Finset.mem_image_of_mem (fun k => ex_10_3_1_empiricalPoint n k) hk)
          simp [Measure.dirac_apply_of_mem hmem]
    _ = 1 := ex_10_3_1_empirical_weight_sum n

theorem ex_10_3_1_empiricalMeasure_univ (n : ℕ) :
    ex_10_3_1_empiricalMeasure n univ = 1 := by
  rw [ex_10_3_1_empiricalMeasure]
  rw [Measure.coe_finset_sum]
  simp only [Finset.sum_apply, Measure.smul_apply]
  calc
    (∑ k ∈ Finset.range (n + 1),
        ENNReal.ofReal (1 / ↑(n + 1)) •
          Measure.dirac (ex_10_3_1_empiricalPoint n k) univ)
        = ∑ _k ∈ Finset.range (n + 1),
            ENNReal.ofReal (1 / ↑(n + 1 : ℕ)) := by
          refine Finset.sum_congr rfl ?_
          intro _k _hk
          simp
    _ = 1 := ex_10_3_1_empirical_weight_sum n

theorem ex_10_3_1_empiricalMeasure_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (ex_10_3_1_empiricalMeasure n) := by
  exact ⟨ex_10_3_1_empiricalMeasure_univ n⟩

theorem ex_10_3_1_uniformMeasure_univ :
    ex_10_3_1_uniformMeasure univ = 1 := by
  rw [ex_10_3_1_uniformMeasure, Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

theorem ex_10_3_1_uniformMeasure_isProbabilityMeasure :
    IsProbabilityMeasure ex_10_3_1_uniformMeasure := by
  exact ⟨ex_10_3_1_uniformMeasure_univ⟩

def ex_10_3_1_empiricalLaw (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨ex_10_3_1_empiricalMeasure n,
    ex_10_3_1_empiricalMeasure_isProbabilityMeasure n⟩

def ex_10_3_1_uniformLaw : ProbabilityMeasure ℝ :=
  ⟨ex_10_3_1_uniformMeasure, ex_10_3_1_uniformMeasure_isProbabilityMeasure⟩

theorem ex_10_3_1_uniformMeasure_atomSet_zero (n : ℕ) :
    ex_10_3_1_uniformMeasure (ex_10_3_1_atomSet n) = 0 := by
  rw [ex_10_3_1_uniformMeasure,
    Measure.restrict_apply (ex_10_3_1_atomSet_measurable n)]
  exact measure_mono_null inter_subset_left (ex_10_3_1_volume_atomSet_zero n)

theorem ex_10_3_1_atomSet_witness_abs (n : ℕ) :
    |(ex_10_3_1_empiricalMeasure n).real (ex_10_3_1_atomSet n) -
      ex_10_3_1_uniformMeasure.real (ex_10_3_1_atomSet n)| = 1 := by
  rw [Measure.real_def, Measure.real_def,
    ex_10_3_1_empiricalMeasure_atomSet,
    ex_10_3_1_uniformMeasure_atomSet_zero]
  norm_num

lemma ex_10_3_1_totalVariationDistance_event_bound
    {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (A : Set Ω) (hA : MeasurableSet A) :
    |P.real A - Q.real A| ≤ totalVariationDistance P Q := by
  unfold totalVariationDistance
  let S : Set ℝ :=
    {d : ℝ | ∃ A : Set Ω, MeasurableSet A ∧ d = |P.real A - Q.real A|}
  have hbounded : BddAbove S := by
    refine ⟨1, ?_⟩
    intro d hd
    rcases hd with ⟨B, _hB, rfl⟩
    have hP0 : 0 ≤ P.real B := measureReal_nonneg
    have hQ0 : 0 ≤ Q.real B := measureReal_nonneg
    have hP1 : P.real B ≤ 1 := by
      rw [Measure.real_def]
      have hB : P B ≤ P univ := measure_mono (subset_univ B)
      have hfin : P univ ≠ ⊤ := measure_ne_top P univ
      calc
        (P B).toReal ≤ (P univ).toReal := ENNReal.toReal_mono hfin hB
        _ = 1 := by rw [measure_univ]; norm_num
    have hQ1 : Q.real B ≤ 1 := by
      rw [Measure.real_def]
      have hB : Q B ≤ Q univ := measure_mono (subset_univ B)
      have hfin : Q univ ≠ ⊤ := measure_ne_top Q univ
      calc
        (Q B).toReal ≤ (Q univ).toReal := ENNReal.toReal_mono hfin hB
        _ = 1 := by rw [measure_univ]; norm_num
    exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have hmem : |P.real A - Q.real A| ∈ S := ⟨A, hA, rfl⟩
  exact le_csSup hbounded hmem

theorem ex_10_3_1_totalVariationDistance_ge_one (n : ℕ) :
    1 ≤ totalVariationDistance
      (ex_10_3_1_empiricalMeasure n) ex_10_3_1_uniformMeasure := by
  haveI : IsProbabilityMeasure (ex_10_3_1_empiricalMeasure n) :=
    ex_10_3_1_empiricalMeasure_isProbabilityMeasure n
  haveI : IsProbabilityMeasure ex_10_3_1_uniformMeasure :=
    ex_10_3_1_uniformMeasure_isProbabilityMeasure
  simpa [ex_10_3_1_atomSet_witness_abs n] using
    ex_10_3_1_totalVariationDistance_event_bound
      (ex_10_3_1_empiricalMeasure n) ex_10_3_1_uniformMeasure
      (ex_10_3_1_atomSet n) (ex_10_3_1_atomSet_measurable n)

theorem ex_10_3_1_not_totalVariation :
    ¬ MeasuresConvergeInTotalVariation
      (fun n : ℕ => ex_10_3_1_empiricalMeasure n)
      ex_10_3_1_uniformMeasure := by
  intro hTV
  rw [MeasuresConvergeInTotalVariation] at hTV
  rcases hTV with ⟨hPn, hP, hlim⟩
  letI (n : ℕ) : IsProbabilityMeasure (ex_10_3_1_empiricalMeasure n) := hPn n
  letI : IsProbabilityMeasure ex_10_3_1_uniformMeasure := hP
  have hlt :
      ∀ᶠ n : ℕ in atTop,
        totalVariationDistance
          (ex_10_3_1_empiricalMeasure n) ex_10_3_1_uniformMeasure < (1 / 2 : ℝ) := by
    exact hlim (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hge :
      ∀ᶠ n : ℕ in atTop,
        (1 : ℝ) ≤ totalVariationDistance
          (ex_10_3_1_empiricalMeasure n) ex_10_3_1_uniformMeasure :=
    Filter.Eventually.of_forall ex_10_3_1_totalVariationDistance_ge_one
  rcases (hlt.and hge).exists with ⟨_n, hnlt, hnge⟩
  linarith

theorem ex_10_3_1_measureCdf_empiricalMeasure (n : ℕ) (x : ℝ) :
    measureCdf (ex_10_3_1_empiricalLaw n) x =
      ex_10_3_1_empiricalCDF n x := by
  change (ex_10_3_1_empiricalMeasure n).real (Iic x) =
    ex_10_3_1_empiricalCDF n x
  rw [ex_10_3_1_empiricalCDF, Measure.real_def, ex_10_3_1_empiricalMeasure]
  rw [Measure.coe_finset_sum]
  simp only [Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl ?_
    intro k _hk
    by_cases hle : ex_10_3_1_empiricalPoint n k ≤ x
    · have hmem : ex_10_3_1_empiricalPoint n k ∈ Iic x := hle
      rw [Measure.dirac_apply_of_mem hmem]
      rw [ENNReal.toReal_mul]
      simp only [ENNReal.toReal_one, mul_one]
      have hnonneg : 0 ≤ (1 : ℝ) / ((n + 1 : ℕ) : ℝ) := by positivity
      rw [ENNReal.toReal_ofReal hnonneg]
      simp [hle]
    · have hnotmem : ex_10_3_1_empiricalPoint n k ∉ Iic x := hle
      simp [hle, hnotmem]
  · intro _k _hk
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

theorem ex_10_3_1_measureCdf_uniformMeasure (x : ℝ) :
    measureCdf ex_10_3_1_uniformLaw x = ex_10_3_1_uniformCDF x := by
  change ex_10_3_1_uniformMeasure.real (Iic x) =
    ex_10_3_1_uniformCDF x
  by_cases hxneg : x < 0
  · have hinter : Iic x ∩ Icc (0 : ℝ) 1 = ∅ := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨hyx, hy0, _hy1⟩
        have hyxle : y ≤ x := hyx
        linarith
      · intro hy
        simp at hy
    rw [ex_10_3_1_uniformMeasure, Measure.real_def,
      Measure.restrict_apply measurableSet_Iic, hinter, measure_empty]
    simp [ex_10_3_1_uniformCDF, hxneg]
  · have hx0 : 0 ≤ x := le_of_not_gt hxneg
    by_cases hx1 : x ≤ 1
    · have hinter : Iic x ∩ Icc (0 : ℝ) 1 = Icc (0 : ℝ) x := by
        ext y
        constructor
        · intro hy
          rcases hy with ⟨hyx, hy0, _hy1⟩
          have hyxle : y ≤ x := hyx
          exact ⟨hy0, hyxle⟩
        · intro hy
          rcases hy with ⟨hy0, hyx⟩
          exact ⟨hyx, hy0, hyx.trans hx1⟩
      rw [ex_10_3_1_uniformMeasure, Measure.real_def,
        Measure.restrict_apply measurableSet_Iic, hinter, Real.volume_Icc]
      have hnonneg : 0 ≤ x - 0 := by linarith
      rw [ENNReal.toReal_ofReal hnonneg]
      simp [ex_10_3_1_uniformCDF, hxneg, hx1]
    · have hxgt : 1 < x := lt_of_not_ge hx1
      have hinter : Iic x ∩ Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := by
        ext y
        constructor
        · intro hy
          exact hy.2
        · intro hy
          exact ⟨hy.2.trans hxgt.le, hy⟩
      rw [ex_10_3_1_uniformMeasure, Measure.real_def,
        Measure.restrict_apply measurableSet_Iic, hinter, Real.volume_Icc]
      norm_num [ex_10_3_1_uniformCDF, hxneg, hx1]

theorem ex_10_3_1_distribution_convergence :
    MeasuresConvergeInDistribution
      ex_10_3_1_empiricalLaw ex_10_3_1_uniformLaw := by
  rw [measuresConvergeInDistribution_iff_cdf]
  intro x _hcont
  have hUniform := ex_10_3_1_measureCdf_uniformMeasure x
  by_cases hxneg : x < 0
  · have htarget : measureCdf ex_10_3_1_uniformLaw x = 0 := by
      simpa [ex_10_3_1_uniformCDF, hxneg] using hUniform
    rw [htarget]
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards with n
    rw [ex_10_3_1_measureCdf_empiricalMeasure n x,
      ex_10_3_1_empiricalCDF_of_neg n hxneg]
  · have hx0 : 0 ≤ x := le_of_not_gt hxneg
    by_cases hx1 : x ≤ 1
    · have htarget : measureCdf ex_10_3_1_uniformLaw x = x := by
        simpa [ex_10_3_1_uniformCDF, hxneg, hx1] using hUniform
      rw [htarget]
      refine Filter.Tendsto.congr' ?_ (ex_10_3_1_floorRatio_tendsto x hx0)
      filter_upwards with n
      rw [ex_10_3_1_measureCdf_empiricalMeasure n x,
        ex_10_3_1_empiricalCDF_eq_floorRatio_on_unit_interval n hx0 hx1]
    · have hxgt : 1 < x := lt_of_not_ge hx1
      have htarget : measureCdf ex_10_3_1_uniformLaw x = 1 := by
        simpa [ex_10_3_1_uniformCDF, hxneg, hx1] using hUniform
      rw [htarget]
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards with n
      rw [ex_10_3_1_measureCdf_empiricalMeasure n x,
        ex_10_3_1_empiricalCDF_of_one_lt n hxgt]

theorem ex_10_3_1_distribution_not_totalVariation :
    MeasuresConvergeInDistribution
        ex_10_3_1_empiricalLaw ex_10_3_1_uniformLaw ∧
      ¬ MeasuresConvergeInTotalVariation
        (fun n : ℕ => ex_10_3_1_empiricalMeasure n)
        ex_10_3_1_uniformMeasure := by
  exact ⟨ex_10_3_1_distribution_convergence, ex_10_3_1_not_totalVariation⟩

theorem ex_10_3_1 :
    MeasuresConvergeInDistribution
        ex_10_3_1_empiricalLaw ex_10_3_1_uniformLaw ∧
    ¬ MeasuresConvergeInTotalVariation
      (fun n : ℕ => ex_10_3_1_empiricalMeasure n)
      ex_10_3_1_uniformMeasure := by
  exact ex_10_3_1_distribution_not_totalVariation

end
