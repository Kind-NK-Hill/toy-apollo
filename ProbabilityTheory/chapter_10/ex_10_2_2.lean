/-
TASK ID: ex_10_2_2
TYPE: Example_Proof
SOURCE PLAN: chapter10-mean
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_10.def_10_1
import ProbabilityTheory.chapter_10.def_10_3




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set
open scoped Topology ENNReal

noncomputable section



def ex_10_2_2_unitIntervalMeasure : Measure ℝ :=
  volume.restrict (Icc (0 : ℝ) 1)

 
def ex_10_2_2_textbookIndex (n : ℕ) : ℕ :=
  n + 1



def ex_10_2_2_level (n : ℕ) : ℕ :=
  Nat.log2 (ex_10_2_2_textbookIndex n)

 
def ex_10_2_2_blockStart (n : ℕ) : ℕ :=
  2 ^ ex_10_2_2_level n

 
def ex_10_2_2_position (n : ℕ) : ℕ :=
  ex_10_2_2_textbookIndex n - ex_10_2_2_blockStart n

 
def ex_10_2_2_width (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ ex_10_2_2_level n)⁻¹

 
def ex_10_2_2_left (n : ℕ) : ℝ :=
  (ex_10_2_2_position n : ℝ) * ex_10_2_2_width n

 
def ex_10_2_2_right (n : ℕ) : ℝ :=
  ((ex_10_2_2_position n : ℝ) + 1) * ex_10_2_2_width n

 
def ex_10_2_2_event (n : ℕ) : Set ℝ :=
  Icc (ex_10_2_2_left n) (ex_10_2_2_right n)

 
def ex_10_2_2_sequence (n : ℕ) (ω : ℝ) : ℝ :=
  (ex_10_2_2_event n).indicator (fun _ => (1 : ℝ)) ω

 
def ex_10_2_2_zero : ℝ → ℝ :=
  fun _ => 0

 
def ex_10_2_2_blockIndices (m : ℕ) : Set ℕ :=
  {n : ℕ | 2 ^ m - 1 ≤ n ∧ n < 2 ^ (m + 1) - 1}



def ex_10_2_2_blockCoversSource : Prop :=
  ∀ m : ℕ,
    Icc (0 : ℝ) 1 ⊆
      ⋃ n : ℕ, ⋃ _ : n ∈ ex_10_2_2_blockIndices m, ex_10_2_2_event n

 
def ex_10_2_2_eventMeasureFormula : Prop :=
  ∀ n : ℕ,
    ex_10_2_2_unitIntervalMeasure (ex_10_2_2_event n) =
      ENNReal.ofReal (ex_10_2_2_width n)



def ex_10_2_2_infinitelyManyHits : Prop :=
  ∀ ω ∈ Icc (0 : ℝ) 1, ∀ N : ℕ,
    ∃ n ≥ N, ex_10_2_2_sequence n ω = 1



def ex_10_2_2_meanMomentFormula : Prop :=
  ∀ n : ℕ,
    meanDeviationMoment ex_10_2_2_unitIntervalMeasure
      ex_10_2_2_sequence ex_10_2_2_zero 1 n =
        ex_10_2_2_unitIntervalMeasure (ex_10_2_2_event n)



def ex_10_2_2_sourceConclusion : Prop :=
  ConvergesInMean ex_10_2_2_unitIntervalMeasure
      ex_10_2_2_sequence ex_10_2_2_zero ∧
    ¬ ConvergesAlmostSurely ex_10_2_2_unitIntervalMeasure
      ex_10_2_2_sequence ex_10_2_2_zero



def ex_10_2_2_sourceRoute : Prop :=
  ex_10_2_2_blockCoversSource ∧
    ex_10_2_2_eventMeasureFormula ∧
      ex_10_2_2_infinitelyManyHits ∧
        ex_10_2_2_meanMomentFormula ∧
          ex_10_2_2_sourceConclusion

theorem ex_10_2_2_event_measurable (n : ℕ) :
    MeasurableSet (ex_10_2_2_event n) := by
  unfold ex_10_2_2_event
  exact measurableSet_Icc

theorem ex_10_2_2_measure_univ :
    ex_10_2_2_unitIntervalMeasure Set.univ = 1 := by
  unfold ex_10_2_2_unitIntervalMeasure
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc]
  norm_num

theorem ex_10_2_2_unitIntervalMeasure_Icc_eq {a b : ℝ}
    (h0 : 0 ≤ a) (_hab : a ≤ b) (h1 : b ≤ 1) :
    ex_10_2_2_unitIntervalMeasure (Icc a b) = ENNReal.ofReal (b - a) := by
  unfold ex_10_2_2_unitIntervalMeasure
  rw [Measure.restrict_apply measurableSet_Icc]
  have hinter : Icc a b ∩ Icc (0 : ℝ) 1 = Icc a b := by
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hx
      exact ⟨hx, ⟨h0.trans hx.1, hx.2.trans h1⟩⟩
  rw [hinter, Real.volume_Icc]

theorem ex_10_2_2_level_eq_of_block {m j : ℕ} (hj : j < 2 ^ m) :
    ex_10_2_2_level (2 ^ m - 1 + j) = m := by
  unfold ex_10_2_2_level ex_10_2_2_textbookIndex
  rw [Nat.log2_eq_log_two]
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · have hpos : 0 < 2 ^ m := by positivity
    omega
  · rw [pow_succ]
    have hpos : 0 < 2 ^ m := by positivity
    omega

theorem ex_10_2_2_position_eq_of_block {m j : ℕ} (hj : j < 2 ^ m) :
    ex_10_2_2_position (2 ^ m - 1 + j) = j := by
  unfold ex_10_2_2_position ex_10_2_2_textbookIndex ex_10_2_2_blockStart
  rw [ex_10_2_2_level_eq_of_block hj]
  have hpos : 0 < 2 ^ m := by positivity
  omega

theorem ex_10_2_2_block_mem_of_position {m j : ℕ} (hj : j < 2 ^ m) :
    2 ^ m - 1 + j ∈ ex_10_2_2_blockIndices m := by
  unfold ex_10_2_2_blockIndices
  constructor
  · omega
  · rw [pow_succ]
    have hpos : 0 < 2 ^ m := by positivity
    omega

theorem ex_10_2_2_event_eq_of_block {m j : ℕ} (hj : j < 2 ^ m) :
    ex_10_2_2_event (2 ^ m - 1 + j) =
      Icc ((j : ℝ) * ((2 : ℝ) ^ m)⁻¹)
        (((j : ℝ) + 1) * ((2 : ℝ) ^ m)⁻¹) := by
  simp [ex_10_2_2_event, ex_10_2_2_left, ex_10_2_2_right,
    ex_10_2_2_width, ex_10_2_2_level_eq_of_block hj,
    ex_10_2_2_position_eq_of_block hj]

theorem ex_10_2_2_exists_dyadic_cell (m : ℕ) {ω : ℝ}
    (hω : ω ∈ Icc (0 : ℝ) 1) :
    ∃ j : ℕ, j < 2 ^ m ∧
      ω ∈ Icc ((j : ℝ) * ((2 : ℝ) ^ m)⁻¹)
        (((j : ℝ) + 1) * ((2 : ℝ) ^ m)⁻¹) := by
  by_cases htop : ω = 1
  · refine ⟨2 ^ m - 1, ?_, ?_⟩
    · have hpos : 0 < 2 ^ m := by positivity
      omega
    · rw [htop]
      constructor
      · have hpowposR : 0 < (2 : ℝ) ^ m := by positivity
        have hle : ((2 ^ m - 1 : ℕ) : ℝ) ≤ (2 ^ m : ℕ) := by
          exact_mod_cast Nat.sub_le (2 ^ m) 1
        calc
          ((2 ^ m - 1 : ℕ) : ℝ) * ((2 : ℝ) ^ m)⁻¹
              ≤ ((2 ^ m : ℕ) : ℝ) * ((2 : ℝ) ^ m)⁻¹ := by
                exact mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr hpowposR.le)
          _ = 1 := by
                norm_num [mul_inv_cancel₀ hpowposR.ne']
      · have hpowposR : 0 < (2 : ℝ) ^ m := by positivity
        have hpowposN : 0 < 2 ^ m := by positivity
        have hcast : (((2 ^ m - 1 : ℕ) : ℝ) + 1) = ((2 ^ m : ℕ) : ℝ) := by
          exact_mod_cast Nat.sub_add_cancel (Nat.succ_le_of_lt hpowposN)
        rw [hcast]
        norm_num [mul_inv_cancel₀ hpowposR.ne']
  · have hlt : ω < 1 := lt_of_le_of_ne hω.2 htop
    let j : ℕ := Nat.floor (ω * (2 : ℝ) ^ m)
    refine ⟨j, ?_, ?_⟩
    · have hpowposR : 0 < (2 : ℝ) ^ m := by positivity
      have hnonneg : 0 ≤ ω * (2 : ℝ) ^ m := mul_nonneg hω.1 hpowposR.le
      have hltmul : ω * (2 : ℝ) ^ m < (2 : ℝ) ^ m := by
        simpa using (mul_lt_mul_of_pos_right hlt hpowposR)
      rw [Nat.floor_lt hnonneg]
      exact_mod_cast hltmul
    · constructor
      · have hpowposR : 0 < (2 : ℝ) ^ m := by positivity
        have hfloorle : (j : ℝ) ≤ ω * (2 : ℝ) ^ m :=
          Nat.floor_le (mul_nonneg hω.1 hpowposR.le)
        have hmul := mul_le_mul_of_nonneg_right hfloorle (inv_nonneg.mpr hpowposR.le)
        have hcancel : (ω * (2 : ℝ) ^ m) * ((2 : ℝ) ^ m)⁻¹ = ω := by
          field_simp [hpowposR.ne']
        calc
          (j : ℝ) * ((2 : ℝ) ^ m)⁻¹
              ≤ (ω * (2 : ℝ) ^ m) * ((2 : ℝ) ^ m)⁻¹ := hmul
          _ = ω := hcancel
      · have hpowposR : 0 < (2 : ℝ) ^ m := by positivity
        have hltfloor : ω * (2 : ℝ) ^ m < (j : ℝ) + 1 :=
          Nat.lt_floor_add_one (ω * (2 : ℝ) ^ m)
        have hmul :=
          mul_le_mul_of_nonneg_right (le_of_lt hltfloor) (inv_nonneg.mpr hpowposR.le)
        have hcancel : (ω * (2 : ℝ) ^ m) * ((2 : ℝ) ^ m)⁻¹ = ω := by
          field_simp [hpowposR.ne']
        calc
          ω = (ω * (2 : ℝ) ^ m) * ((2 : ℝ) ^ m)⁻¹ := hcancel.symm
          _ ≤ ((j : ℝ) + 1) * ((2 : ℝ) ^ m)⁻¹ := hmul

theorem ex_10_2_2_blockCoversSource_proved :
    ex_10_2_2_blockCoversSource := by
  intro m ω hω
  rcases ex_10_2_2_exists_dyadic_cell m hω with ⟨j, hj, hcell⟩
  refine mem_iUnion.2 ⟨2 ^ m - 1 + j, ?_⟩
  refine mem_iUnion.2 ⟨ex_10_2_2_block_mem_of_position hj, ?_⟩
  rw [ex_10_2_2_event_eq_of_block hj]
  exact hcell

theorem ex_10_2_2_level_lower (n : ℕ) :
    ex_10_2_2_blockStart n ≤ ex_10_2_2_textbookIndex n := by
  unfold ex_10_2_2_blockStart ex_10_2_2_level
  rw [Nat.log2_eq_log_two]
  exact Nat.pow_log_le_self 2 (by unfold ex_10_2_2_textbookIndex; omega)

theorem ex_10_2_2_level_upper (n : ℕ) :
    ex_10_2_2_textbookIndex n < 2 ^ (ex_10_2_2_level n + 1) := by
  unfold ex_10_2_2_level
  rw [Nat.log2_eq_log_two]
  exact Nat.lt_pow_succ_log_self (b := 2) (by norm_num)
    (ex_10_2_2_textbookIndex n)

theorem ex_10_2_2_position_succ_le_blockStart (n : ℕ) :
    ex_10_2_2_position n + 1 ≤ ex_10_2_2_blockStart n := by
  unfold ex_10_2_2_position
  have hlower := ex_10_2_2_level_lower n
  have hupper := ex_10_2_2_level_upper n
  have hupper' :
      ex_10_2_2_textbookIndex n < ex_10_2_2_blockStart n * 2 := by
    simpa [ex_10_2_2_blockStart, pow_succ, mul_comm, mul_left_comm, mul_assoc]
      using hupper
  omega

theorem ex_10_2_2_eventMeasureFormula_proved :
    ex_10_2_2_eventMeasureFormula := by
  intro n
  unfold ex_10_2_2_event
  have hpowpos : 0 < (2 : ℝ) ^ ex_10_2_2_level n := by positivity
  have hwidth_nonneg : 0 ≤ ex_10_2_2_width n := by
    unfold ex_10_2_2_width
    positivity
  have h0 : 0 ≤ ex_10_2_2_left n := by
    unfold ex_10_2_2_left
    positivity
  have hle : ex_10_2_2_left n ≤ ex_10_2_2_right n := by
    unfold ex_10_2_2_left ex_10_2_2_right
    exact mul_le_mul_of_nonneg_right (by norm_num) hwidth_nonneg
  have hright_le_one : ex_10_2_2_right n ≤ 1 := by
    unfold ex_10_2_2_right ex_10_2_2_width
    have hsucc := ex_10_2_2_position_succ_le_blockStart n
    have hcast :
        ((ex_10_2_2_position n : ℝ) + 1) ≤
          ((ex_10_2_2_blockStart n : ℕ) : ℝ) := by
      exact_mod_cast hsucc
    have hstart_cast :
        ((ex_10_2_2_blockStart n : ℕ) : ℝ) =
          (2 : ℝ) ^ ex_10_2_2_level n := by
      unfold ex_10_2_2_blockStart
      norm_num
    calc
      ((ex_10_2_2_position n : ℝ) + 1) *
            ((2 : ℝ) ^ ex_10_2_2_level n)⁻¹
          ≤ ((ex_10_2_2_blockStart n : ℕ) : ℝ) *
            ((2 : ℝ) ^ ex_10_2_2_level n)⁻¹ := by
              exact mul_le_mul_of_nonneg_right hcast (inv_nonneg.mpr hpowpos.le)
      _ = (2 : ℝ) ^ ex_10_2_2_level n *
            ((2 : ℝ) ^ ex_10_2_2_level n)⁻¹ := by
              rw [hstart_cast]
      _ = 1 := by
              exact mul_inv_cancel₀ hpowpos.ne'
  rw [ex_10_2_2_unitIntervalMeasure_Icc_eq h0 hle hright_le_one]
  congr 1
  unfold ex_10_2_2_left ex_10_2_2_right ex_10_2_2_width
  ring

theorem ex_10_2_2_sequence_is_indicator (n : ℕ) :
    ex_10_2_2_sequence n =
      fun ω : ℝ => (ex_10_2_2_event n).indicator (fun _ => (1 : ℝ)) ω := by
  rfl

theorem ex_10_2_2_infinitelyManyHits_of_blockCovers
    (hCover : ex_10_2_2_blockCoversSource) :
    ex_10_2_2_infinitelyManyHits := by
  intro ω hω N
  let m := N + 1
  have hstart : N ≤ 2 ^ m - 1 := by
    have hlt : N + 1 < 2 ^ (N + 1) := Nat.lt_two_pow_self (n := N + 1)
    dsimp [m]
    omega
  have hmemUnion :
      ω ∈
        ⋃ n : ℕ, ⋃ _ : n ∈ ex_10_2_2_blockIndices m, ex_10_2_2_event n :=
    hCover m hω
  rcases mem_iUnion.1 hmemUnion with ⟨n, hnUnion⟩
  rcases mem_iUnion.1 hnUnion with ⟨hnBlock, hnevent⟩
  refine ⟨n, ?_, ?_⟩
  · exact hstart.trans hnBlock.1
  · simp [ex_10_2_2_sequence, hnevent]

theorem ex_10_2_2_infinitelyManyHits_proved :
    ex_10_2_2_infinitelyManyHits :=
  ex_10_2_2_infinitelyManyHits_of_blockCovers
    ex_10_2_2_blockCoversSource_proved

theorem ex_10_2_2_meanDeviationMoment_eq_event_measure (n : ℕ) :
    meanDeviationMoment ex_10_2_2_unitIntervalMeasure
      ex_10_2_2_sequence ex_10_2_2_zero 1 n =
        ex_10_2_2_unitIntervalMeasure (ex_10_2_2_event n) := by
  unfold meanDeviationMoment ex_10_2_2_sequence ex_10_2_2_zero
  have hfun :
      (fun ω : ℝ =>
          ENNReal.ofReal
            (|(ex_10_2_2_event n).indicator (fun _ => (1 : ℝ)) ω - 0| ^ (1 : ℝ))) =
        fun ω : ℝ => (ex_10_2_2_event n).indicator (fun _ => (1 : ENNReal)) ω := by
    funext ω
    by_cases hω : ω ∈ ex_10_2_2_event n
    · simp [Set.indicator, hω, Real.rpow_one]
    · simp [Set.indicator, hω, Real.rpow_one]
  rw [hfun]
  rw [lintegral_indicator (ex_10_2_2_event_measurable n)]
  rw [lintegral_const]
  simp

theorem ex_10_2_2_not_tendsto_zero_of_infinite_ones {u : ℕ → ℝ}
    (hhit : ∀ N : ℕ, ∃ n ≥ N, u n = 1) :
    ¬ Tendsto u atTop (nhds (0 : ℝ)) := by
  intro hlim
  have hlt : ∀ᶠ n : ℕ in atTop, u n < (1 / 2 : ℝ) :=
    hlim.eventually_lt_const (by norm_num)
  rcases eventually_atTop.1 hlt with ⟨N, hN⟩
  rcases hhit N with ⟨n, hn, hone⟩
  have hbad : (1 : ℝ) < 1 / 2 := by
    simpa [hone] using hN n hn
  norm_num at hbad

theorem ex_10_2_2_pointwise_failure_of_infinitelyManyHits
    (hHits : ex_10_2_2_infinitelyManyHits) :
    ∀ ω ∈ Icc (0 : ℝ) 1,
      ¬ Tendsto (fun n : ℕ => ex_10_2_2_sequence n ω) atTop (nhds (0 : ℝ)) := by
  intro ω hω
  exact ex_10_2_2_not_tendsto_zero_of_infinite_ones (hHits ω hω)

theorem ex_10_2_2_not_almost_sure_of_pointwise_failure_on_unit
    (hbad : ∀ ω ∈ Icc (0 : ℝ) 1,
      ¬ Tendsto (fun n : ℕ => ex_10_2_2_sequence n ω) atTop (nhds (0 : ℝ))) :
    ¬ ConvergesAlmostSurely ex_10_2_2_unitIntervalMeasure
      ex_10_2_2_sequence ex_10_2_2_zero := by
  intro hAS
  have hbad_zero :
      ex_10_2_2_unitIntervalMeasure
        {ω : ℝ |
          ¬ Tendsto (fun n : ℕ => ex_10_2_2_sequence n ω) atTop (nhds (0 : ℝ))} = 0 :=
    ae_iff.1 hAS.2.2
  have hsub :
      Icc (0 : ℝ) 1 ⊆
        {ω : ℝ |
          ¬ Tendsto (fun n : ℕ => ex_10_2_2_sequence n ω) atTop (nhds (0 : ℝ))} := by
    intro ω hω
    exact hbad ω hω
  have hmono :=
    measure_mono hsub
      (μ := ex_10_2_2_unitIntervalMeasure)
  have hunit :
      ex_10_2_2_unitIntervalMeasure (Icc (0 : ℝ) 1) = 1 := by
    simpa using
      (ex_10_2_2_unitIntervalMeasure_Icc_eq
        (a := 0) (b := 1) (by norm_num) (by norm_num) (by norm_num))
  have hone_le_zero : (1 : ENNReal) ≤ 0 := by
    simpa [hunit, hbad_zero] using hmono
  exact (not_lt_of_ge hone_le_zero) zero_lt_one

theorem ex_10_2_2_meanMomentFormula_proved :
    ex_10_2_2_meanMomentFormula := by
  intro n
  exact ex_10_2_2_meanDeviationMoment_eq_event_measure n

theorem ex_10_2_2_level_tendsto_atTop :
    Tendsto ex_10_2_2_level atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro m
  refine ⟨2 ^ m - 1, ?_⟩
  intro n hn
  unfold ex_10_2_2_level
  rw [Nat.log2_eq_log_two]
  apply Nat.le_log_of_pow_le (b := 2) (by norm_num)
  unfold ex_10_2_2_textbookIndex
  have hpos : 0 < 2 ^ m := by positivity
  omega

theorem ex_10_2_2_width_eq_pow (n : ℕ) :
    ENNReal.ofReal (ex_10_2_2_width n) =
      ((2 : ENNReal)⁻¹) ^ ex_10_2_2_level n := by
  unfold ex_10_2_2_width
  rw [ENNReal.ofReal_inv_of_pos]
  · rw [ENNReal.ofReal_pow]
    · rw [ENNReal.inv_pow]
      norm_num
    · norm_num
  · positivity

theorem ex_10_2_2_width_tendsto_zero :
    Tendsto (fun n : ℕ => ENNReal.ofReal (ex_10_2_2_width n)) atTop
      (nhds 0) := by
  have hgeom :
      Tendsto (fun k : ℕ => ((2 : ENNReal)⁻¹) ^ k) atTop (nhds 0) := by
    apply ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    norm_num
  have hcomp := hgeom.comp ex_10_2_2_level_tendsto_atTop
  simpa [Function.comp_def, ex_10_2_2_width_eq_pow] using hcomp

theorem ex_10_2_2_convergesInMean :
    ConvergesInMean ex_10_2_2_unitIntervalMeasure
      ex_10_2_2_sequence ex_10_2_2_zero := by
  unfold ConvergesInMean ConvergesInRthMean
  refine ⟨?_, aestronglyMeasurable_const, by norm_num, ?_⟩
  · intro n
    exact
      (measurable_const.indicator
        (ex_10_2_2_event_measurable n)).aestronglyMeasurable
  · have hmoments :
        (fun n : ℕ =>
          meanDeviationMoment ex_10_2_2_unitIntervalMeasure
            ex_10_2_2_sequence ex_10_2_2_zero 1 n) =
          fun n : ℕ => ENNReal.ofReal (ex_10_2_2_width n) := by
      funext n
      rw [ex_10_2_2_meanMomentFormula_proved n,
        ex_10_2_2_eventMeasureFormula_proved n]
    simpa [hmoments] using ex_10_2_2_width_tendsto_zero

theorem ex_10_2_2_not_almost_sure :
    ¬ ConvergesAlmostSurely ex_10_2_2_unitIntervalMeasure
      ex_10_2_2_sequence ex_10_2_2_zero :=
  ex_10_2_2_not_almost_sure_of_pointwise_failure_on_unit
    (ex_10_2_2_pointwise_failure_of_infinitelyManyHits
      ex_10_2_2_infinitelyManyHits_proved)

theorem ex_10_2_2_sourceConclusion_proved :
    ex_10_2_2_sourceConclusion := by
  constructor
  · exact ex_10_2_2_convergesInMean
  · exact ex_10_2_2_not_almost_sure

theorem ex_10_2_2_sourceRoute_proved :
    ex_10_2_2_sourceRoute := by
  exact ⟨ex_10_2_2_blockCoversSource_proved,
    ex_10_2_2_eventMeasureFormula_proved,
    ex_10_2_2_infinitelyManyHits_proved,
    ex_10_2_2_meanMomentFormula_proved,
    ex_10_2_2_sourceConclusion_proved⟩



theorem ex_10_2_2 :
    ConvergesInMean ex_10_2_2_unitIntervalMeasure
        ex_10_2_2_sequence ex_10_2_2_zero ∧
      ¬ ConvergesAlmostSurely ex_10_2_2_unitIntervalMeasure
        ex_10_2_2_sequence ex_10_2_2_zero := by
  constructor
  · exact ex_10_2_2_convergesInMean
  · exact ex_10_2_2_not_almost_sure
