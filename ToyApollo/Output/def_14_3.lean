/-
TASK ID: def_14_3
TYPE: Definition
SOURCE PLAN: chapter14-tightness
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

def def_14_3_tightProbabilityMeasures
    (Pseq : ℕ → ProbabilityMeasure ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 ≤ M ∧
    ∀ n : ℕ, 1 - ε < (Pseq n : Measure ℝ).real (Icc (-M) M)

def def_14_3
    (Pseq : ℕ → ProbabilityMeasure ℝ) : Prop :=
  def_14_3_tightProbabilityMeasures Pseq

def def_14_3_tightCdfs
    (Fseq : ℕ → ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 ≤ M ∧
    ∀ n : ℕ, 1 - ε < Fseq n M - Fseq n (-M)

def def_14_3_mathlibTight
    (Pseq : ℕ → ProbabilityMeasure ℝ) : Prop :=
  IsTightMeasureSet (range fun n : ℕ => ((Pseq n : ProbabilityMeasure ℝ) : Measure ℝ))

def def_14_3_cdfOfMeasure (P : ProbabilityMeasure ℝ) : ℝ → ℝ :=
  fun x => (P : Measure ℝ).real (Iic x)

def def_14_3_cdfsOfMeasures
    (Pseq : ℕ → ProbabilityMeasure ℝ) : ℕ → ℝ → ℝ :=
  fun n => def_14_3_cdfOfMeasure (Pseq n)

structure def_14_3_IntervalMathlibTightBridge
    (Pseq : ℕ → ProbabilityMeasure ℝ) : Prop where
  interval_to_mathlib :
    def_14_3 Pseq → def_14_3_mathlibTight Pseq
  mathlib_to_interval :
    def_14_3_mathlibTight Pseq → def_14_3 Pseq

theorem def_14_3_of_mathlibTight
    (Pseq : ℕ → ProbabilityMeasure ℝ)
    (hTight : def_14_3_mathlibTight Pseq) :
    def_14_3 Pseq := by
  intro ε hε
  have hTendsto :
      Tendsto
        (fun r : ℝ =>
          ⨆ μ ∈ Set.range fun n : ℕ => ((Pseq n : ProbabilityMeasure ℝ) : Measure ℝ),
            μ {x : ℝ | r < ‖x‖})
        atTop (𝓝 (0 : ENNReal)) := by
    exact tendsto_measure_norm_gt_of_isTightMeasureSet hTight
  have hEventuallyLe :
      ∃ R : ℝ, ∀ r ≥ R,
        (fun r : ℝ =>
          ⨆ μ ∈ Set.range fun n : ℕ => ((Pseq n : ProbabilityMeasure ℝ) : Measure ℝ),
            μ {x : ℝ | r < ‖x‖}) r ≤ ENNReal.ofReal (ε / 2) :=
    ENNReal.tendsto_atTop_zero.mp hTendsto (ENNReal.ofReal (ε / 2))
      (ENNReal.ofReal_pos.mpr (by linarith))
  rcases hEventuallyLe with ⟨R, hR⟩
  let M : ℝ := max R 0
  refine ⟨M, le_max_right R 0, ?_⟩
  intro n
  have hRleM : R ≤ M := le_max_left R 0
  have htail_le_iSup :
      (Pseq n : Measure ℝ) {x : ℝ | M < ‖x‖} ≤
        (⨆ μ ∈ Set.range fun n : ℕ => ((Pseq n : ProbabilityMeasure ℝ) : Measure ℝ),
          μ {x : ℝ | M < ‖x‖}) := by
    refine le_iSup_of_le ((Pseq n : ProbabilityMeasure ℝ) : Measure ℝ) ?_
    exact le_iSup_of_le ⟨n, rfl⟩ le_rfl
  have hsup_lt :
      (⨆ μ ∈ Set.range fun n : ℕ => ((Pseq n : ProbabilityMeasure ℝ) : Measure ℝ),
          μ {x : ℝ | M < ‖x‖}) < ENNReal.ofReal ε := by
    exact lt_of_le_of_lt (hR M hRleM)
      ((ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith))
  have htail_lt :
      (Pseq n : Measure ℝ) {x : ℝ | M < ‖x‖} < ENNReal.ofReal ε :=
    lt_of_le_of_lt htail_le_iSup hsup_lt
  have htail_real_lt :
      (Pseq n : Measure ℝ).real {x : ℝ | M < |x|} < ε := by
    have hset : {x : ℝ | M < |x|} = {x : ℝ | M < ‖x‖} := by
      ext x
      simp [Real.norm_eq_abs]
    rw [hset, measureReal_def]
    exact ENNReal.toReal_lt_of_lt_ofReal htail_lt
  let s : Set ℝ := Icc (-M) M
  have hs : MeasurableSet s := measurableSet_Icc
  have hcompl : sᶜ = {x : ℝ | M < |x|} := by
    ext x
    simp only [s, mem_compl_iff, mem_Icc, mem_setOf_eq]
    constructor
    · intro hnot
      by_cases hxlt : x < -M
      · have hneg : |x| = -x := by
          exact abs_of_neg (lt_of_lt_of_le hxlt (neg_nonpos.mpr (le_max_right R 0)))
        rw [hneg]
        linarith
      · have hxge : -M ≤ x := le_of_not_gt hxlt
        have hxnotle : ¬ x ≤ M := fun hxle => hnot ⟨hxge, hxle⟩
        have hxM : M < x := lt_of_not_ge hxnotle
        exact lt_of_lt_of_le hxM (le_abs_self x)
    · intro hx hinside
      exact (not_lt.mpr (abs_le.mpr hinside)) hx
  have hsum := probReal_add_probReal_compl (μ := (Pseq n : Measure ℝ)) hs
  have htailn : (Pseq n : Measure ℝ).real sᶜ < ε := by
    simpa [hcompl] using htail_real_lt
  change 1 - ε < (Pseq n : Measure ℝ).real s
  linarith

theorem def_14_3_to_mathlibTight
    (Pseq : ℕ → ProbabilityMeasure ℝ)
    (hTight : def_14_3 Pseq) :
    def_14_3_mathlibTight Pseq := by
  rw [def_14_3_mathlibTight]
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases hε_top : ε = ⊤
  · refine ⟨∅, isCompact_empty, ?_⟩
    intro μ _hμ
    rw [hε_top]
    exact le_top
  have hε_real_pos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hε_top
  rcases hTight ε.toReal hε_real_pos with ⟨M, hM_nonneg, hM⟩
  refine ⟨Icc (-M) M, isCompact_Icc, ?_⟩
  rintro μ ⟨n, rfl⟩
  haveI : IsProbabilityMeasure (Pseq n : Measure ℝ) := (Pseq n).property
  let s : Set ℝ := Icc (-M) M
  have hs : MeasurableSet s := measurableSet_Icc
  have hcompl : sᶜ = {x : ℝ | M < |x|} := by
    ext x
    simp only [s, mem_compl_iff, mem_Icc, mem_setOf_eq]
    constructor
    · intro hnot
      by_cases hxlt : x < -M
      · have hneg : |x| = -x := by
          exact abs_of_neg (lt_of_lt_of_le hxlt (neg_nonpos.mpr hM_nonneg))
        rw [hneg]
        linarith
      · have hxge : -M ≤ x := le_of_not_gt hxlt
        have hxnotle : ¬ x ≤ M := fun hxle => hnot ⟨hxge, hxle⟩
        have hxM : M < x := lt_of_not_ge hxnotle
        exact lt_of_lt_of_le hxM (le_abs_self x)
    · intro hx hinside
      exact (not_lt.mpr (abs_le.mpr hinside)) hx
  have hsum := probReal_add_probReal_compl (μ := (Pseq n : Measure ℝ)) hs
  have htail_real_lt : (Pseq n : Measure ℝ).real sᶜ < ε.toReal := by
    have hinside := hM n
    change 1 - ε.toReal < (Pseq n : Measure ℝ).real s at hinside
    linarith
  have htail_lt : (Pseq n : Measure ℝ) sᶜ < ENNReal.ofReal ε.toReal := by
    rw [ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top (Pseq n : Measure ℝ) sᶜ)]
    simpa [measureReal_def] using htail_real_lt
  have htail_lt_eps : (Pseq n : Measure ℝ) sᶜ < ε := by
    simpa [ENNReal.ofReal_toReal hε_top] using htail_lt
  simpa [s] using htail_lt_eps.le

theorem def_14_3_intervalMathlibTightBridge
    (Pseq : ℕ → ProbabilityMeasure ℝ) :
    def_14_3_IntervalMathlibTightBridge Pseq where
  interval_to_mathlib := def_14_3_to_mathlibTight Pseq
  mathlib_to_interval := def_14_3_of_mathlibTight Pseq
