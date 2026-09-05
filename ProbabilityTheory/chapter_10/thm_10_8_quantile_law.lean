/-
TASK ID: thm_10_8_quantile_law
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_03.thm_3_9
import ProbabilityTheory.chapter_10.thm_10_8_quantile_defs

open MeasureTheory ProbabilityTheory Set
open scoped Topology

noncomputable section



theorem thm_10_8_quantile_event_ae_eq_Ioc
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (y : ℝ) :
    (Set.inter
      {ω : ℝ |
        thm_10_8_lowerQuantileVariable (thm_10_8_probabilityCdfOfMeasure μ) ω ≤ y}
      (Ioc (0 : ℝ) 1)) =ᵐ[volume]
      Ioc (0 : ℝ) (cdf μ y) := by
  have hcdf1 : cdf μ y ≤ 1 := cdf_le_one μ y
  filter_upwards
    [(show ∀ᵐ ω ∂(volume : Measure ℝ), ω ≠ cdf μ y by
        rw [ae_iff]
        simp),
      (show ∀ᵐ ω ∂(volume : Measure ℝ), ω ≠ (1 : ℝ) by
        rw [ae_iff]
        simp)]
    with ω hω_ne_cdf hω_ne_one
  apply propext
  constructor
  · intro hω
    rcases hω with ⟨hQ, hunit⟩
    have hω0 : 0 < ω := hunit.1
    have hω1le : ω ≤ 1 := hunit.2
    have hω1 : ω < 1 := lt_of_le_of_ne hω1le hω_ne_one
    have hQlower :
        thm_10_8_lowerQuantile (thm_10_8_probabilityCdfOfMeasure μ) ω ≤ y := by
      simpa [thm_10_8_lowerQuantileVariable, hω0, hω1] using hQ
    have hle : ω ≤ cdf μ y := by
      simpa [thm_10_8_probabilityCdfOfMeasure] using
        (thm_10_8_lowerQuantile_le_iff
          (thm_10_8_probabilityCdfOfMeasure μ) hω0 hω1).1 hQlower
    exact ⟨hω0, hle⟩
  · intro hω
    rcases hω with ⟨hω0, hωle⟩
    have hω1le : ω ≤ 1 := hωle.trans hcdf1
    have hω1 : ω < 1 := lt_of_le_of_ne hω1le hω_ne_one
    have hQ :
        thm_10_8_lowerQuantileVariable (thm_10_8_probabilityCdfOfMeasure μ) ω ≤ y := by
      have hQlower :
          thm_10_8_lowerQuantile (thm_10_8_probabilityCdfOfMeasure μ) ω ≤ y := by
        simpa [thm_10_8_probabilityCdfOfMeasure] using
          (thm_10_8_lowerQuantile_le_iff
            (thm_10_8_probabilityCdfOfMeasure μ) hω0 hω1).2 hωle
      simpa [thm_10_8_lowerQuantileVariable, hω0, hω1] using hQlower
    exact ⟨hQ, hω0, hω1le⟩



theorem thm_10_8_unitIntervalMeasure_lowerQuantile_event
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (y : ℝ) :
    thm_10_8_unitIntervalMeasure
      {ω : ℝ |
        thm_10_8_lowerQuantileVariable (thm_10_8_probabilityCdfOfMeasure μ) ω ≤ y} =
      μ (Iic y) := by
  rw [thm_10_8_unitIntervalMeasure, Measure.restrict_apply' measurableSet_Ioc]
  calc
    volume
        (Set.inter
          {ω : ℝ |
            thm_10_8_lowerQuantileVariable (thm_10_8_probabilityCdfOfMeasure μ) ω ≤ y}
          (Ioc (0 : ℝ) 1)) =
        volume (Ioc (0 : ℝ) (cdf μ y)) := by
          exact measure_congr (thm_10_8_quantile_event_ae_eq_Ioc μ y)
    _ = ENNReal.ofReal (cdf μ y) := by
          rw [Real.volume_Ioc]
          ring_nf
    _ = μ (Iic y) := by
          exact ofReal_cdf μ y



theorem thm_10_8_law_eq_of_Iic
    (ν μ : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hIic : ∀ y : ℝ, ν (Iic y) = μ (Iic y)) :
    ν = μ :=
  thm_3_9 ν μ hIic



theorem thm_10_8_quantile_law_preservation_of_Iic
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (F : thm_10_8_ProbabilityCdf)
    (hY : Measurable (thm_10_8_lowerQuantileVariable F))
    (hIic :
      ∀ y : ℝ,
        thm_10_8_unitIntervalMeasure
          {ω : ℝ | thm_10_8_lowerQuantileVariable F ω ≤ y} =
        μ (Iic y)) :
    Measure.map (thm_10_8_lowerQuantileVariable F)
        thm_10_8_unitIntervalMeasure = μ := by
  haveI :
      IsProbabilityMeasure
        (Measure.map (thm_10_8_lowerQuantileVariable F)
          thm_10_8_unitIntervalMeasure) :=
    Measure.isProbabilityMeasure_map hY.aemeasurable
  refine thm_10_8_law_eq_of_Iic
    (Measure.map (thm_10_8_lowerQuantileVariable F)
      thm_10_8_unitIntervalMeasure) μ ?_
  intro y
  rw [Measure.map_apply hY measurableSet_Iic]
  change
    thm_10_8_unitIntervalMeasure
        {ω : ℝ | thm_10_8_lowerQuantileVariable F ω ≤ y} =
      μ (Iic y)
  exact hIic y



theorem thm_10_8_quantile_law_preservation_of_probabilityCdfOfMeasure
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measure.map
        (thm_10_8_lowerQuantileVariable (thm_10_8_probabilityCdfOfMeasure μ))
        thm_10_8_unitIntervalMeasure = μ := by
  exact thm_10_8_quantile_law_preservation_of_Iic
    μ
    (thm_10_8_probabilityCdfOfMeasure μ)
    (thm_10_8_lowerQuantileVariable_measurable
      (thm_10_8_probabilityCdfOfMeasure μ))
    (thm_10_8_unitIntervalMeasure_lowerQuantile_event μ)



theorem thm_10_8_quantile_law_preservation_seq_of_Iic
    (μn : ℕ → Measure ℝ) [∀ n : ℕ, IsProbabilityMeasure (μn n)]
    (Fs : ℕ → thm_10_8_ProbabilityCdf)
    (hY : ∀ n : ℕ, Measurable (thm_10_8_lowerQuantileVariable (Fs n)))
    (hIic :
      ∀ n : ℕ, ∀ y : ℝ,
        thm_10_8_unitIntervalMeasure
          {ω : ℝ | thm_10_8_lowerQuantileVariable (Fs n) ω ≤ y} =
        μn n (Iic y)) :
    ∀ n : ℕ,
      Measure.map (thm_10_8_lowerQuantileVariable (Fs n))
        thm_10_8_unitIntervalMeasure = μn n := by
  intro n
  exact thm_10_8_quantile_law_preservation_of_Iic
    (μn n) (Fs n) (hY n) (hIic n)
