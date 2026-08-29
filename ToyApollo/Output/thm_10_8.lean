/-
TASK ID: thm_10_8
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter10-distribution-total-variation
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_10_4
import ToyApollo.Output.prob_3_5
import ToyApollo.Output.thm_10_8_quantile_defs
import ToyApollo.Output.thm_10_8_quantile_convergence
import ToyApollo.Output.thm_10_8_quantile_law

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

def SkorokhodRepresentation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
    ∃ (Yn : ℕ → ℝ → ℝ) (Y : ℝ → ℝ),
      (∀ᵐ ω ∂ν, Tendsto (fun n : ℕ => Yn n ω) atTop (nhds (Y ω))) ∧
      (∀ n : ℕ, Measure.map (Yn n) ν = Measure.map (Xn n) μ) ∧
      Measure.map Y ν = Measure.map X μ

structure SkorokhodQuantileSupport {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (_hDist :
      RandomVariablesConvergeInDistribution (fun _ : ℕ => μ) Xn μ X) where
  target_seq_isProbability : ∀ n : ℕ, IsProbabilityMeasure (Measure.map (Xn n) μ)
  target_isProbability : IsProbabilityMeasure (Measure.map X μ)

theorem mkSkorokhodQuantileSupport {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hDist :
      RandomVariablesConvergeInDistribution (fun _ : ℕ => μ) Xn μ X)
    (hXn : ∀ n : ℕ, AEMeasurable (Xn n) μ)
    (hX : AEMeasurable X μ) :
    SkorokhodQuantileSupport μ Xn X hDist where
  target_seq_isProbability := fun n : ℕ =>
    Measure.isProbabilityMeasure_map (hXn n)
  target_isProbability := Measure.isProbabilityMeasure_map hX

theorem thm_10_8 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hDist :
      RandomVariablesConvergeInDistribution (fun _ : ℕ => μ) Xn μ X)
    (hXn : ∀ n : ℕ, AEMeasurable (Xn n) μ)
    (hX : AEMeasurable X μ) :
    SkorokhodRepresentation μ Xn X := by
  let h_quantile_support :=
    mkSkorokhodQuantileSupport μ Xn X hDist hXn hX
  have hCdfConv :
      ∀ x : ℝ,
        ContinuousAt
          ((thm_10_8_probabilityCdfOfMeasure
            (Measure.map X μ)).stieltjes : ℝ → ℝ) x →
        Tendsto
          (fun n : ℕ =>
            (thm_10_8_probabilityCdfOfMeasure
              (Measure.map (Xn n) μ)).stieltjes x)
          atTop
          (𝓝
            ((thm_10_8_probabilityCdfOfMeasure
              (Measure.map X μ)).stieltjes x)) := by
    haveI hTarget : IsProbabilityMeasure (Measure.map X μ) :=
      h_quantile_support.target_isProbability
    haveI hSeq (n : ℕ) : IsProbabilityMeasure (Measure.map (Xn n) μ) :=
      h_quantile_support.target_seq_isProbability n
    let Pseq : ℕ → ProbabilityMeasure ℝ := fun n =>
      ⟨Measure.map (Xn n) μ, h_quantile_support.target_seq_isProbability n⟩
    let P : ProbabilityMeasure ℝ :=
      ⟨Measure.map X μ, h_quantile_support.target_isProbability⟩
    have hWeak : MeasuresConvergeInDistribution Pseq P := by
      simpa [MeasuresConvergeInDistribution, Pseq, P] using hDist.tendsto
    have hDistCdf : CdfConvergesInDistribution Pseq P :=
      (measuresConvergeInDistribution_iff_cdf Pseq P).1 hWeak
    intro x hcont
    have hcont_measure :
        ContinuousAt (measureCdf P) x := by
      have hfun :
          (fun y : ℝ => measureCdf P y) =
            (fun y : ℝ =>
              (thm_10_8_probabilityCdfOfMeasure
                (Measure.map X μ)).stieltjes y) := by
        funext y
        simp [P, measureCdf, thm_10_8_probabilityCdfOfMeasure,
          ProbabilityTheory.cdf_eq_real]
      change ContinuousAt
        (fun y : ℝ => measureCdf P y) x
      rw [hfun]
      exact hcont
    have htendsto := hDistCdf x hcont_measure
    simpa [Pseq, P, measureCdf, thm_10_8_probabilityCdfOfMeasure,
      ProbabilityTheory.cdf_eq_real] using htendsto
  have hAlmostSure :
      ∀ᵐ ω ∂thm_10_8_unitIntervalMeasure,
        Tendsto
          (fun n : ℕ =>
            thm_10_8_lowerQuantileVariable
              (thm_10_8_probabilityCdfOfMeasure (Measure.map (Xn n) μ)) ω)
          atTop
          (nhds
            (thm_10_8_lowerQuantileVariable
              (thm_10_8_probabilityCdfOfMeasure (Measure.map X μ)) ω)) :=
    thm_10_8_almost_sure_lowerQuantile_tendsto
      (fun n : ℕ =>
        thm_10_8_probabilityCdfOfMeasure (Measure.map (Xn n) μ))
      (thm_10_8_probabilityCdfOfMeasure (Measure.map X μ))
      hCdfConv
  have hYnLaw :
      ∀ n : ℕ,
        Measure.map
          (thm_10_8_lowerQuantileVariable
            (thm_10_8_probabilityCdfOfMeasure (Measure.map (Xn n) μ)))
          thm_10_8_unitIntervalMeasure =
        Measure.map (Xn n) μ :=
    fun n : ℕ =>
      @thm_10_8_quantile_law_preservation_of_probabilityCdfOfMeasure
        (Measure.map (Xn n) μ)
        (h_quantile_support.target_seq_isProbability n)
  have hYLaw :
      Measure.map
        (thm_10_8_lowerQuantileVariable
          (thm_10_8_probabilityCdfOfMeasure (Measure.map X μ)))
        thm_10_8_unitIntervalMeasure =
      Measure.map X μ :=
    @thm_10_8_quantile_law_preservation_of_probabilityCdfOfMeasure
      (Measure.map X μ)
      h_quantile_support.target_isProbability
  exact
    ⟨thm_10_8_unitIntervalMeasure,
      thm_10_8_unitIntervalMeasure_isProbabilityMeasure,
      fun n : ℕ =>
        thm_10_8_lowerQuantileVariable
          (thm_10_8_probabilityCdfOfMeasure (Measure.map (Xn n) μ)),
      thm_10_8_lowerQuantileVariable
        (thm_10_8_probabilityCdfOfMeasure (Measure.map X μ)),
      hAlmostSure,
      hYnLaw,
      hYLaw⟩
