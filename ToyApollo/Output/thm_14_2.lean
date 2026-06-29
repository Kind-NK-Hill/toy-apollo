/-
TASK ID: thm_14_2
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter14-weak-convergence
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_10_4
import ToyApollo.Output.def_14_2
import ToyApollo.Output.thm_10_8
import ToyApollo.Output.thm_10_11
import ToyApollo.Output.thm_14_1

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set ProbabilityTheory Function
open scoped Topology

noncomputable section

def thm_14_2_randomVariableCdf
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) : ℝ → ℝ :=
  fun x => measureCdf (Measure.map X μ) x

def thm_14_2_cdfConvergence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  CdfConvergesInDistribution
    (fun n => thm_14_2_randomVariableCdf μ (Xseq n))
    (thm_14_2_randomVariableCdf μ X)

def thm_14_2_weakConvergence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X) : Prop :=
  def_14_2 μ Xseq X hXseq hX

theorem thm_14_2_cdfConvergence_eq_def_10_4
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ) :
    thm_14_2_cdfConvergence μ Xseq X =
      RandomVariablesConvergeInDistribution μ Xseq X := by
  rfl

theorem thm_14_2_weak_iff_expectations
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Xseq : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X) :
    thm_14_2_weakConvergence μ Xseq X hXseq hX ↔
      ∀ h : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun n : ℕ => ∫ ω, h (Xseq n ω) ∂μ) atTop
          (𝓝 (∫ ω, h (X ω) ∂μ)) := by
  exact def_14_2_iff_expectations μ hXseq hX

theorem thm_14_2_atom_zero_of_cdf_continuous
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {x : ℝ}
    (hcont : ContinuousAt (fun y : ℝ => measureCdf μ y) x) :
    μ {x} = 0 := by
  have hcont_cdf : ContinuousAt (fun y : ℝ => cdf μ y) x := by
    simpa [measureCdf, cdf_eq_real] using hcont
  have hleft : Function.leftLim (fun y : ℝ => cdf μ y) x = cdf μ x := by
    exact hcont_cdf.continuousWithinAt.leftLim_eq
  rw [← measure_cdf μ, StieltjesFunction.measure_singleton]
  simp [hleft]

theorem thm_14_2_weak_to_cdfConvergence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Xseq : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X)
    (hWeak : thm_14_2_weakConvergence μ Xseq X hXseq hX) :
    thm_14_2_cdfConvergence μ Xseq X := by
  let Pseq : ℕ → ProbabilityMeasure ℝ := def_14_1_laws μ Xseq hXseq
  let P : ProbabilityMeasure ℝ := def_14_1_law μ X hX
  have hLawWeak : def_14_1 Pseq P := by
    simpa [Pseq, P, thm_14_2_weakConvergence, def_14_2,
      def_14_1, def_14_1_weakConvergence,
      def_14_1_randomVariableWeakConvergence, def_14_1_laws, def_14_1_law] using hWeak
  have hTend : Tendsto Pseq atTop (𝓝 P) := (def_14_1_iff_tendsto).1 hLawWeak
  intro x hxcont
  have hAtom : (P : Measure ℝ) {x} = 0 := by
    haveI : IsProbabilityMeasure (Measure.map X μ) :=
      Measure.isProbabilityMeasure_map hX.aemeasurable
    simpa [P, def_14_1_law] using
      (thm_14_2_atom_zero_of_cdf_continuous (Measure.map X μ) hxcont)
  have hFrontier : (P : Measure ℝ) (frontier (Iic x)) = 0 := by
    simpa [frontier_Iic] using hAtom
  have hENN :
      Tendsto
        (fun n : ℕ => ((Pseq n : ProbabilityMeasure ℝ) : Measure ℝ) (Iic x))
        atTop (𝓝 (((P : ProbabilityMeasure ℝ) : Measure ℝ) (Iic x))) :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hTend hFrontier
  have hReal :
      Tendsto
        (fun n : ℕ =>
          (((Pseq n : ProbabilityMeasure ℝ) : Measure ℝ) (Iic x)).toReal)
        atTop
        (𝓝 ((((P : ProbabilityMeasure ℝ) : Measure ℝ) (Iic x)).toReal)) :=
    (ENNReal.tendsto_toReal
      (measure_ne_top (((P : ProbabilityMeasure ℝ) : Measure ℝ)) (Iic x))).comp hENN
  simpa [thm_14_2_cdfConvergence, thm_14_2_randomVariableCdf,
    CdfConvergesInDistribution, measureCdf, Pseq, P, def_14_1_laws,
    def_14_1_law, measureReal_def] using hReal

theorem thm_14_2_skorokhod_representation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Xseq : ℕ → Ω → ℝ} {X : Ω → ℝ}
    {hXseq : ∀ n : ℕ, Measurable (Xseq n)} {hX : Measurable X}
    (hDist : thm_14_2_cdfConvergence μ Xseq X) :
    SkorokhodRepresentation μ Xseq X := by
  exact thm_10_8 μ Xseq X hDist
    (fun n : ℕ => (hXseq n).aemeasurable) hX.aemeasurable

theorem thm_14_2_distribution_to_weak
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Xseq : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X)
    (hDist : thm_14_2_cdfConvergence μ Xseq X) :
    thm_14_2_weakConvergence μ Xseq X hXseq hX := by
  let Fseq : ℕ → thm_10_8_ProbabilityCdf := fun n : ℕ =>
    thm_10_8_probabilityCdfOfMeasure (Measure.map (Xseq n) μ)
  let F : thm_10_8_ProbabilityCdf :=
    thm_10_8_probabilityCdfOfMeasure (Measure.map X μ)
  let Yn : ℕ → ℝ → ℝ := fun n : ℕ =>
    thm_10_8_lowerQuantileVariable (Fseq n)
  let Y : ℝ → ℝ := thm_10_8_lowerQuantileVariable F
  have hCdfConv :
      CdfConvergesInDistribution
        (fun n x => (Fseq n).stieltjes x)
        (F.stieltjes : ℝ → ℝ) := by
    haveI hTarget : IsProbabilityMeasure (Measure.map X μ) :=
      Measure.isProbabilityMeasure_map hX.aemeasurable
    haveI hSeq (n : ℕ) : IsProbabilityMeasure (Measure.map (Xseq n) μ) :=
      Measure.isProbabilityMeasure_map (hXseq n).aemeasurable
    have hDistCdf :
        CdfConvergesInDistribution
          (fun n x => measureCdf (Measure.map (Xseq n) μ) x)
          (measureCdf (Measure.map X μ)) := by
      simpa [thm_14_2_cdfConvergence, thm_14_2_randomVariableCdf] using hDist
    intro x hcont
    have hcont_measure :
        ContinuousAt (measureCdf (Measure.map X μ)) x := by
      have hfun :
          (fun y : ℝ => measureCdf (Measure.map X μ) y) =
            (fun y : ℝ => F.stieltjes y) := by
        funext y
        simp [F, thm_10_8_probabilityCdfOfMeasure,
          measureCdf, ProbabilityTheory.cdf_eq_real]
      change ContinuousAt (fun y : ℝ => measureCdf (Measure.map X μ) y) x
      rw [hfun]
      exact hcont
    have htendsto := hDistCdf x hcont_measure
    simpa [Fseq, F, thm_10_8_probabilityCdfOfMeasure,
      measureCdf, ProbabilityTheory.cdf_eq_real] using htendsto
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
          Measure.map (Xseq n) μ := by
    intro n
    simpa [Yn, Fseq] using
      @thm_10_8_quantile_law_preservation_of_probabilityCdfOfMeasure
        (Measure.map (Xseq n) μ)
        (Measure.isProbabilityMeasure_map (hXseq n).aemeasurable)
  have hYLaw :
      Measure.map Y thm_10_8_unitIntervalMeasure = Measure.map X μ := by
    simpa [Y, F] using
      @thm_10_8_quantile_law_preservation_of_probabilityCdfOfMeasure
        (Measure.map X μ)
        (Measure.isProbabilityMeasure_map hX.aemeasurable)
  let Pseq : ℕ → ProbabilityMeasure ℝ := def_14_1_laws μ Xseq hXseq
  let P : ProbabilityMeasure ℝ := def_14_1_law μ X hX
  have hLawTendsto : Tendsto Pseq atTop (𝓝 P) := by
    have hPseq :
        (fun n : ℕ =>
          (⟨Measure.map (Yn n) thm_10_8_unitIntervalMeasure,
            Measure.isProbabilityMeasure_map
              (hInDistribution.forall_aemeasurable n)⟩ :
            ProbabilityMeasure ℝ)) = Pseq := by
      funext n
      apply Subtype.ext
      simpa [Pseq, def_14_1_laws, def_14_1_law] using hYnLaw n
    have hP :
        (⟨Measure.map Y thm_10_8_unitIntervalMeasure,
          Measure.isProbabilityMeasure_map hInDistribution.aemeasurable_limit⟩ :
          ProbabilityMeasure ℝ) = P := by
      apply Subtype.ext
      simpa [P, def_14_1_law] using hYLaw
    rw [← hPseq, ← hP]
    exact hInDistribution.tendsto
  have hLawWeak : def_14_1 Pseq P := (def_14_1_iff_tendsto).2 hLawTendsto
  simpa [thm_14_2_weakConvergence, def_14_2,
    def_14_1_randomVariableWeakConvergence, Pseq, P, def_14_1_laws,
    def_14_1_law, def_14_1, def_14_1_weakConvergence] using hLawWeak

theorem thm_14_2
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X) :
    thm_14_2_weakConvergence μ Xseq X hXseq hX ↔
      thm_14_2_cdfConvergence μ Xseq X := by
  constructor
  · intro hWeak
    exact thm_14_2_weak_to_cdfConvergence μ hXseq hX hWeak
  · intro hDist
    exact thm_14_2_distribution_to_weak μ hXseq hX hDist

theorem thm_14_2_levy_condition_one_to_two
    {P : ℕ → ProbabilityMeasure ℝ} {φ : ℝ → ℂ}
    (hφ : thm_14_1_pointwiseCharFunConvergence P φ) :
    thm_14_1_weakLimit P → thm_14_1_limitIsCharacteristic φ :=
  (thm_14_1_weak_iff_characteristic hφ).mp
