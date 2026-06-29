/-
TASK ID: ex_10_3_2
TYPE: Example_Proof
SOURCE PLAN: chapter10-distribution-total-variation
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_10_4
import ToyApollo.Output.def_10_5
import ToyApollo.Output.prob_7_6
import ToyApollo.Output.prob_8_7
import ToyApollo.Output.thm_10_6

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open TVCore
open ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

def ex_10_3_2_densityProbabilityMeasure
    (f : ℝ → ℝ) (hf : IsProbabilityDensity f) : ProbabilityMeasure ℝ :=
  ⟨densityMeasure f, by
    constructor
    exact densityMeasure_apply_univ
      (MeasureTheory.integrable_of_integral_eq_one hf.integral_eq_one)
      hf.nonneg hf.integral_eq_one⟩

lemma ex_10_3_2_pdf_lintegral_eq_one
    {f : ℝ → ℝ} (hf : IsProbabilityDensity f) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂(volume : Measure ℝ) = 1 := by
  have hf_int : Integrable f (volume : Measure ℝ) :=
    MeasureTheory.integrable_of_integral_eq_one hf.integral_eq_one
  have hf_nonneg : 0 ≤ᵐ[volume] f :=
    Filter.Eventually.of_forall hf.nonneg
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_int hf_nonneg,
    hf.integral_eq_one]
  norm_num

theorem ex_10_3_2_scheffe_l1
    (fn : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hfn : ∀ n : ℕ, IsProbabilityDensity (fn n))
    (hf : IsProbabilityDensity f)
    (h_ae :
      ∀ᵐ x ∂(volume : Measure ℝ),
        Tendsto (fun n : ℕ => fn n x) atTop (𝓝 (f x))) :
    Tendsto (fun n : ℕ => ∫ x, |fn n x - f x| ∂(volume : Measure ℝ))
      atTop (𝓝 0) := by
  have h_lint_fn :
      ∀ n : ℕ, ∫⁻ x, ENNReal.ofReal (fn n x) ∂(volume : Measure ℝ) < ⊤ := by
    intro n
    rw [ex_10_3_2_pdf_lintegral_eq_one (hfn n)]
    exact ENNReal.one_lt_top
  have h_lint_f :
      ∫⁻ x, ENNReal.ofReal (f x) ∂(volume : Measure ℝ) < ⊤ := by
    rw [ex_10_3_2_pdf_lintegral_eq_one hf]
    exact ENNReal.one_lt_top
  have h_lint_conv :
      Tendsto
        (fun n : ℕ => ∫⁻ x, ENNReal.ofReal (fn n x) ∂(volume : Measure ℝ))
        atTop
        (𝓝 (∫⁻ x, ENNReal.ofReal (f x) ∂(volume : Measure ℝ))) := by
    have hfn_eq :
        (fun n : ℕ => ∫⁻ x, ENNReal.ofReal (fn n x) ∂(volume : Measure ℝ)) =
          fun _n : ℕ => (1 : ℝ≥0∞) := by
      funext n
      exact ex_10_3_2_pdf_lintegral_eq_one (hfn n)
    have hf_eq :
        ∫⁻ x, ENNReal.ofReal (f x) ∂(volume : Measure ℝ) = 1 :=
      ex_10_3_2_pdf_lintegral_eq_one hf
    rw [hfn_eq, hf_eq]
    exact tendsto_const_nhds
  exact (prob_7_6
    (μ := (volume : Measure ℝ))
    (f := fn)
    (f_final := f)
    (fun n => (hfn n).measurable)
    (fun n => (hfn n).nonneg)
    h_ae
    h_lint_fn
    h_lint_f
    h_lint_conv).2

theorem ex_10_3_2_totalVariation_convergence
    (fn : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hfn : ∀ n : ℕ, IsProbabilityDensity (fn n))
    (hf : IsProbabilityDensity f)
    (h_ae :
      ∀ᵐ x ∂(volume : Measure ℝ),
        Tendsto (fun n : ℕ => fn n x) atTop (𝓝 (f x))) :
    MeasuresConvergeInTotalVariation
      (fun n : ℕ => densityMeasure (fn n)) (densityMeasure f) := by
  have hL1 := ex_10_3_2_scheffe_l1 fn f hfn hf h_ae
  have hScaled :
      Tendsto
        (fun n : ℕ =>
          (1 / 2 : ℝ) * ∫ x, |fn n x - f x| ∂(volume : Measure ℝ))
        atTop (𝓝 0) := by
    simpa using hL1.const_mul (1 / 2 : ℝ)
  have hTV_eq :
      ∀ n : ℕ,
        totalVariationDistance (densityMeasure (fn n)) (densityMeasure f) =
          (1 / 2 : ℝ) * ∫ x, |fn n x - f x| ∂(volume : Measure ℝ) := by
    intro n
    simpa [densityDiff] using
      thm_8_6_continuous
        (hfn n).measurable hf.measurable
        (MeasureTheory.integrable_of_integral_eq_one (hfn n).integral_eq_one)
        (MeasureTheory.integrable_of_integral_eq_one hf.integral_eq_one)
        (hfn n).nonneg hf.nonneg
        (hfn n).integral_eq_one hf.integral_eq_one
  have hProbFn :
      ∀ n : ℕ, IsProbabilityMeasure (densityMeasure (fn n)) := by
    intro n
    let Pn : ProbabilityMeasure ℝ :=
      ex_10_3_2_densityProbabilityMeasure (fn n) (hfn n)
    change IsProbabilityMeasure (Pn : Measure ℝ)
    infer_instance
  have hProbF : IsProbabilityMeasure (densityMeasure f) := by
    let P : ProbabilityMeasure ℝ := ex_10_3_2_densityProbabilityMeasure f hf
    change IsProbabilityMeasure (P : Measure ℝ)
    infer_instance
  exact ⟨hProbFn, hProbF, by simpa [hTV_eq] using hScaled⟩

theorem ex_10_3_2_density_convergesInDistribution
    (fn : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hfn : ∀ n : ℕ, IsProbabilityDensity (fn n))
    (hf : IsProbabilityDensity f)
    (h_ae :
      ∀ᵐ x ∂(volume : Measure ℝ),
        Tendsto (fun n : ℕ => fn n x) atTop (𝓝 (f x))) :
    MeasuresConvergeInDistribution
      (fun n : ℕ => densityMeasure (fn n)) (densityMeasure f) := by
  let Pseq : ℕ → ProbabilityMeasure ℝ :=
    fun n : ℕ => ex_10_3_2_densityProbabilityMeasure (fn n) (hfn n)
  let P : ProbabilityMeasure ℝ :=
    ex_10_3_2_densityProbabilityMeasure f hf
  have hTV :
      MeasuresConvergeInTotalVariation
        (fun n : ℕ => (Pseq n : Measure ℝ)) (P : Measure ℝ) := by
    simpa [Pseq, P, ex_10_3_2_densityProbabilityMeasure] using
      ex_10_3_2_totalVariation_convergence fn f hfn hf h_ae
  have hDist := thm_10_6 Pseq P hTV
  simpa [Pseq, P, ex_10_3_2_densityProbabilityMeasure] using hDist

structure ex_10_3_2_ContinuousRandomVariableSetup
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (fn : ℕ → ℝ → ℝ) (f : ℝ → ℝ) where
  probability_space : IsProbabilityMeasure μ
  Xn_measurable : ∀ n : ℕ, Measurable (Xn n)
  X_measurable : Measurable X
  fn_pdf : ∀ n : ℕ, IsProbabilityDensity (fn n)
  f_pdf : IsProbabilityDensity f
  density_ae_convergence :
    ∀ᵐ x ∂(volume : Measure ℝ),
      Tendsto (fun n : ℕ => fn n x) atTop (𝓝 (f x))
  Xn_law_eq_density :
    ∀ n : ℕ, Measure.map (Xn n) μ = densityMeasure (fn n)
  X_law_eq_density :
    Measure.map X μ = densityMeasure f

theorem ex_10_3_2_randomVariables_convergeInDistribution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (fn : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (S : ex_10_3_2_ContinuousRandomVariableSetup μ Xn X fn f) :
    RandomVariablesConvergeInDistribution μ Xn X := by
  have hDist :=
    ex_10_3_2_density_convergesInDistribution fn f
      S.fn_pdf S.f_pdf S.density_ae_convergence
  simpa [RandomVariablesConvergeInDistribution, S.Xn_law_eq_density,
    S.X_law_eq_density] using hDist

noncomputable def ex_10_3_2_gaussianPdf
    (mean variance x : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi * variance)) *
    Real.exp (-((x - mean) ^ 2) / (2 * variance))

lemma ex_10_3_2_gaussianPdf_eq_gaussianPDFReal
    (mean : ℝ) {variance : ℝ} (hvariance : 0 < variance) :
    ex_10_3_2_gaussianPdf mean variance =
      gaussianPDFReal mean ⟨variance, hvariance.le⟩ := by
  ext x
  simp [ex_10_3_2_gaussianPdf, gaussianPDFReal, one_div]

theorem ex_10_3_2_gaussianPdf_isProbabilityDensity
    (mean : ℝ) {variance : ℝ} (hvariance : 0 < variance) :
    IsProbabilityDensity (ex_10_3_2_gaussianPdf mean variance) := by
  let v : ℝ≥0 := ⟨variance, hvariance.le⟩
  have hv : v ≠ 0 := by
    intro hv0
    have hcoe : (v : ℝ) = 0 := congrArg Subtype.val hv0
    exact hvariance.ne' hcoe
  refine ⟨?_, ?_, ?_⟩
  · rw [ex_10_3_2_gaussianPdf_eq_gaussianPDFReal mean hvariance]
    exact measurable_gaussianPDFReal mean v
  · intro x
    rw [ex_10_3_2_gaussianPdf_eq_gaussianPDFReal mean hvariance]
    exact gaussianPDFReal_nonneg mean v x
  · rw [ex_10_3_2_gaussianPdf_eq_gaussianPDFReal mean hvariance]
    exact integral_gaussianPDFReal_eq_one mean hv

theorem ex_10_3_2_gaussian_pdf_convergence
    (meanSeq varianceSeq : ℕ → ℝ) (mean variance : ℝ)
    (mean_tendsto : Tendsto meanSeq atTop (𝓝 mean))
    (variance_tendsto : Tendsto varianceSeq atTop (𝓝 variance))
    (variance_pos : 0 < variance) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      Tendsto
        (fun n : ℕ => ex_10_3_2_gaussianPdf (meanSeq n) (varianceSeq n) x)
        atTop
        (𝓝 (ex_10_3_2_gaussianPdf mean variance x)) := by
  filter_upwards [] with x
  have h_sqrt_ne : Real.sqrt (2 * Real.pi * variance) ≠ 0 := by
    positivity
  have h_variance_ne : (2 * variance) ≠ 0 := by
    positivity
  have h_sqrt :
      Tendsto
        (fun n : ℕ => Real.sqrt (2 * Real.pi * varianceSeq n))
        atTop
        (𝓝 (Real.sqrt (2 * Real.pi * variance))) := by
    exact ((tendsto_const_nhds.mul tendsto_const_nhds).mul variance_tendsto).sqrt
  have h_coeff :
      Tendsto
        (fun n : ℕ => (Real.sqrt (2 * Real.pi * varianceSeq n))⁻¹)
        atTop
        (𝓝 (Real.sqrt (2 * Real.pi * variance))⁻¹) := by
    exact h_sqrt.inv₀ h_sqrt_ne
  have h_quadratic :
      Tendsto
        (fun n : ℕ => -((x - meanSeq n) ^ 2) / (2 * varianceSeq n))
        atTop
        (𝓝 (-((x - mean) ^ 2) / (2 * variance))) := by
    have h_num :
        Tendsto (fun n : ℕ => -((x - meanSeq n) ^ 2))
          atTop (𝓝 (-((x - mean) ^ 2))) := by
      exact ((tendsto_const_nhds.sub mean_tendsto).pow 2).neg
    have h_den :
        Tendsto (fun n : ℕ => 2 * varianceSeq n) atTop (𝓝 (2 * variance)) := by
      exact tendsto_const_nhds.mul variance_tendsto
    exact h_num.div h_den h_variance_ne
  have h_exp :
      Tendsto
        (fun n : ℕ => Real.exp (-((x - meanSeq n) ^ 2) / (2 * varianceSeq n)))
        atTop
        (𝓝 (Real.exp (-((x - mean) ^ 2) / (2 * variance)))) := by
    exact (Real.continuous_exp.tendsto _).comp h_quadratic
  simpa [ex_10_3_2_gaussianPdf, one_div] using h_coeff.mul h_exp

structure ex_10_3_2_GaussianDensityConvergenceSetup where
  meanSeq : ℕ → ℝ
  varianceSeq : ℕ → ℝ
  mean : ℝ
  variance : ℝ
  mean_tendsto : Tendsto meanSeq atTop (𝓝 mean)
  variance_tendsto : Tendsto varianceSeq atTop (𝓝 variance)
  variance_pos : 0 < variance
  varianceSeq_pos : ∀ n : ℕ, 0 < varianceSeq n

theorem ex_10_3_2_gaussian_convergesInDistribution
    (S : ex_10_3_2_GaussianDensityConvergenceSetup) :
    MeasuresConvergeInDistribution
      (fun n : ℕ =>
        densityMeasure (ex_10_3_2_gaussianPdf (S.meanSeq n) (S.varianceSeq n)))
      (densityMeasure (ex_10_3_2_gaussianPdf S.mean S.variance)) :=
  ex_10_3_2_density_convergesInDistribution
    (fun n : ℕ => ex_10_3_2_gaussianPdf (S.meanSeq n) (S.varianceSeq n))
    (ex_10_3_2_gaussianPdf S.mean S.variance)
    (fun n : ℕ =>
      ex_10_3_2_gaussianPdf_isProbabilityDensity
        (S.meanSeq n) (S.varianceSeq_pos n))
    (ex_10_3_2_gaussianPdf_isProbabilityDensity S.mean S.variance_pos)
    (ex_10_3_2_gaussian_pdf_convergence
      S.meanSeq S.varianceSeq S.mean S.variance
      S.mean_tendsto S.variance_tendsto S.variance_pos)

theorem ex_10_3_2
    (fn : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hfn : ∀ n : ℕ, IsProbabilityDensity (fn n))
    (hf : IsProbabilityDensity f)
    (h_ae :
      ∀ᵐ x ∂(volume : Measure ℝ),
        Tendsto (fun n : ℕ => fn n x) atTop (𝓝 (f x))) :
    Tendsto (fun n : ℕ => ∫ x, |fn n x - f x| ∂(volume : Measure ℝ))
        atTop (𝓝 0) ∧
      MeasuresConvergeInTotalVariation
        (fun n : ℕ => densityMeasure (fn n)) (densityMeasure f) ∧
      MeasuresConvergeInDistribution
        (fun n : ℕ => densityMeasure (fn n)) (densityMeasure f) := by
  exact ⟨ex_10_3_2_scheffe_l1 fn f hfn hf h_ae,
    ex_10_3_2_totalVariation_convergence fn f hfn hf h_ae,
    ex_10_3_2_density_convergesInDistribution fn f hfn hf h_ae⟩
