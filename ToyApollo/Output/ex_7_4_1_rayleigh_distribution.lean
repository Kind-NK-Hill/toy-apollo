/-
TASK ID: ex_7_4_1_rayleigh_distribution
TYPE: Example_Proof
SOURCE PLAN: 28_chap7_pushforward_change_of_variable
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.prob_1_1
import ToyApollo.Output.thm_7_11

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

def gaussianVariance (σ : ℝ) : ℝ≥0 :=
  ⟨σ ^ 2, sq_nonneg σ⟩

noncomputable def gaussian1DMeasure (σ : ℝ) : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 (gaussianVariance σ)

noncomputable def gaussianPlaneMeasure (σ : ℝ) : Measure (ℝ × ℝ) :=
  (gaussian1DMeasure σ).prod (gaussian1DMeasure σ)

noncomputable def gaussianPlaneDensity (σ : ℝ) : ℝ × ℝ → ℝ≥0∞ :=
  fun p =>
    ProbabilityTheory.gaussianPDF 0 (gaussianVariance σ) p.1 *
      ProbabilityTheory.gaussianPDF 0 (gaussianVariance σ) p.2

def gaussianRadiusSq (p : ℝ × ℝ) : ℝ :=
  p.1 ^ 2 + p.2 ^ 2

def gaussianRadius (p : ℝ × ℝ) : ℝ :=
  Real.sqrt (gaussianRadiusSq p)

def gaussianDisk (z : ℝ) : Set (ℝ × ℝ) :=
  {p | gaussianRadiusSq p ≤ z ^ 2}

noncomputable instance gaussian1DMeasure_isProbabilityMeasure (σ : ℝ) :
    IsProbabilityMeasure (gaussian1DMeasure σ) := by
  unfold gaussian1DMeasure
  infer_instance

noncomputable instance gaussianPlaneMeasure_isProbabilityMeasure (σ : ℝ) :
    IsProbabilityMeasure (gaussianPlaneMeasure σ) := by
  unfold gaussianPlaneMeasure
  infer_instance

lemma gaussianVariance_pos {σ : ℝ} (hσ : 0 < σ) :
    0 < gaussianVariance σ := by
  exact_mod_cast sq_pos_of_pos hσ

lemma gaussianVariance_ne_zero {σ : ℝ} (hσ : 0 < σ) :
    gaussianVariance σ ≠ 0 := by
  exact (ne_of_gt (gaussianVariance_pos hσ))

lemma gaussianRadiusSq_nonneg (p : ℝ × ℝ) :
    0 ≤ gaussianRadiusSq p := by
  dsimp [gaussianRadiusSq]
  positivity

lemma gaussianRadiusSq_measurable :
    Measurable gaussianRadiusSq := by
  change Measurable (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2)
  exact (measurable_fst.pow_const (2 : ℕ)).add
    (measurable_snd.pow_const (2 : ℕ))

lemma gaussianRadius_measurable :
    Measurable gaussianRadius := by
  change Measurable (fun p : ℝ × ℝ => Real.sqrt (gaussianRadiusSq p))
  exact gaussianRadiusSq_measurable.sqrt

lemma measurableSet_gaussianDisk (z : ℝ) :
    MeasurableSet (gaussianDisk z) := by
  simpa [gaussianDisk] using
    measurableSet_le gaussianRadiusSq_measurable measurable_const

lemma gaussianRadius_preimage_Iic_nonneg {z : ℝ} (hz : 0 ≤ z) :
    gaussianRadius ⁻¹' Iic z = gaussianDisk z := by
  ext p
  simp [gaussianRadius, gaussianDisk, Real.sqrt_le_iff, hz]

lemma gaussianRadius_preimage_Iic_neg {z : ℝ} (hz : z < 0) :
    gaussianRadius ⁻¹' Iic z = ∅ := by
  ext p
  have hp : 0 ≤ gaussianRadius p := Real.sqrt_nonneg _
  have hnot : ¬ gaussianRadius p ≤ z := by
    linarith
  simp [hnot]

lemma sqrt_preimage_Iic_nonneg {z : ℝ} (hz : 0 ≤ z) :
    Real.sqrt ⁻¹' Iic z = Iic (z ^ 2) := by
  ext t
  simp [Real.sqrt_le_iff, hz]

lemma sqrt_preimage_Iic_neg {z : ℝ} (hz : z < 0) :
    Real.sqrt ⁻¹' Iic z = ∅ := by
  ext t
  have ht : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have hnot : ¬ Real.sqrt t ≤ z := by
    linarith
  simp [hnot]

lemma gaussianPlaneMeasure_eq_density (σ : ℝ) (hσ : 0 < σ) :
    gaussianPlaneMeasure σ =
      (volume : Measure (ℝ × ℝ)).withDensity (gaussianPlaneDensity σ) := by
  have hv : gaussianVariance σ ≠ 0 := gaussianVariance_ne_zero hσ
  unfold gaussianPlaneMeasure gaussian1DMeasure
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero 0 hv]
  rw [Measure.volume_eq_prod]
  change
    ((volume : Measure ℝ).withDensity
      (ProbabilityTheory.gaussianPDF 0 (gaussianVariance σ))).prod
      ((volume : Measure ℝ).withDensity
        (ProbabilityTheory.gaussianPDF 0 (gaussianVariance σ))) =
    ((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
      (fun z : ℝ × ℝ =>
        ProbabilityTheory.gaussianPDF 0 (gaussianVariance σ) z.1 *
        ProbabilityTheory.gaussianPDF 0 (gaussianVariance σ) z.2)
  exact prod_withDensity
    (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))
    (f := ProbabilityTheory.gaussianPDF 0 (gaussianVariance σ))
    (g := ProbabilityTheory.gaussianPDF 0 (gaussianVariance σ))
    (ProbabilityTheory.measurable_gaussianPDF 0 (gaussianVariance σ))
    (ProbabilityTheory.measurable_gaussianPDF 0 (gaussianVariance σ))

lemma gaussianPlaneMeasure_rectangle (σ x y : ℝ) (hσ : 0 < σ) :
    gaussianPlaneMeasure σ (Iic x ×ˢ Iic y) =
      ENNReal.ofReal
        (∫ u in Iic x, ProbabilityTheory.gaussianPDFReal 0 (gaussianVariance σ) u) *
      ENNReal.ofReal
        (∫ v in Iic y, ProbabilityTheory.gaussianPDFReal 0 (gaussianVariance σ) v) := by
  have hv : gaussianVariance σ ≠ 0 := gaussianVariance_ne_zero hσ
  unfold gaussianPlaneMeasure gaussian1DMeasure
  rw [Measure.prod_prod]
  rw [ProbabilityTheory.gaussianReal_apply_eq_integral 0 hv (Iic x)]
  rw [ProbabilityTheory.gaussianReal_apply_eq_integral 0 hv (Iic y)]

lemma gaussianPlaneMeasure_disk_as_lintegral (σ z : ℝ) (hσ : 0 < σ) :
    gaussianPlaneMeasure σ (gaussianDisk z) =
      ∫⁻ p in gaussianDisk z, gaussianPlaneDensity σ p ∂(volume : Measure (ℝ × ℝ)) := by
  rw [gaussianPlaneMeasure_eq_density σ hσ]
  rw [MeasureTheory.withDensity_apply _ (measurableSet_gaussianDisk z)]

lemma gaussianRadiusSq_distribution (σ : ℝ) (hσ : 0 < σ) :
    Measure.map gaussianRadiusSq (gaussianPlaneMeasure σ) =
      ProbabilityTheory.expMeasure ((2 * σ ^ 2)⁻¹) := by
  have hv : ((gaussianVariance σ : ℝ)) > 0 := by
    exact_mod_cast sq_pos_of_pos hσ
  have hvar : (gaussianVariance σ : ℝ) = σ ^ 2 := by
    change σ ^ 2 = σ ^ 2
    rfl
  change Measure.map (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2)
      ((ProbabilityTheory.gaussianReal 0 (gaussianVariance σ)).prod
       (ProbabilityTheory.gaussianReal 0 (gaussianVariance σ))) =
    ProbabilityTheory.expMeasure ((2 * σ ^ 2)⁻¹)
  simpa only [hvar] using
    gaussianReal_sq_sum_eq_expMeasure (gaussianVariance σ) hv

lemma gaussianRadius_distribution (σ : ℝ) (hσ : 0 < σ) :
    Measure.map gaussianRadius (gaussianPlaneMeasure σ) =
      Measure.map Real.sqrt (ProbabilityTheory.expMeasure ((2 * σ ^ 2)⁻¹)) := by
  have hsqrt_meas : Measurable (fun x : ℝ => Real.sqrt x) := by
    fun_prop
  calc
    Measure.map gaussianRadius (gaussianPlaneMeasure σ)
      = Measure.map Real.sqrt (Measure.map gaussianRadiusSq (gaussianPlaneMeasure σ)) := by
          rw [show gaussianRadius = Real.sqrt ∘ gaussianRadiusSq by
            funext p
            rfl]
          rw [← Measure.map_map hsqrt_meas gaussianRadiusSq_measurable]
    _ = Measure.map Real.sqrt (ProbabilityTheory.expMeasure ((2 * σ ^ 2)⁻¹)) := by
          rw [gaussianRadiusSq_distribution σ hσ]

lemma gaussianRadius_cdf (σ z : ℝ) (hσ : 0 < σ) :
    ProbabilityTheory.cdf (Measure.map gaussianRadius (gaussianPlaneMeasure σ)) z =
      if 0 ≤ z then 1 - Real.exp (-(z ^ 2 / (2 * σ ^ 2))) else 0 := by
  have hrate : 0 < ((2 * σ ^ 2)⁻¹) := by positivity
  have hsqrt_meas : Measurable (fun x : ℝ => Real.sqrt x) := by
    fun_prop
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure ((2 * σ ^ 2)⁻¹)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  haveI : IsProbabilityMeasure
      (Measure.map Real.sqrt (ProbabilityTheory.expMeasure ((2 * σ ^ 2)⁻¹))) :=
    Measure.isProbabilityMeasure_map hsqrt_meas.aemeasurable
  rw [gaussianRadius_distribution σ hσ]
  by_cases hz : 0 ≤ z
  · rw [ProbabilityTheory.cdf_eq_real]
    rw [MeasureTheory.map_measureReal_apply hsqrt_meas measurableSet_Iic]
    rw [sqrt_preimage_Iic_nonneg hz]
    rw [← ProbabilityTheory.cdf_eq_real (μ := ProbabilityTheory.expMeasure ((2 * σ ^ 2)⁻¹))
      (x := z ^ 2)]
    rw [ProbabilityTheory.cdf_expMeasure_eq hrate]
    have hzsq : 0 ≤ z ^ 2 := by positivity
    rw [if_pos hzsq]
    simp only [hz, if_true]
    congr 1
    field_simp [hσ.ne']
  · rw [ProbabilityTheory.cdf_eq_real]
    rw [MeasureTheory.map_measureReal_apply hsqrt_meas measurableSet_Iic]
    rw [sqrt_preimage_Iic_neg (lt_of_not_ge hz)]
    simp [hz]

lemma gaussianRadius_change_of_variable (σ : ℝ) {g : ℝ → ℝ}
    (hg : Measurable g) :
    (Integrable (fun p : ℝ × ℝ => g (gaussianRadius p)) (gaussianPlaneMeasure σ) ↔
        Integrable g (Measure.map gaussianRadius (gaussianPlaneMeasure σ))) ∧
      (∫ p : ℝ × ℝ, g (gaussianRadius p) ∂gaussianPlaneMeasure σ =
        ∫ x : ℝ, g x ∂Measure.map gaussianRadius (gaussianPlaneMeasure σ)) := by
  simpa [gaussianRadius] using
    (thm_7_11 (μ := gaussianPlaneMeasure σ)
      (X := gaussianRadius) (hX := gaussianRadius_measurable) (hh := hg))

theorem ex_7_4_1_rayleigh_distribution (σ : ℝ) (hσ : 0 < σ) :
    let P := gaussianPlaneMeasure σ
    let Z := gaussianRadius
    P Set.univ = 1 ∧
      (∀ x y : ℝ,
        P (Iic x ×ˢ Iic y) =
          ENNReal.ofReal
            (∫ u in Iic x, ProbabilityTheory.gaussianPDFReal 0 (gaussianVariance σ) u) *
          ENNReal.ofReal
            (∫ v in Iic y, ProbabilityTheory.gaussianPDFReal 0 (gaussianVariance σ) v)) ∧
      (∀ z : ℝ, 0 ≤ z →
        P (Z ⁻¹' Iic z) =
          ∫⁻ p in gaussianDisk z, gaussianPlaneDensity σ p ∂(volume : Measure (ℝ × ℝ))) ∧
      (Measure.map Z P =
        Measure.map Real.sqrt (ProbabilityTheory.expMeasure ((2 * σ ^ 2)⁻¹))) ∧
      (∀ z : ℝ,
        ProbabilityTheory.cdf (Measure.map Z P) z =
          if 0 ≤ z then 1 - Real.exp (-(z ^ 2 / (2 * σ ^ 2))) else 0) ∧
      (∀ {g : ℝ → ℝ}, Measurable g →
        (Integrable (fun p : ℝ × ℝ => g (Z p)) P ↔ Integrable g (Measure.map Z P)) ∧
          (∫ p : ℝ × ℝ, g (Z p) ∂P = ∫ x : ℝ, g x ∂Measure.map Z P)) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using (MeasureTheory.measure_univ (gaussianPlaneMeasure σ))
  · intro x y
    exact gaussianPlaneMeasure_rectangle σ x y hσ
  · intro z hz
    rw [gaussianRadius_preimage_Iic_nonneg hz]
    exact gaussianPlaneMeasure_disk_as_lintegral σ z hσ
  · exact gaussianRadius_distribution σ hσ
  · intro z
    exact gaussianRadius_cdf σ z hσ
  · intro g hg
    exact gaussianRadius_change_of_variable σ hg
