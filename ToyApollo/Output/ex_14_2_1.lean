/-
TASK ID: ex_14_2_1
TYPE: Example_Proof
SOURCE PLAN: chapter14-tightness
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_14_3

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set
open scoped Topology ENNReal

noncomputable section

def ex_14_2_1_uniformPdf (n : ℕ) (x : ℝ) : ℝ :=
  ((2 * ((n : ℝ) + 1))⁻¹) *
    (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)).indicator (fun _ => (1 : ℝ)) x

def ex_14_2_1_intervalFiniteMeasure (n : ℕ) : FiniteMeasure ℝ :=
  (⟨volume.restrict (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)), inferInstance⟩ :
    FiniteMeasure ℝ)

def ex_14_2_1_uniformMeasure (n : ℕ) : ProbabilityMeasure ℝ :=
  MeasureTheory.FiniteMeasure.normalize (ex_14_2_1_intervalFiniteMeasure n)

def ex_14_2_1_uniformMeasures : ℕ → ProbabilityMeasure ℝ :=
  fun n => ex_14_2_1_uniformMeasure n

def ex_14_2_1_pdfRepresentsMeasure
    (P : ProbabilityMeasure ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ s : Set ℝ, MeasurableSet s → (P : Measure ℝ).real s = ∫ x in s, f x

def ex_14_2_1_textbookIntervalMass (M : ℝ) (n : ℕ) : ℝ :=
  M / ((n : ℝ) + 1)

theorem ex_14_2_1_textbookIntervalMass_tendsto_zero (M : ℝ) :
    Tendsto (fun n : ℕ => ex_14_2_1_textbookIntervalMass M n) atTop (𝓝 0) := by
  unfold ex_14_2_1_textbookIntervalMass
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (tendsto_const_nhds (x := M)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem ex_14_2_1_intervalFiniteMeasure_ne_zero (n : ℕ) :
    ex_14_2_1_intervalFiniteMeasure n ≠ 0 := by
  intro hzero
  have hval :
      (ex_14_2_1_intervalFiniteMeasure n : Measure ℝ) Set.univ = 0 := by
    rw [hzero]
    simp
  have hpos :
      (0 : ℝ≥0∞) <
        (ex_14_2_1_intervalFiniteMeasure n : Measure ℝ) Set.univ := by
    change
      (0 : ℝ≥0∞) <
        (volume.restrict (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))) Set.univ
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc]
    have hn : 0 < 2 * ((n : ℝ) + 1) := by positivity
    have hdiff :
        ((n : ℝ) + 1) - (-((n : ℝ) + 1)) =
          2 * ((n : ℝ) + 1) := by
      ring
    rw [hdiff]
    exact ENNReal.ofReal_pos.mpr hn
  rw [hval] at hpos
  exact (lt_irrefl (0 : ℝ≥0∞) hpos).elim

theorem ex_14_2_1_intervalFiniteMeasure_mass (n : ℕ) :
    ↑(ex_14_2_1_intervalFiniteMeasure n).mass =
      ENNReal.ofReal (2 * ((n : ℝ) + 1)) := by
  rw [FiniteMeasure.ennreal_mass]
  change
    (volume.restrict (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))) Set.univ =
      ENNReal.ofReal (2 * ((n : ℝ) + 1))
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc]
  congr 1
  ring

theorem ex_14_2_1_restrictedIntervalMeasure_Icc
    (n : ℕ) (M : ℝ) (hMle : M ≤ (n : ℝ) + 1) :
    (ex_14_2_1_intervalFiniteMeasure n : Measure ℝ) (Icc (-M) M) =
      ENNReal.ofReal (2 * M) := by
  change
    (volume.restrict (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))) (Icc (-M) M) =
      ENNReal.ofReal (2 * M)
  rw [Measure.restrict_apply measurableSet_Icc]
  have hset :
      Icc (-M) M ∩ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) =
        Icc (-M) M := by
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hx
      refine ⟨hx, ?_⟩
      constructor
      · have hneg : -((n : ℝ) + 1) ≤ -M := by
          linarith
        exact hneg.trans hx.1
      · exact hx.2.trans hMle
  rw [hset, Real.volume_Icc]
  have hdiff : M - (-M) = 2 * M := by
    ring
  rw [hdiff]

theorem ex_14_2_1_intervalMass_eq_textbook
    (n : ℕ) (M : ℝ) (hM_nonneg : 0 ≤ M) (hMle : M ≤ (n : ℝ) + 1) :
    (ex_14_2_1_uniformMeasures n : Measure ℝ).real (Icc (-M) M) =
      ex_14_2_1_textbookIntervalMass M n := by
  let μ : FiniteMeasure ℝ :=
    ex_14_2_1_intervalFiniteMeasure n
  have hnonzero : μ ≠ 0 := by
    simpa [μ] using ex_14_2_1_intervalFiniteMeasure_ne_zero n
  have hmass : ↑μ.mass = ENNReal.ofReal (2 * ((n : ℝ) + 1)) := by
    simpa [μ] using ex_14_2_1_intervalFiniteMeasure_mass n
  have hset :
      (μ : Measure ℝ) (Icc (-M) M) = ENNReal.ofReal (2 * M) := by
    simpa [μ] using ex_14_2_1_restrictedIntervalMeasure_Icc n M hMle
  have hmass_ne : μ.mass ≠ 0 := μ.mass_nonzero_iff.mpr hnonzero
  have hNpos : 0 < 2 * ((n : ℝ) + 1) := by positivity
  have hMnonneg : 0 ≤ 2 * M := by nlinarith
  rw [ex_14_2_1_uniformMeasures, ex_14_2_1_uniformMeasure]
  change (μ.normalize : Measure ℝ).real (Icc (-M) M) =
    ex_14_2_1_textbookIntervalMass M n
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero (μ := μ) hnonzero]
  rw [Measure.real, Measure.coe_smul, Pi.smul_apply, Measure.nnreal_smul_coe_apply]
  rw [ENNReal.coe_inv hmass_ne, hmass, hset, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hNpos.le,
    ENNReal.toReal_ofReal hMnonneg]
  unfold ex_14_2_1_textbookIntervalMass
  field_simp [show (2 * ((n : ℝ) + 1)) ≠ 0 by positivity]

theorem ex_14_2_1_uniformPdf_represents_measure (n : ℕ) :
    ex_14_2_1_pdfRepresentsMeasure
      (ex_14_2_1_uniformMeasure n) (ex_14_2_1_uniformPdf n) := by
  intro s hs
  let I : Set ℝ := Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)
  let μ : FiniteMeasure ℝ := ex_14_2_1_intervalFiniteMeasure n
  have hnonzero : μ ≠ 0 := by
    simpa [μ] using ex_14_2_1_intervalFiniteMeasure_ne_zero n
  have hmass : ↑μ.mass = ENNReal.ofReal (2 * ((n : ℝ) + 1)) := by
    simpa [μ] using ex_14_2_1_intervalFiniteMeasure_mass n
  have hmass_ne : μ.mass ≠ 0 := μ.mass_nonzero_iff.mpr hnonzero
  have hNpos : 0 < 2 * ((n : ℝ) + 1) := by positivity
  have hμs : (μ : Measure ℝ) s = volume (s ∩ I) := by
    change (volume.restrict I) s = volume (s ∩ I)
    rw [Measure.restrict_apply hs]
  have hleft :
      (ex_14_2_1_uniformMeasure n : Measure ℝ).real s =
        (2 * ((n : ℝ) + 1))⁻¹ * volume.real (s ∩ I) := by
    rw [ex_14_2_1_uniformMeasure]
    change (μ.normalize : Measure ℝ).real s = _
    rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero (μ := μ) hnonzero]
    rw [Measure.real, Measure.coe_smul, Pi.smul_apply, Measure.nnreal_smul_coe_apply]
    rw [ENNReal.coe_inv hmass_ne, hmass, hμs, ENNReal.toReal_mul,
      ENNReal.toReal_inv, ENNReal.toReal_ofReal hNpos.le]
    rw [Measure.real_def]
  have hright :
      ∫ x in s, ex_14_2_1_uniformPdf n x =
        (2 * ((n : ℝ) + 1))⁻¹ * volume.real (s ∩ I) := by
    unfold ex_14_2_1_uniformPdf
    change
      ∫ x in s,
          (2 * ((n : ℝ) + 1))⁻¹ * I.indicator (fun _ => (1 : ℝ)) x =
        (2 * ((n : ℝ) + 1))⁻¹ * volume.real (s ∩ I)
    rw [integral_const_mul]
    have hI :
        (∫ a : ℝ, I.indicator (fun _ : ℝ => (1 : ℝ)) a ∂(volume.restrict s)) =
          (volume.restrict s).real I := by
      simpa only [Pi.one_apply] using
        (integral_indicator_one (μ := volume.restrict s) (s := I) measurableSet_Icc)
    rw [hI]
    rw [measureReal_restrict_apply measurableSet_Icc]
    rw [inter_comm]
  rw [hleft, hright]

theorem ex_14_2_1_interval_mass_eventually_eq_textbook
    (M : ℝ) (hM : 0 ≤ M) :
    (fun n : ℕ => (ex_14_2_1_uniformMeasures n : Measure ℝ).real (Icc (-M) M))
      =ᶠ[atTop] fun n : ℕ => ex_14_2_1_textbookIntervalMass M n := by
  have hEventually : ∀ᶠ n : ℕ in atTop, M ≤ (n : ℝ) + 1 := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (M - 1)] with n hn
    linarith
  filter_upwards [hEventually] with n hn
  exact ex_14_2_1_intervalMass_eq_textbook n M hM hn

theorem ex_14_2_1_interval_probability_tendsto_zero
    (M : ℝ) (hM : 0 ≤ M) :
    Tendsto
      (fun n : ℕ => (ex_14_2_1_uniformMeasures n : Measure ℝ).real (Icc (-M) M))
      atTop (𝓝 0) := by
  exact (ex_14_2_1_textbookIntervalMass_tendsto_zero M).congr'
    (ex_14_2_1_interval_mass_eventually_eq_textbook M hM).symm

theorem ex_14_2_1_not_tight :
    ¬ def_14_3 ex_14_2_1_uniformMeasures := by
  intro htight
  rcases htight (1 / 2) (by norm_num) with ⟨M, hM_nonneg, hM_mass⟩
  have hsmall_formula :
      ∀ᶠ n : ℕ in atTop, ex_14_2_1_textbookIntervalMass M n < 1 / 2 :=
    (ex_14_2_1_textbookIntervalMass_tendsto_zero M).eventually_lt_const (by norm_num)
  have hsmall_actual :
      ∀ᶠ n : ℕ in atTop,
        (ex_14_2_1_uniformMeasures n : Measure ℝ).real (Icc (-M) M) < 1 / 2 := by
    filter_upwards [ex_14_2_1_interval_mass_eventually_eq_textbook M hM_nonneg,
      hsmall_formula] with n hmass hsmall
    simpa [hmass] using hsmall
  rcases eventually_atTop.1 hsmall_actual with ⟨N, hN⟩
  have hlt :
      (ex_14_2_1_uniformMeasures N : Measure ℝ).real (Icc (-M) M) < 1 / 2 :=
    hN N le_rfl
  have hgt :
      1 / 2 < (ex_14_2_1_uniformMeasures N : Measure ℝ).real (Icc (-M) M) := by
    have hgt' := hM_mass N
    norm_num at hgt'
    exact hgt'
  linarith

theorem ex_14_2_1 :
    ¬ def_14_3 ex_14_2_1_uniformMeasures :=
  ex_14_2_1_not_tight
