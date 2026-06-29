/-
TASK ID: thm_6_6
TYPE: Theorem_with_Proof
SOURCE PLAN: 21_chap6_real_complex_functions
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_6_3

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

namespace Thm66Support

noncomputable def posPart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → EReal) : Ω → ENNReal :=
  fun ω => (X ω).toENNReal

noncomputable def negPart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → EReal) : Ω → ENNReal :=
  fun ω => (-X ω).toENNReal

noncomputable def posLIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EReal) : ENNReal :=
  ∫⁻ ω, posPart X ω ∂μ

noncomputable def negLIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EReal) : ENNReal :=
  ∫⁻ ω, negPart X ω ∂μ

def textbookIntegrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EReal) : Prop :=
  posLIntegral μ X < ⊤ ∧ negLIntegral μ X < ⊤

noncomputable def realAbsIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EReal) : ENNReal :=
  posLIntegral μ X + negLIntegral μ X

noncomputable def realPartAbsIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℂ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal |(Z ω).re| ∂μ

noncomputable def imagPartAbsIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℂ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal |(Z ω).im| ∂μ

def complexTextbookIntegrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℂ) : Prop :=
  realPartAbsIntegral μ Z < ⊤ ∧ imagPartAbsIntegral μ Z < ⊤

noncomputable def complexAbsIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℂ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal ‖Z ω‖ ∂μ

theorem textbookIntegrable_iff_realAbsIntegral_lt_top {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → EReal) :
    textbookIntegrable μ X ↔ realAbsIntegral μ X < ⊤ := by
  constructor
  · intro hX
    simpa [textbookIntegrable, realAbsIntegral] using (ENNReal.add_lt_top.mpr hX)
  · intro hAbs
    constructor
    · exact lt_of_le_of_lt (le_add_of_nonneg_right bot_le) (by simpa [realAbsIntegral] using hAbs)
    · exact lt_of_le_of_lt (le_add_of_nonneg_left bot_le) (by simpa [realAbsIntegral] using hAbs)

theorem complexTextbookIntegrable_iff_complexAbsIntegral_lt_top {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℂ) (hZm : Measurable Z) :
    complexTextbookIntegrable μ Z ↔ complexAbsIntegral μ Z < ⊤ := by
  constructor
  · intro hZ
    have h_pointwise :
        (fun ω => ENNReal.ofReal ‖Z ω‖) ≤
          fun ω => ENNReal.ofReal |(Z ω).re| + ENNReal.ofReal |(Z ω).im| := by
      intro ω
      simpa [ENNReal.ofReal_add, abs_nonneg, add_comm, add_left_comm, add_assoc] using
        ENNReal.ofReal_le_ofReal (Complex.norm_le_abs_re_add_abs_im (Z ω))
    have h_meas_re : Measurable fun ω => ENNReal.ofReal |(Z ω).re| := by
      exact Measurable.ennreal_ofReal ((Complex.continuous_re.measurable.comp hZm).abs)
    have h_rhs_top :
        ∫⁻ ω, (ENNReal.ofReal |(Z ω).re| + ENNReal.ofReal |(Z ω).im|) ∂μ < ⊤ := by
      have hsum :
          ∫⁻ ω, (ENNReal.ofReal |(Z ω).re| + ENNReal.ofReal |(Z ω).im|) ∂μ =
            realPartAbsIntegral μ Z + imagPartAbsIntegral μ Z := by
        rw [lintegral_add_left h_meas_re]
        · simp [realPartAbsIntegral, imagPartAbsIntegral]
      rw [hsum]
      exact ENNReal.add_lt_top.mpr hZ
    exact lt_of_le_of_lt (lintegral_mono h_pointwise) h_rhs_top
  · intro hAbs
    constructor
    · refine lt_of_le_of_lt ?_ hAbs
      apply lintegral_mono
      intro ω
      exact ENNReal.ofReal_le_ofReal (Complex.abs_re_le_norm (Z ω))
    · refine lt_of_le_of_lt ?_ hAbs
      apply lintegral_mono
      intro ω
      exact ENNReal.ofReal_le_ofReal (Complex.abs_im_le_norm (Z ω))

end Thm66Support

theorem thm_6_6 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → EReal)
    (_hXm : Measurable X) :
    ((∫⁻ ω, (X ω).toENNReal ∂μ) < ⊤ ∧
        (∫⁻ ω, (-X ω).toENNReal ∂μ) < ⊤) ↔
      (∫⁻ ω, (X ω).toENNReal ∂μ) + (∫⁻ ω, (-X ω).toENNReal ∂μ) < ⊤ := by
  simpa [Thm66Support.textbookIntegrable, Thm66Support.realAbsIntegral,
    Thm66Support.posLIntegral, Thm66Support.negLIntegral, Thm66Support.posPart, Thm66Support.negPart]
    using Thm66Support.textbookIntegrable_iff_realAbsIntegral_lt_top μ X

theorem thm_6_6_complex {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℂ)
    (hZm : Measurable Z) :
    ((∫⁻ ω, ENNReal.ofReal |(Z ω).re| ∂μ) < ⊤ ∧
        (∫⁻ ω, ENNReal.ofReal |(Z ω).im| ∂μ) < ⊤) ↔
      (∫⁻ ω, ENNReal.ofReal ‖Z ω‖ ∂μ) < ⊤ := by
  simpa [Thm66Support.complexTextbookIntegrable, Thm66Support.complexAbsIntegral,
    Thm66Support.realPartAbsIntegral, Thm66Support.imagPartAbsIntegral]
    using Thm66Support.complexTextbookIntegrable_iff_complexAbsIntegral_lt_top μ Z hZm
