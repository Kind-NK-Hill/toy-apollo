/-
TASK ID: thm_11_3
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter11-bounds-inequalities
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_4_1
import ToyApollo.Output.thm_6_7__lemma_1

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

namespace Thm113Support

theorem expectation_mono_of_integrable_lower
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {f g : Ω → EReal} {x : EReal}
    (hf : textbookIntegrable P f) (hfx : expectation P f = some x)
    (hfg : ∀ ω, f ω ≤ g ω) :
    ∃ y : EReal, expectation P g = some y ∧ x ≤ y := by
  have hpos :
      Def65Support.posLIntegral P f ≤ Def65Support.posLIntegral P g := by
    unfold Def65Support.posLIntegral Def65Support.posPart
    exact lintegral_mono fun ω => EReal.toENNReal_le_toENNReal (hfg ω)
  have hneg :
      Def65Support.negLIntegral P g ≤ Def65Support.negLIntegral P f := by
    unfold Def65Support.negLIntegral Def65Support.negPart
    exact lintegral_mono fun ω =>
      EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hfg ω))
  have hf_defined :
      ¬ (Def65Support.posLIntegral P f = ⊤ ∧
        Def65Support.negLIntegral P f = ⊤) := by
    rintro ⟨_, hneg_top⟩
    exact (ne_of_lt hf.2) hneg_top
  have hg_neg_finite : Def65Support.negLIntegral P g < ⊤ :=
    lt_of_le_of_lt hneg hf.2
  have hg_defined :
      ¬ (Def65Support.posLIntegral P g = ⊤ ∧
        Def65Support.negLIntegral P g = ⊤) := by
    rintro ⟨_, hneg_top⟩
    exact (ne_of_lt hg_neg_finite) hneg_top
  let y : EReal :=
    (Def65Support.posLIntegral P g : EReal) -
      (Def65Support.negLIntegral P g : EReal)
  have hf_value :
      textbookIntegral P f =
        some ((Def65Support.posLIntegral P f : EReal) -
          (Def65Support.negLIntegral P f : EReal)) := by
    simp [textbookIntegral, hf_defined]
  have hg_value : textbookIntegral P g = some y := by
    simp [textbookIntegral, hg_defined, y]
  have hfx' : textbookIntegral P f = some x := by
    simpa [chapter6_expectation_eq_textbookIntegral] using hfx
  have hx :
      (Def65Support.posLIntegral P f : EReal) -
          (Def65Support.negLIntegral P f : EReal) = x :=
    Option.some.inj (hf_value.symm.trans hfx')
  refine ⟨y, ?_, ?_⟩
  · simpa [chapter6_expectation_eq_textbookIntegral] using hg_value
  · rw [← hx]
    exact EReal.sub_le_sub
      (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hpos)
      (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hneg)

end Thm113Support

theorem thm_11_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {φ : ℝ → ℝ} {X : Ω → ℝ}
    (hXrv : IsRealMeasurable X) (hφ : ConvexOn ℝ Set.univ φ)
    (hX : Integrable X P) :
    ∃ y : EReal,
      expectation P (fun ω => (φ (X ω) : EReal)) = some y ∧
        (φ (P[X]) : EReal) ≤ y := by
  let m : ℝ := P[X]
  let a : ℝ := derivWithin φ (Set.Iio m) m
  let b : ℝ := φ m - a * m
  let g : ℝ → ℝ := fun z => a * z + b
  have hm_interior : m ∈ interior (Set.univ : Set ℝ) := by simp
  have hg_eq : g m = φ m := by
    dsimp [g, b]
    ring
  have hg_le : ∀ z : ℝ, g z ≤ φ z := by
    intro z
    rcases lt_trichotomy z m with hzm | rfl | hmz
    · have hslope :
          slope φ z m ≤ derivWithin φ (Set.Iio m) m :=
        hφ.slope_le_leftDeriv_of_mem_interior (by simp) hm_interior hzm
      rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hzm)] at hslope
      dsimp [g, b, a]
      nlinarith
    · exact hg_eq.le
    · have hleft_right :
          derivWithin φ (Set.Iio m) m ≤ derivWithin φ (Set.Ioi m) m :=
        hφ.leftDeriv_le_rightDeriv_of_mem_interior hm_interior
      have hright_slope :
          derivWithin φ (Set.Ioi m) m ≤ slope φ m z :=
        hφ.rightDeriv_le_slope_of_mem_interior hm_interior (by simp) hmz
      have hslope : derivWithin φ (Set.Iio m) m ≤ slope φ m z :=
        hleft_right.trans hright_slope
      rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hmz)] at hslope
      dsimp [g, b, a]
      nlinarith
  have hX_meas : Measurable X := hXrv
  have hgX_meas : Measurable (fun ω => g (X ω)) := by
    exact (hX_meas.const_mul a).add measurable_const
  have hgX_integrable : Integrable (fun ω => g (X ω)) P := by
    exact (hX.const_mul a).add (integrable_const b)
  have hgX_integral : P[fun ω => g (X ω)] = φ m := by
    simp [g, b, integral_add (hX.const_mul a) (integrable_const b),
      integral_const_mul, m]
  have hgX_textbook :
      textbookIntegrable P (fun ω => (g (X ω) : EReal)) :=
    chapter6_mathlib_integrable_to_textbookIntegrable hgX_meas hgX_integrable
  have hgX_expectation :
      expectation P (fun ω => (g (X ω) : EReal)) = some (φ m : EReal) := by
    rw [chapter6_expectation_real_eq_integral hgX_meas hgX_integrable,
      hgX_integral]
  obtain ⟨y, hy, hle⟩ :=
    Thm113Support.expectation_mono_of_integrable_lower
      (f := fun ω => (g (X ω) : EReal))
      (g := fun ω => (φ (X ω) : EReal)) P hgX_textbook
      hgX_expectation (fun ω => EReal.coe_le_coe (hg_le (X ω)))
  exact ⟨y, hy, by simpa [m] using hle⟩
