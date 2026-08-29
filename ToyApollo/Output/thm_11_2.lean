/-
TASK ID: thm_11_2
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter11-bounds-inequalities
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_9_1
import ToyApollo.Output.thm_10_3

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

theorem thm_11_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hXm : Measurable X) (hX : MemLp X 2 P)
    {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ |X ω - P[X]|} ≤
      _root_.variance P X (FiniteAbsMoment.of_memLp hXm hX) / ε ^ 2 := by
  let Y : Ω → ℝ := fun ω => (X ω - P[X]) ^ 2
  have hεsq_pos : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hY_nonneg : 0 ≤ᵐ[P] Y :=
    Filter.Eventually.of_forall fun ω => sq_nonneg (X ω - P[X])
  have hCentered : MemLp (fun ω => X ω - P[X]) 2 P := by
    convert hX.sub (memLp_const (P[X]) : MemLp (fun _ : Ω => P[X]) 2 P) using 1
    ext ω
    rfl
  have hY_int : Integrable Y P := by
    simpa [Y] using hCentered.integrable_sq
  have hMarkov :
      P.real {ω | ε ^ 2 ≤ Y ω} ≤ (∫ ω, Y ω ∂P) / ε ^ 2 :=
    thm_10_3 P Y hY_nonneg hY_int hεsq_pos
  have hsubset :
      {ω | ε ≤ |X ω - P[X]|} ⊆ {ω | ε ^ 2 ≤ Y ω} := by
    intro ω hω
    dsimp [Y]
    exact sq_le_sq.mpr (by simpa [abs_of_pos hε] using hω)
  have hmeasure :
      P.real {ω | ε ≤ |X ω - P[X]|} ≤ P.real {ω | ε ^ 2 ≤ Y ω} :=
    measureReal_mono (μ := P) hsubset
  have hvar :
      _root_.variance P X (FiniteAbsMoment.of_memLp hXm hX) =
        ∫ ω, Y ω ∂P := by
    rw [_root_.variance, rthCentralMoment]
    rw [ProbabilityTheory.centralMoment_two_eq_variance (μ := P) (X := X) hX.aemeasurable]
    rw [ProbabilityTheory.variance_eq_integral (μ := P) (X := X) hX.aemeasurable]
  calc
    P.real {ω | ε ≤ |X ω - P[X]|}
        ≤ P.real {ω | ε ^ 2 ≤ Y ω} := hmeasure
    _ ≤ (∫ ω, Y ω ∂P) / ε ^ 2 := hMarkov
    _ = _root_.variance P X (FiniteAbsMoment.of_memLp hXm hX) / ε ^ 2 := by
      rw [← hvar]
