/-
TASK ID: thm_8_5
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod








open MeasureTheory
open scoped ENNReal



theorem thm_8_5
    {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β)
    [SigmaFinite P] [SigmaFinite Q]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : α × β → E}
    (hf_meas : AEStronglyMeasurable f (P.prod Q))
    (hfinite :
      ((∫⁻ x, ∫⁻ y, ‖f (x, y)‖ₑ ∂Q ∂P) < ∞) ∨
      ((∫⁻ y, ∫⁻ x, ‖f (x, y)‖ₑ ∂P ∂Q) < ∞) ∨
      ((∫⁻ z, ‖f z‖ₑ ∂(P.prod Q)) < ∞)) :
    Integrable f (P.prod Q) ∧
      Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂Q) P ∧
      Integrable (fun y => ∫ x, ‖f (x, y)‖ ∂P) Q ∧
      (∫ x, ∫ y, f (x, y) ∂Q ∂P = ∫ y, ∫ x, f (x, y) ∂P ∂Q) ∧
      (∫ x, ∫ y, f (x, y) ∂Q ∂P = ∫ z, f z ∂(P.prod Q)) := by
  have hnorm_aemeas :
      AEMeasurable (fun z : α × β => ‖f z‖ₑ) (P.prod Q) :=
    hf_meas.enorm
  have hprod_lintegral :
      (∫⁻ z, ‖f z‖ₑ ∂(P.prod Q)) < ∞ := by
    rcases hfinite with hleft | hrest
    · rwa [MeasureTheory.lintegral_prod (fun z : α × β => ‖f z‖ₑ) hnorm_aemeas]
    · rcases hrest with hright | hprod
      · rwa [MeasureTheory.lintegral_prod_symm (fun z : α × β => ‖f z‖ₑ) hnorm_aemeas]
      · exact hprod
  have hf : Integrable f (P.prod Q) :=
    ⟨hf_meas, hprod_lintegral⟩
  have hswap :
      (∫ x, ∫ y, f (x, y) ∂Q ∂P) = ∫ y, ∫ x, f (x, y) ∂P ∂Q := by
    simpa using
      (integral_integral_swap (μ := P) (ν := Q) (f := fun x y => f (x, y)) hf)
  have hprod :
      (∫ z, f z ∂(P.prod Q)) = ∫ x, ∫ y, f (x, y) ∂Q ∂P := by
    simpa using (integral_prod (μ := P) (ν := Q) f hf)
  exact ⟨hf, hf.integral_norm_prod_left, hf.integral_norm_prod_right, hswap, hprod.symm⟩
