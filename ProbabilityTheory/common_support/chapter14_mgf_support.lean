/-
TASK ID: chapter14_mgf_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_14.thm_14_1




open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section



def chapter14_mgfOfLaw (P : ProbabilityMeasure ℝ) (t : ℝ) : ℝ :=
  mgf (fun x : ℝ => x) (P : Measure ℝ) t



theorem chapter14_characteristic_eq_complexMGF
    (P : ProbabilityMeasure ℝ) (t : ℝ) :
    thm_14_1_characteristicFunction P t =
      complexMGF (fun x : ℝ => x) (P : Measure ℝ) (t * Complex.I) := by
  change charFun (P : Measure ℝ) t =
    complexMGF id (P : Measure ℝ) (t * Complex.I)
  exact (complexMGF_id_mul_I (μ := (P : Measure ℝ)) t).symm



def chapter14_mgfDefinedOn
    (P : ProbabilityMeasure ℝ) (δ : ℝ) : Prop :=
  ∀ t : ℝ, t ∈ Set.Icc (-δ) δ →
    Integrable (fun x : ℝ => Real.exp (t * x)) (P : Measure ℝ)



theorem chapter14_real_axis_complexMGF_convergence_at
    (Pseq : ℕ → ProbabilityMeasure ℝ) (targetLaw : ProbabilityMeasure ℝ)
    {t : ℝ}
    (hReal :
      Tendsto (fun n : ℕ => chapter14_mgfOfLaw (Pseq n) t) atTop
        (𝓝 (chapter14_mgfOfLaw targetLaw t))) :
    Tendsto
      (fun n : ℕ => complexMGF (fun x : ℝ => x) (Pseq n : Measure ℝ) (t : ℂ))
      atTop
      (𝓝 (complexMGF (fun x : ℝ => x) (targetLaw : Measure ℝ) (t : ℂ))) := by
  have hComplex :
      Tendsto
        (fun n : ℕ => (chapter14_mgfOfLaw (Pseq n) t : ℂ))
        atTop
        (𝓝 (chapter14_mgfOfLaw targetLaw t : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hReal
  simpa [chapter14_mgfOfLaw, complexMGF_ofReal] using hComplex
