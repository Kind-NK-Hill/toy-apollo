import Mathlib
import ToyApollo.Output.thm_14_1

/-!
Foundational moment-generating-function support for Chapter 14.

This file owns the task-neutral law-level MGF interface used by the MGF
convergence problems.  Analytic strip, Montel, and subsequence machinery remains
task-owned.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

/-- The moment generating function of a law on `ℝ`, using Mathlib's `mgf`
primitive. -/
def chapter14_mgfOfLaw (P : ProbabilityMeasure ℝ) (t : ℝ) : ℝ :=
  mgf (fun x : ℝ => x) (P : Measure ℝ) t

/-- The law characteristic function is the complex MGF of the identity random
variable on the imaginary axis. -/
theorem chapter14_characteristic_eq_complexMGF
    (P : ProbabilityMeasure ℝ) (t : ℝ) :
    thm_14_1_characteristicFunction P t =
      complexMGF (fun x : ℝ => x) (P : Measure ℝ) (t * Complex.I) := by
  simpa [thm_14_1_characteristicFunction] using
    (complexMGF_id_mul_I (μ := (P : Measure ℝ)) t).symm

/-- The textbook assumption that the MGF is finite on the closed interval
`[-δ,δ]`. -/
def chapter14_mgfDefinedOn
    (P : ProbabilityMeasure ℝ) (δ : ℝ) : Prop :=
  ∀ t : ℝ, t ∈ Set.Icc (-δ) δ →
    Integrable (fun x : ℝ => Real.exp (t * x)) (P : Measure ℝ)

/-- On the real axis, convergence of real MGFs is exactly convergence of complex
MGFs after coercing real points into `ℂ`. -/
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
