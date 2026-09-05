/-
TASK ID: thm_14_3
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter14-weak-convergence
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_14.def_14_2




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology

noncomputable section

 
def thm_14_3_characteristicFunction
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (t : ℝ) : ℂ :=
  charFun (Measure.map X μ) t

 
def thm_14_3_cosTest (t : ℝ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : ℝ => Real.cos (t * x))
    (by fun_prop)
    1
    (by
      intro x
      simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (t * x))

 
def thm_14_3_sinTest (t : ℝ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : ℝ => Real.sin (t * x))
    (by fun_prop)
    1
    (by
      intro x
      simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (t * x))

 
theorem thm_14_3_cos_expectations
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Xseq : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X)
    (hWeak : def_14_2 μ Xseq X hXseq hX) :
    ∀ t : ℝ,
      Tendsto (fun n : ℕ => ∫ ω, Real.cos (t * Xseq n ω) ∂μ) atTop
        (𝓝 (∫ ω, Real.cos (t * X ω) ∂μ)) := by
  intro t
  have htests := (def_14_2_iff_expectations μ hXseq hX).mp hWeak
  simpa [thm_14_3_cosTest] using htests (thm_14_3_cosTest t)

 
theorem thm_14_3_sin_expectations
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Xseq : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X)
    (hWeak : def_14_2 μ Xseq X hXseq hX) :
    ∀ t : ℝ,
      Tendsto (fun n : ℕ => ∫ ω, Real.sin (t * Xseq n ω) ∂μ) atTop
        (𝓝 (∫ ω, Real.sin (t * X ω) ∂μ)) := by
  intro t
  have htests := (def_14_2_iff_expectations μ hXseq hX).mp hWeak
  simpa [thm_14_3_sinTest] using htests (thm_14_3_sinTest t)



theorem thm_14_3_characteristicFunction_cos_sin
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) (t : ℝ) :
    thm_14_3_characteristicFunction μ X t =
      ((∫ ω, Real.cos (t * X ω) ∂μ : ℝ) : ℂ) +
        ((∫ ω, Real.sin (t * X ω) ∂μ : ℝ) : ℂ) * Complex.I := by
  unfold thm_14_3_characteristicFunction
  rw [charFun_apply_real]
  rw [integral_map hX.aemeasurable (by fun_prop)]
  have hEuler :
      (fun x : Ω => Complex.exp ((t : ℂ) * (X x : ℂ) * Complex.I)) =
        fun x => ((Real.cos (t * X x) : ℝ) : ℂ) +
          ((Real.sin (t * X x) : ℝ) : ℂ) * Complex.I := by
    funext x
    rw [← Complex.ofReal_mul]
    rw [Complex.exp_mul_I]
    simp
  rw [hEuler]
  have hCosInt :
      Integrable (fun x : Ω => ((Real.cos (t * X x) : ℝ) : ℂ)) μ := by
    refine Integrable.of_bound ?_ 1 ?_
    · fun_prop
    · exact ae_of_all μ fun x => by
        rw [Complex.norm_real]
        exact Real.abs_cos_le_one (t * X x)
  have hSinInt :
      Integrable (fun x : Ω => ((Real.sin (t * X x) : ℝ) : ℂ)) μ := by
    refine Integrable.of_bound ?_ 1 ?_
    · fun_prop
    · exact ae_of_all μ fun x => by
        rw [Complex.norm_real]
        exact Real.abs_sin_le_one (t * X x)
  have hCosIntegral :
      ∫ x : Ω, ((Real.cos (t * X x) : ℝ) : ℂ) ∂μ =
        ((∫ x : Ω, Real.cos (t * X x) ∂μ : ℝ) : ℂ) := by
    exact integral_ofReal
  have hSinIntegral :
      ∫ x : Ω, ((Real.sin (t * X x) : ℝ) : ℂ) ∂μ =
        ((∫ x : Ω, Real.sin (t * X x) ∂μ : ℝ) : ℂ) := by
    exact integral_ofReal
  rw [integral_add hCosInt (hSinInt.mul_const Complex.I)]
  rw [hCosIntegral]
  rw [show ∫ a : Ω, ((Real.sin (t * X a) : ℝ) : ℂ) * Complex.I ∂μ =
      (∫ a : Ω, ((Real.sin (t * X a) : ℝ) : ℂ) ∂μ) * Complex.I by
        exact integral_mul_const Complex.I
          (fun a : Ω => ((Real.sin (t * X a) : ℝ) : ℂ))]
  rw [hSinIntegral]



theorem thm_14_3_recombine
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Xseq : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X)
    (hCos :
      ∀ t : ℝ,
        Tendsto (fun n : ℕ => ∫ ω, Real.cos (t * Xseq n ω) ∂μ) atTop
          (𝓝 (∫ ω, Real.cos (t * X ω) ∂μ)))
    (hSin :
      ∀ t : ℝ,
        Tendsto (fun n : ℕ => ∫ ω, Real.sin (t * Xseq n ω) ∂μ) atTop
          (𝓝 (∫ ω, Real.sin (t * X ω) ∂μ))) :
    ∀ t : ℝ,
      Tendsto (fun n : ℕ => thm_14_3_characteristicFunction μ (Xseq n) t) atTop
        (𝓝 (thm_14_3_characteristicFunction μ X t)) := by
  intro t
  have hcosC :
      Tendsto
        (fun n : ℕ => ((∫ ω, Real.cos (t * Xseq n ω) ∂μ : ℝ) : ℂ))
        atTop
        (𝓝 ((∫ ω, Real.cos (t * X ω) ∂μ : ℝ) : ℂ)) :=
    Filter.tendsto_ofReal_iff.mpr (hCos t)
  have hsinC :
      Tendsto
        (fun n : ℕ => ((∫ ω, Real.sin (t * Xseq n ω) ∂μ : ℝ) : ℂ))
        atTop
        (𝓝 ((∫ ω, Real.sin (t * X ω) ∂μ : ℝ) : ℂ)) :=
    Filter.tendsto_ofReal_iff.mpr (hSin t)
  have hsum := hcosC.add (hsinC.mul_const Complex.I)
  have hrewrite :
      (fun n : ℕ => ((∫ ω, Real.cos (t * Xseq n ω) ∂μ : ℝ) : ℂ) +
        ((∫ ω, Real.sin (t * Xseq n ω) ∂μ : ℝ) : ℂ) * Complex.I)
        =
      (fun n : ℕ => thm_14_3_characteristicFunction μ (Xseq n) t) := by
    funext n
    exact (thm_14_3_characteristicFunction_cos_sin μ (hXseq n) t).symm
  rw [thm_14_3_characteristicFunction_cos_sin μ hX t]
  simpa [← hrewrite] using hsum



theorem thm_14_3
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X)
    (hWeak : def_14_2 μ Xseq X hXseq hX) :
    ∀ t : ℝ,
      Tendsto (fun n : ℕ => thm_14_3_characteristicFunction μ (Xseq n) t) atTop
        (𝓝 (thm_14_3_characteristicFunction μ X t)) := by
  have hCos := thm_14_3_cos_expectations μ hXseq hX hWeak
  have hSin := thm_14_3_sin_expectations μ hXseq hX hWeak
  exact thm_14_3_recombine μ hXseq hX hCos hSin



theorem thm_14_3_sourceRouteCertificate
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X)
    (hWeak : def_14_2 μ Xseq X hXseq hX) :
    (∀ t : ℝ,
      Tendsto (fun n : ℕ => ∫ ω, Real.cos (t * Xseq n ω) ∂μ) atTop
        (𝓝 (∫ ω, Real.cos (t * X ω) ∂μ))) ∧
    (∀ t : ℝ,
      Tendsto (fun n : ℕ => ∫ ω, Real.sin (t * Xseq n ω) ∂μ) atTop
        (𝓝 (∫ ω, Real.sin (t * X ω) ∂μ))) ∧
    (∀ t : ℝ,
      Tendsto (fun n : ℕ => thm_14_3_characteristicFunction μ (Xseq n) t) atTop
        (𝓝 (thm_14_3_characteristicFunction μ X t))) := by
  refine ⟨?_, ?_, ?_⟩
  · exact thm_14_3_cos_expectations μ hXseq hX hWeak
  · exact thm_14_3_sin_expectations μ hXseq hX hWeak
  · exact thm_14_3 μ Xseq X hXseq hX hWeak



structure thm_14_3_CosSinProofSpine
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop where
  cos_expectations :
    ∀ t : ℝ,
      Tendsto (fun n : ℕ => ∫ ω, Real.cos (t * Xseq n ω) ∂μ) atTop
        (𝓝 (∫ ω, Real.cos (t * X ω) ∂μ))
  sin_expectations :
    ∀ t : ℝ,
      Tendsto (fun n : ℕ => ∫ ω, Real.sin (t * Xseq n ω) ∂μ) atTop
        (𝓝 (∫ ω, Real.sin (t * X ω) ∂μ))
  characteristic_convergence :
    ∀ t : ℝ,
      Tendsto (fun n : ℕ => thm_14_3_characteristicFunction μ (Xseq n) t) atTop
        (𝓝 (thm_14_3_characteristicFunction μ X t))

 
theorem thm_14_3_cosSinProofSpine
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X)
    (hWeak : def_14_2 μ Xseq X hXseq hX) :
    thm_14_3_CosSinProofSpine μ Xseq X where
  cos_expectations := thm_14_3_cos_expectations μ hXseq hX hWeak
  sin_expectations := thm_14_3_sin_expectations μ hXseq hX hWeak
  characteristic_convergence := thm_14_3 μ Xseq X hXseq hX hWeak
