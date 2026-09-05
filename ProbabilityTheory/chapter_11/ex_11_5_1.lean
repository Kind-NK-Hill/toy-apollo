/-
TASK ID: ex_11_5_1
TYPE: Example_Proof
SOURCE PLAN: chapter11-strong-law-large-numbers
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_11.thm_11_5
import ProbabilityTheory.chapter_11.thm_11_8




-- WRITE FINAL LEAN CODE BELOW

open Filter
open MeasureTheory
open ProbabilityTheory

noncomputable section



def empiricalCDFIndicator {Ω : Type*} (X : ℕ → Ω → ℝ) (x : ℝ) (k : ℕ) : Ω → ℝ :=
  fun ω => if X k ω ≤ x then 1 else 0



def empiricalCDFAt {Ω : Type*} (X : ℕ → Ω → ℝ) (x : ℝ) (n : ℕ) : Ω → ℝ :=
  thm_11_5_sampleMean (fun k => empiricalCDFIndicator X x k) n



def ex_11_5_1_HasCDF {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, P.real (Y ⁻¹' Set.Iic x) = F x



structure ex_11_5_1_IIDSamplesFromCDF {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (F : ℝ → ℝ) : Prop where
  sampleMeasurable : ∀ k : ℕ, Measurable (X k)
  independent : ProbabilityTheory.iIndepFun X P
  identDistrib : ∀ k : ℕ, IdentDistrib (X k) (X 0) P P
  commonCDF : ex_11_5_1_HasCDF P (X 0) F

 
theorem empiricalCDFIndicator_measurable {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → ℝ} {x : ℝ} {k : ℕ} (hX : Measurable (X k)) :
    Measurable (empiricalCDFIndicator X x k) := by
  unfold empiricalCDFIndicator
  exact Measurable.ite
    (measurableSet_le hX measurable_const) measurable_const measurable_const

 
theorem empiricalCDFIndicator_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {X : ℕ → Ω → ℝ} {x : ℝ} {k : ℕ}
    (hX : Measurable (X k)) :
    Integrable (empiricalCDFIndicator X x k) P := by
  refine Integrable.of_bound
    (empiricalCDFIndicator_measurable hX).aestronglyMeasurable 1 ?_
  filter_upwards with ω
  by_cases hω : X k ω ≤ x <;> simp [empiricalCDFIndicator, hω]



theorem empiricalCDFIndicator_iIndepFun {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℕ → Ω → ℝ} (x : ℝ)
    (hIndep : ProbabilityTheory.iIndepFun X P) :
    ProbabilityTheory.iIndepFun (fun k => empiricalCDFIndicator X x k) P := by
  let phi : ℕ → ℝ → ℝ := fun _ y => if y ≤ x then 1 else 0
  have hphi : ∀ k, Measurable (phi k) := by
    intro k
    dsimp [phi]
    exact Measurable.ite
      (measurableSet_le measurable_id measurable_const) measurable_const measurable_const
  change ProbabilityTheory.iIndepFun
    (fun k ω => if X k ω ≤ x then 1 else 0) P
  simpa [phi, Function.comp_def] using
    hIndep.comp phi hphi

 
theorem empiricalCDFIndicator_identDistrib {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℕ → Ω → ℝ} (x : ℝ)
    (hIdent : ∀ k : ℕ, IdentDistrib (X k) (X 0) P P) (k : ℕ) :
    IdentDistrib
      (empiricalCDFIndicator X x k) (empiricalCDFIndicator X x 0) P P := by
  let phi : ℝ → ℝ := fun y => if y ≤ x then 1 else 0
  have hphi : Measurable phi := by
    dsimp [phi]
    exact Measurable.ite
      (measurableSet_le measurable_id measurable_const) measurable_const measurable_const
  change IdentDistrib
    (fun ω => if X k ω ≤ x then 1 else 0)
    (fun ω => if X 0 ω ≤ x then 1 else 0) P P
  simpa [phi, Function.comp_def] using
    (hIdent k).comp hphi



theorem empiricalCDFIndicator_eq_indicator_preimage {Ω : Type*}
    (X : ℕ → Ω → ℝ) (x : ℝ) (k : ℕ) :
    empiricalCDFIndicator X x k =
      (X k ⁻¹' Set.Iic x).indicator (1 : Ω → ℝ) := by
  funext ω
  by_cases hω : X k ω ≤ x <;> simp [empiricalCDFIndicator, hω]

 
theorem empiricalCDFIndicator_integral_eq_cdf {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {F : ℝ → ℝ}
    (hX : Measurable (X 0)) (hCDF : ex_11_5_1_HasCDF P (X 0) F) (x : ℝ) :
    P[empiricalCDFIndicator X x 0] = F x := by
  have hEvent : MeasurableSet (X 0 ⁻¹' Set.Iic x) := hX measurableSet_Iic
  calc
    P[empiricalCDFIndicator X x 0] = P.real (X 0 ⁻¹' Set.Iic x) := by
      rw [empiricalCDFIndicator_eq_indicator_preimage]
      simpa using
        (MeasureTheory.integral_indicator_one (μ := P) (s := X 0 ⁻¹' Set.Iic x) hEvent)
    _ = F x := hCDF x



theorem ex_11_5_1_indicatorInputs_of_iidSamplesFromCDF
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (F : ℝ → ℝ)
    (hSamples : ex_11_5_1_IIDSamplesFromCDF P X F) (x : ℝ) :
    Integrable (empiricalCDFIndicator X x 0) P ∧
      (Pairwise fun i j =>
        empiricalCDFIndicator X x i ⟂ᵢ[P] empiricalCDFIndicator X x j) ∧
      (∀ i, IdentDistrib
        (empiricalCDFIndicator X x i) (empiricalCDFIndicator X x 0) P P) ∧
      P[empiricalCDFIndicator X x 0] = F x := by
  have hIndependentIndicators :
      ProbabilityTheory.iIndepFun (fun k => empiricalCDFIndicator X x k) P :=
    empiricalCDFIndicator_iIndepFun x hSamples.independent
  exact ⟨
    empiricalCDFIndicator_integrable P (hSamples.sampleMeasurable 0),
    fun i j hij => hIndependentIndicators.indepFun hij,
    fun i => empiricalCDFIndicator_identDistrib x hSamples.identDistrib i,
    empiricalCDFIndicator_integral_eq_cdf P
      (hSamples.sampleMeasurable 0) hSamples.commonCDF x⟩



theorem ex_11_5_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (F : ℝ → ℝ)
    (hSamples : ex_11_5_1_IIDSamplesFromCDF P X F) (x : ℝ) :
    ConvergesAlmostSurely P (fun n => empiricalCDFAt X x n) (fun _ => F x) := by
  rcases ex_11_5_1_indicatorInputs_of_iidSamplesFromCDF P X F hSamples x with
    ⟨hInt, hpairwise, hident, hmean⟩
  simpa [empiricalCDFAt] using
    thm_11_8 P (fun k => empiricalCDFIndicator X x k) (F x)
      hInt hpairwise hident hmean
