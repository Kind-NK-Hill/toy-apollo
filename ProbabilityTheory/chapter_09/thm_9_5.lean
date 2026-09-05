/-
TASK ID: thm_9_5
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter9-characteristic-functions
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_07.thm_7_7
import ProbabilityTheory.chapter_09.thm_9_5_kernel




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set
open scoped Topology Interval

noncomputable section

 
def characteristicInversionLimitAssembly
    (μ : Measure ℝ) (a b : ℝ) : Prop :=
  Tendsto
    (fun T : ℝ => characteristicInversionTruncation μ a b T)
    atTop
    (nhds ((2 * Real.pi : ℂ) * characteristicInversionMass μ a b))

 
def characteristicInversionDCTInnerLimit
    (μ : Measure ℝ) (a b : ℝ) : Prop :=
  Tendsto
    (fun T : ℝ => ∫ x, characteristicInversionInnerKernel a b x T ∂μ)
    atTop
    (nhds ((2 * Real.pi : ℂ) * characteristicInversionMass μ a b))



def characteristicInversionDCTAtTopHypotheses
    (μ : Measure ℝ) (a b : ℝ) : Prop :=
  ∃ Y : ℝ → ℝ,
    (∀ T : ℝ,
      AEStronglyMeasurable
        (fun x : ℝ => characteristicInversionInnerKernel a b x T) μ) ∧
    Integrable Y μ ∧
    (∀ T : ℝ, ∀ᵐ x ∂μ,
      ‖characteristicInversionInnerKernel a b x T‖ ≤ Y x) ∧
    (∀ᵐ x ∂μ,
      Tendsto
        (fun T : ℝ => characteristicInversionInnerKernel a b x T)
        atTop
        (nhds (characteristicInversionKernelLimitValue a b x)))



theorem characteristicInversionDCTAtTopHypotheses_of_pointwise_dominated
    (μ : Measure ℝ) [IsFiniteMeasure μ] (a b : ℝ)
    (hmeas :
      ∀ T : ℝ,
        AEStronglyMeasurable
          (fun x : ℝ => characteristicInversionInnerKernel a b x T) μ)
    (hdom : characteristicInversionKernelDominated a b)
    (hpoint :
      ∀ x : ℝ, characteristicInversionKernelPointwiseLimit a b x) :
    characteristicInversionDCTAtTopHypotheses μ a b := by
  rcases hdom with ⟨C, hC_nonneg, hbound⟩
  refine ⟨fun _ : ℝ => C, hmeas, integrable_const C, ?_, ?_⟩
  · intro T
    exact ae_of_all μ fun x => hbound x T
  · exact ae_of_all μ hpoint



theorem characteristicInversionDCTAtTopHypotheses_of_dirichlet
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a b : ℝ} (hab : a < b)
    (hlim : characteristicInversionDirichletIntegralLimit)
    (hchange : ∀ x : ℝ, characteristicInversionKernelChangeOfVariables a b x)
    (hmeas :
      ∀ T : ℝ,
        AEStronglyMeasurable
          (fun x : ℝ => characteristicInversionInnerKernel a b x T) μ) :
    characteristicInversionDCTAtTopHypotheses μ a b := by
  have hdom : characteristicInversionKernelDominated a b :=
    characteristicInversionKernelDominated_of_dirichlet hlim hchange
  have hpoint :
      ∀ x : ℝ, characteristicInversionKernelPointwiseLimit a b x := by
    intro x
    exact characteristicInversionKernelFromSine_of_change a b x
      (hchange x)
      (characteristicInversionSineKernelLimit_of_dirichlet hlim hab)
  exact characteristicInversionDCTAtTopHypotheses_of_pointwise_dominated
    μ a b hmeas hdom hpoint



theorem characteristicInversionDCTAtTopHypotheses_of_dirichlet_change
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a b : ℝ} (hab : a < b)
    (hlim : characteristicInversionDirichletIntegralLimit)
    (hchange : ∀ x : ℝ, characteristicInversionKernelChangeOfVariables a b x) :
    characteristicInversionDCTAtTopHypotheses μ a b := by
  exact characteristicInversionDCTAtTopHypotheses_of_dirichlet μ hab hlim hchange
    (characteristicInversionInnerKernel_aestronglyMeasurable_of_change
      μ a b hchange)



theorem characteristicInversionDCTInnerLimit_of_atTop
    (μ : Measure ℝ) (a b : ℝ)
    (hhyp : characteristicInversionDCTAtTopHypotheses μ a b)
    (hid :
      ∫ x, characteristicInversionKernelLimitValue a b x ∂μ =
        (2 * Real.pi : ℂ) * characteristicInversionMass μ a b) :
    characteristicInversionDCTInnerLimit μ a b := by
  rcases hhyp with ⟨Y, hXm, hYint, hbound, hlim⟩
  have hdct :
      Tendsto
        (fun T : ℝ => ∫ x,
          characteristicInversionInnerKernel a b x T ∂μ)
        atTop
        (nhds (∫ x,
          characteristicInversionKernelLimitValue a b x ∂μ)) :=
    thm_7_DCT_filter μ
      (fun T x => characteristicInversionInnerKernel a b x T)
      (fun x => characteristicInversionKernelLimitValue a b x)
      Y atTop
      (Eventually.of_forall hXm) hYint
      (Eventually.of_forall hbound) hlim
  simpa [characteristicInversionDCTInnerLimit, hid] using hdct



def characteristicInversionDCTLimitVersion
    (μ : Measure ℝ) (a b : ℝ) : Prop :=
  characteristicInversionDCTInnerLimit μ a b

 
def CharacteristicInversionFormula (μ : Measure ℝ) : Prop :=
  ∀ ⦃a b : ℝ⦄, a < b →
    Tendsto
      (fun T : ℝ =>
        ((2 * Real.pi : ℂ)⁻¹) *
          characteristicInversionTruncation μ a b T)
      atTop
      (nhds (characteristicInversionMass μ a b))



theorem characteristicInversionKernelLimitValue_integral
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a b : ℝ} (hab : a < b) :
    (∫ x, characteristicInversionKernelLimitValue a b x ∂μ) =
      (2 * Real.pi : ℂ) * characteristicInversionMass μ a b := by
  let f : ℝ → ℂ := (Ioo a b).indicator (fun _ : ℝ => (2 * Real.pi : ℂ))
  let g : ℝ → ℂ := ({a} : Set ℝ).indicator (fun _ : ℝ => (Real.pi : ℂ))
  let h : ℝ → ℂ := ({b} : Set ℝ).indicator (fun _ : ℝ => (Real.pi : ℂ))
  have hpoint : (fun x => characteristicInversionKernelLimitValue a b x) =
      (fun x => f x + g x + h x) := by
    funext x
    by_cases hinside : a < x ∧ x < b
    · have hxa : x ≠ a := ne_of_gt hinside.1
      have hxb : x ≠ b := ne_of_lt hinside.2
      simp [f, g, h, characteristicInversionKernelLimitValue, hinside, hxa, hxb]
    · by_cases hxa : x = a
      · have hxnotinside : x ∉ Ioo a b := by simp [hxa]
        simp [f, g, h, characteristicInversionKernelLimitValue,
          hxa, hab.ne]
      · by_cases hxb : x = b
        · have hxnotinside : x ∉ Ioo a b := by simp [hxb]
          simp [f, g, h, characteristicInversionKernelLimitValue,
            hxb, hab.ne']
        · have hxnotinside : x ∉ Ioo a b := by simpa using hinside
          simp [f, g, h, characteristicInversionKernelLimitValue,
            hinside, hxnotinside, hxa, hxb]
  rw [hpoint]
  have hf : Integrable f μ := by
    dsimp [f]
    exact (MeasureTheory.integrable_const (2 * Real.pi : ℂ)).indicator
      measurableSet_Ioo
  have hg : Integrable g μ := by
    dsimp [g]
    exact (MeasureTheory.integrable_const (Real.pi : ℂ)).indicator
      (MeasurableSet.singleton a)
  have hh : Integrable h μ := by
    dsimp [h]
    exact (MeasureTheory.integrable_const (Real.pi : ℂ)).indicator
      (MeasurableSet.singleton b)
  rw [MeasureTheory.integral_add (f := fun x => f x + g x) (g := h)
    (hf.add hg) hh]
  rw [MeasureTheory.integral_add (f := f) (g := g) hf hg]
  dsimp [f, g, h]
  rw [MeasureTheory.integral_indicator_const (μ := μ)
    (e := (2 * Real.pi : ℂ)) measurableSet_Ioo]
  rw [MeasureTheory.integral_indicator_const (μ := μ)
    (e := (Real.pi : ℂ)) (MeasurableSet.singleton a)]
  rw [MeasureTheory.integral_indicator_const (μ := μ)
    (e := (Real.pi : ℂ)) (MeasurableSet.singleton b)]
  have halg :
      μ.real (Ioo a b) • ((2 * Real.pi) : ℂ) +
          μ.real ({a} : Set ℝ) • (Real.pi : ℂ) +
        μ.real ({b} : Set ℝ) • (Real.pi : ℂ) =
          (2 * Real.pi : ℂ) * characteristicInversionMass μ a b := by
    simp [characteristicInversionMass]
    ring_nf
  simpa using halg



structure CharacteristicInversionSourceSpine (μ : Measure ℝ) : Prop where
  dirichlet_limit :
    characteristicInversionDirichletIntegralLimit

 
theorem characteristicInversionLimitAssembly_of_sourceSpine
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h_spine : CharacteristicInversionSourceSpine μ)
    ⦃a b : ℝ⦄ (hab : a < b) :
    characteristicInversionLimitAssembly μ a b := by
  have hswap :
      (fun T : ℝ => characteristicInversionTruncation μ a b T) =ᶠ[atTop]
      (fun T : ℝ => ∫ x, characteristicInversionInnerKernel a b x T ∂μ) :=
    (eventually_ge_atTop (0 : ℝ)).mono fun T hT =>
      characteristicInversionFubiniSwap_of_integrable_nonneg μ a b T hT
        (characteristicInversionFubiniIntegrable_of_finite μ a b T hab.le)
  have hchange :
      ∀ x : ℝ, characteristicInversionKernelChangeOfVariables a b x := by
    intro x
    exact characteristicInversionKernelChangeOfVariables_of_translated a b x
  have hdct_hyp : characteristicInversionDCTAtTopHypotheses μ a b :=
    characteristicInversionDCTAtTopHypotheses_of_dirichlet_change μ hab
      h_spine.dirichlet_limit hchange
  have hinner : characteristicInversionDCTInnerLimit μ a b :=
    characteristicInversionDCTInnerLimit_of_atTop μ a b
      hdct_hyp
      (characteristicInversionKernelLimitValue_integral μ hab)
  exact hinner.congr' hswap.symm

 
theorem characteristicInversionFormula_of_sourceSpine
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h_spine : CharacteristicInversionSourceSpine μ) :
    CharacteristicInversionFormula μ := by
  intro a b hab
  have hlim :=
    (characteristicInversionLimitAssembly_of_sourceSpine μ h_spine hab).const_mul
      ((2 * Real.pi : ℂ)⁻¹)
  have hnonzero : (2 * Real.pi : ℂ) ≠ 0 := by
    norm_num [Real.pi_ne_zero]
  have hscale :
      ((2 * Real.pi : ℂ)⁻¹) *
          ((2 * Real.pi : ℂ) * characteristicInversionMass μ a b) =
        characteristicInversionMass μ a b := by
    calc
      ((2 * Real.pi : ℂ)⁻¹) *
          ((2 * Real.pi : ℂ) * characteristicInversionMass μ a b)
          = (((2 * Real.pi : ℂ)⁻¹) * (2 * Real.pi : ℂ)) *
              characteristicInversionMass μ a b := by
            ring
      _ = 1 * characteristicInversionMass μ a b := by
            rw [inv_mul_cancel₀ hnonzero]
      _ = characteristicInversionMass μ a b := by
            rw [one_mul]
  rw [hscale] at hlim
  simpa [CharacteristicInversionFormula, characteristicInversionLimitAssembly]
    using hlim



theorem thm_9_5 (μ : Measure ℝ) [IsFiniteMeasure μ] :
    CharacteristicInversionFormula μ :=
  characteristicInversionFormula_of_sourceSpine μ
    ⟨characteristicInversionDirichletIntegralLimit_proof⟩
