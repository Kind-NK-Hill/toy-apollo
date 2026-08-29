/-
TASK ID: thm_9_3
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter9-characteristic-functions
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_9_3
import ToyApollo.Output.thm_7_7

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory
open Filter
open scoped Topology ComplexConjugate

theorem characteristicFunction_modulus_tendsto_zero
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Tendsto
      (fun h : ℝ =>
        ∫ x : ℝ, ‖Complex.exp (((h * x : ℝ) : ℂ) * Complex.I) - 1‖ ∂μ)
      (nhds 0) (nhds 0) := by
  have hlim :
      ∀ᵐ x ∂μ,
        Tendsto
          (fun h : ℝ =>
            ((‖Complex.exp (((h * x : ℝ) : ℂ) * Complex.I) - 1‖ : ℝ) : ℂ))
          (nhds 0) (nhds 0) := by
    refine ae_of_all μ ?_
    intro x
    have hcont :
        ContinuousAt
          (fun h : ℝ =>
            Complex.exp (((h * x : ℝ) : ℂ) * Complex.I) - 1)
          0 := by
      fun_prop
    have hnorm :
        Tendsto
          (fun h : ℝ =>
            ‖Complex.exp (((h * x : ℝ) : ℂ) * Complex.I) - 1‖)
          (nhds 0) (nhds (0 : ℝ)) := by
      simpa using hcont.norm.tendsto
    simpa using Filter.tendsto_ofReal_iff.mpr hnorm
  have hmeas :
      ∀ h : ℝ,
        AEStronglyMeasurable
          (fun x : ℝ =>
            ((‖Complex.exp (((h * x : ℝ) : ℂ) * Complex.I) - 1‖ : ℝ) : ℂ))
          μ := by
    intro h
    exact (by fun_prop)
  have hbound :
      ∀ h : ℝ,
        ∀ᵐ x ∂μ,
          ‖((‖Complex.exp (((h * x : ℝ) : ℂ) * Complex.I) - 1‖ : ℝ) : ℂ)‖
            ≤ (2 : ℝ) := by
    intro h
    refine ae_of_all μ ?_
    intro x
    calc
      ‖((‖Complex.exp (((h * x : ℝ) : ℂ) * Complex.I) - 1‖ : ℝ) : ℂ)‖
          = ‖Complex.exp (((h * x : ℝ) : ℂ) * Complex.I) - 1‖ := by
            simp [Complex.normSq, abs_of_nonneg (norm_nonneg _)]
      _ ≤ ‖Complex.exp (((h * x : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ :=
            norm_sub_le _ _
      _ = 2 := by
            norm_num [Complex.norm_exp]
  have hdct :=
    (thm_7_7 μ
      (fun h x =>
        ((‖Complex.exp (((h * x : ℝ) : ℂ) * Complex.I) - 1‖ : ℝ) : ℂ))
      (fun _ : ℝ => (0 : ℂ)) (fun _ : ℝ => (2 : ℝ)) 0
      hmeas (integrable_const (2 : ℝ)) hbound hlim).2
  have hreal :
      Tendsto
        (fun h : ℝ =>
          (((∫ x : ℝ,
              ‖Complex.exp (((h * x : ℝ) : ℂ) * Complex.I) - 1‖ ∂μ) : ℝ) : ℂ))
        (nhds 0) (nhds 0) := by
    convert hdct using 1
    · ext h
      exact (integral_ofReal
        (μ := μ)
        (𝕜 := ℂ)
        (f := fun x : ℝ =>
          ‖Complex.exp (((h * x : ℝ) : ℂ) * Complex.I) - 1‖)).symm
    · simp
  exact Filter.tendsto_ofReal_iff.mp hreal

theorem characteristicFunction_dist_le_modulus
    (μ : Measure ℝ) [IsFiniteMeasure μ] (a b : ℝ) :
    dist (charFun μ a) (charFun μ b) ≤
      ∫ x : ℝ,
        ‖Complex.exp ((((a - b) * x : ℝ) : ℂ) * Complex.I) - 1‖ ∂μ := by
  rw [dist_eq_norm]
  rw [charFun_apply_real, charFun_apply_real]
  have hinta :
      Integrable (fun x : ℝ => Complex.exp ((a : ℂ) * (x : ℂ) * Complex.I)) μ := by
    exact (integrable_const (1 : ℂ)).mono (by fun_prop) (by simp [Complex.norm_exp])
  have hintb :
      Integrable (fun x : ℝ => Complex.exp ((b : ℂ) * (x : ℂ) * Complex.I)) μ := by
    exact (integrable_const (1 : ℂ)).mono (by fun_prop) (by simp [Complex.norm_exp])
  rw [← integral_sub hinta hintb]
  calc
    ‖∫ x : ℝ,
        (Complex.exp ((a : ℂ) * (x : ℂ) * Complex.I) -
          Complex.exp ((b : ℂ) * (x : ℂ) * Complex.I)) ∂μ‖
        ≤ ∫ x : ℝ,
          ‖Complex.exp ((a : ℂ) * (x : ℂ) * Complex.I) -
            Complex.exp ((b : ℂ) * (x : ℂ) * Complex.I)‖ ∂μ :=
          norm_integral_le_integral_norm _
    _ = ∫ x : ℝ,
        ‖Complex.exp ((((a - b) * x : ℝ) : ℂ) * Complex.I) - 1‖ ∂μ := by
          congr with x
          have hmul :
              Complex.exp ((a : ℂ) * (x : ℂ) * Complex.I) =
                Complex.exp ((b : ℂ) * (x : ℂ) * Complex.I) *
                  Complex.exp ((((a - b) * x : ℝ) : ℂ) * Complex.I) := by
            rw [← Complex.exp_add]
            congr 1
            norm_num [Complex.ofReal_mul]
            ring
          rw [hmul]
          calc
            ‖Complex.exp ((b : ℂ) * (x : ℂ) * Complex.I) *
                Complex.exp ((((a - b) * x : ℝ) : ℂ) * Complex.I) -
                Complex.exp ((b : ℂ) * (x : ℂ) * Complex.I)‖
                = ‖Complex.exp ((b : ℂ) * (x : ℂ) * Complex.I) *
                    (Complex.exp ((((a - b) * x : ℝ) : ℂ) * Complex.I) - 1)‖ := by
                  ring_nf
            _ = ‖Complex.exp ((((a - b) * x : ℝ) : ℂ) * Complex.I) - 1‖ := by
                  simp [Complex.norm_exp]

theorem characteristicFunction_uniform_continuous
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    UniformContinuous (charFun μ) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  have hmod := characteristicFunction_modulus_tendsto_zero μ
  rw [Metric.tendsto_nhds_nhds] at hmod
  rcases hmod ε hε with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro a b hab
  refine lt_of_le_of_lt (characteristicFunction_dist_le_modulus μ a b) ?_
  have hdist : dist (a - b) 0 < δ := by
    simpa [Real.dist_eq, abs_sub_comm, sub_eq_add_neg, add_comm] using hab
  exact lt_of_le_of_lt (le_abs_self _)
    (by simpa [Real.dist_eq] using hδ (x := a - b) hdist)

structure CharacteristicFunctionBasicProperties (μ : Measure ℝ) : Prop where
  bounded : ∀ t : ℝ, ‖charFun μ t‖ ≤ μ.real Set.univ
  zero : charFun μ 0 = μ.real Set.univ
  conjugate_symmetry : ∀ t : ℝ, charFun μ (-t) = star (charFun μ t)
  continuous : Continuous (charFun μ)
  uniform_continuous : UniformContinuous (charFun μ)

theorem characteristicFunction_law_eq_charFun
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (hX : AEMeasurable X μ) (t : ℝ) :
    characteristicFunction (μ.map X) t = charFun (μ.map X) t := by
  rfl

theorem characteristicFunction_zero_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) :
    characteristicFunction (P.map X) 0 = 1 := by
  letI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX
  simp [characteristicFunction]

theorem characteristicFunction_norm_le_one_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) (t : ℝ) :
    ‖characteristicFunction (P.map X) t‖ ≤ 1 := by
  letI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX
  simpa [characteristicFunction] using norm_charFun_le_one (μ := P.map X) t

theorem characteristicFunction_conjugate_symmetry_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (t : ℝ) :
    characteristicFunction (P.map X) (-t) =
      star (characteristicFunction (P.map X) t) := by
  simpa [characteristicFunction] using charFun_neg (μ := P.map X) t

theorem characteristicFunction_law_basic_properties
    (μ : Measure ℝ) [IsFiniteMeasure μ] [BorelSpace ℝ] :
    CharacteristicFunctionBasicProperties μ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact norm_charFun_le (μ := μ) t
  · simpa using charFun_zero (μ := μ)
  · intro t
    simpa using charFun_neg (μ := μ) t
  · simpa using continuous_charFun (μ := μ)
  · exact characteristicFunction_uniform_continuous μ

theorem characteristicFunction_probability_bounded
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    ‖charFun μ t‖ ≤ 1 :=
  norm_charFun_le_one (μ := μ) t

theorem characteristicFunction_convolution_product
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (t : ℝ) :
    charFun (μ ∗ ν) t = charFun μ t * charFun ν t :=
  charFun_conv (μ := μ) (ν := ν) t

theorem characteristicFunction_indep_add_eq_mul
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X Y : Ω → ℝ}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hXY : X ⟂ᵢ[P] Y) (t : ℝ) :
    characteristicFunction (P.map (fun ω => X ω + Y ω)) t =
      characteristicFunction (P.map X) t *
        characteristicFunction (P.map Y) t := by
  have hcf := hXY.charFun_map_fun_add_eq_mul hX hY
  simpa [characteristicFunction] using congrFun hcf t

structure CharacteristicFunctionRandomVariableProperties
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) : Prop where
  bounded : ∀ t : ℝ, ‖characteristicFunction (P.map X) t‖ ≤ 1
  zero : characteristicFunction (P.map X) 0 = 1
  conjugate_symmetry :
    ∀ t : ℝ, characteristicFunction (P.map X) (-t) =
      star (characteristicFunction (P.map X) t)
  independent_sum :
    ∀ {Y : Ω → ℝ}, AEMeasurable Y P → X ⟂ᵢ[P] Y → ∀ t : ℝ,
      characteristicFunction (P.map (fun ω => X ω + Y ω)) t =
        characteristicFunction (P.map X) t *
          characteristicFunction (P.map Y) t
  uniform_continuous : UniformContinuous (characteristicFunction (P.map X))

theorem characteristicFunction_random_variable_basic_properties
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) :
    CharacteristicFunctionRandomVariableProperties P X := by
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact characteristicFunction_norm_le_one_source hX t
  · exact characteristicFunction_zero_source hX
  · intro t
    exact characteristicFunction_conjugate_symmetry_source t
  · intro Y hY hXY t
    exact characteristicFunction_indep_add_eq_mul hX hY hXY t
  · have huc := characteristicFunction_uniform_continuous (P.map X)
    simpa [characteristicFunction] using huc

theorem thm_9_3_law (μ : Measure ℝ) [IsFiniteMeasure μ] [BorelSpace ℝ] :
    CharacteristicFunctionBasicProperties μ :=
  characteristicFunction_law_basic_properties μ

theorem thm_9_3
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) :
    CharacteristicFunctionRandomVariableProperties P X :=
  characteristicFunction_random_variable_basic_properties hX
