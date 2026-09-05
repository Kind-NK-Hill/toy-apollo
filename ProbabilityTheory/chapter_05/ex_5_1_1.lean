/-
TASK ID: ex_5_1_1
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_05.def_5_2

open Set
open MeasureTheory
open scoped ENNReal

 
noncomputable def ex_5_1_1_U (x : ℝ) : ℤ := Int.floor (10 * x)

 
noncomputable def ex_5_1_1_V (y : ℝ) : ℝ := (0 : ℝ) - Real.log y

theorem measurable_ex_5_1_1_U : Measurable ex_5_1_1_U := by
  change Measurable (fun x : ℝ => Int.floor (10 * x))
  exact (measurable_const.mul measurable_id).floor

theorem measurable_ex_5_1_1_V : Measurable ex_5_1_1_V := by
  change Measurable (fun y : ℝ => (0 : ℝ) - Real.log y)
  exact measurable_const.sub Real.measurable_log

 
noncomputable def ex_5_1_1_uniform : Measure ℝ :=
  volume.restrict (Icc 0 1)

 
noncomputable def ex_5_1_1_pair {Ω : Type*} (X Y : Ω → ℝ) (ω : Ω) : ℝ × ℝ :=
  ((ex_5_1_1_U (X ω) : ℝ), ex_5_1_1_V (Y ω))

theorem measurable_ex_5_1_1_pair {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) :
    Measurable (ex_5_1_1_pair X Y) := by
  have hcast : Measurable (fun z : ℤ => (z : ℝ)) := Measurable.of_discrete
  exact (hcast.comp (measurable_ex_5_1_1_U.comp hX)).prodMk
    (measurable_ex_5_1_1_V.comp hY)



theorem ex_5_1_1_U_finiteSupport_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : Measurable X)
    (hXlaw : Measure.map X μ = ex_5_1_1_uniform) :
    ∀ᵐ z ∂Measure.map (ex_5_1_1_U ∘ X) μ, z ∈ Finset.Icc (0 : ℤ) 9 := by
  rw [← Measure.map_map measurable_ex_5_1_1_U hX, hXlaw, ex_5_1_1_uniform,
    ← restrict_Ico_eq_restrict_Icc]
  rw [ae_map_iff measurable_ex_5_1_1_U.aemeasurable (by measurability)]
  filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
  simp only [Finset.mem_Icc]
  constructor
  · exact Int.floor_nonneg.mpr (mul_nonneg (by norm_num) hx.1)
  · change Int.floor (10 * x) ≤ 9
    have hten : 10 * x < (10 : ℝ) := by nlinarith [hx.2]
    have hfloor : Int.floor (10 * x) < (10 : ℤ) := Int.floor_lt.mpr hten
    omega

 
theorem ex_5_1_1_V_noAtoms {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (hY : Measurable Y)
    (hYlaw : Measure.map Y μ = ex_5_1_1_uniform) :
    NoAtoms (Measure.map (ex_5_1_1_V ∘ Y) μ) := by
  constructor
  intro v
  rw [← Measure.map_map measurable_ex_5_1_1_V hY, hYlaw, ex_5_1_1_uniform,
    ← restrict_Ioo_eq_restrict_Icc]
  rw [Measure.map_apply measurable_ex_5_1_1_V (measurableSet_singleton v)]
  rw [Measure.restrict_apply
    ((measurableSet_singleton v).preimage measurable_ex_5_1_1_V)]
  apply measure_mono_null _ (measure_singleton (Real.exp (-v)))
  rintro y ⟨hyv, hyIoo⟩
  simp only [mem_preimage, mem_singleton_iff] at hyv ⊢
  have hlog : Real.log y = -v := by
    simp only [ex_5_1_1_V] at hyv
    linarith
  calc
    y = Real.exp (Real.log y) := (Real.exp_log hyIoo.1).symm
    _ = Real.exp (-v) := by rw [hlog]

 
theorem ex_5_1_1_transformed_indep {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) (hXY : ProbabilityTheory.IndepFun X Y μ) :
    ProbabilityTheory.IndepFun (ex_5_1_1_U ∘ X) (ex_5_1_1_V ∘ Y) μ := by
  exact hXY.comp measurable_ex_5_1_1_U measurable_ex_5_1_1_V

 
noncomputable def ex_5_1_1_jointCDF {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) (a b : ℝ) : ℝ≥0∞ :=
  μ {ω | (ex_5_1_1_U (X ω) : ℝ) ≤ a ∧ ex_5_1_1_V (Y ω) ≤ b}

theorem ex_5_1_1_jointCDF_spec {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) (a b : ℝ) :
    ex_5_1_1_jointCDF μ X Y a b =
      μ {ω | (ex_5_1_1_U (X ω) : ℝ) ≤ a ∧ ex_5_1_1_V (Y ω) ≤ b} := rfl

 
theorem ex_5_1_1_jointCDF_exists {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) :
    ∃ F : ℝ → ℝ → ℝ≥0∞, ∀ a b,
      F a b = μ {ω | (ex_5_1_1_U (X ω) : ℝ) ≤ a ∧ ex_5_1_1_V (Y ω) ≤ b} := by
  exact ⟨ex_5_1_1_jointCDF μ X Y, fun _ _ => rfl⟩



theorem ex_5_1_1_no_jointDensity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) :
    ¬ ∃ f : (ℝ × ℝ) → ℝ≥0∞,
      Measure.map (ex_5_1_1_pair X Y) μ =
        ((volume : Measure ℝ).prod volume).withDensity f := by
  let A : Set ℝ := range (fun z : ℤ => (z : ℝ))
  let S : Set (ℝ × ℝ) := A ×ˢ univ
  have hAcount : A.Countable := Set.countable_range _
  have hAmeas : MeasurableSet A := hAcount.measurableSet
  have hSmeas : MeasurableSet S := hAmeas.prod MeasurableSet.univ
  have hAzero : (volume : Measure ℝ) A = 0 := hAcount.measure_zero volume
  have hSzero : ((volume : Measure ℝ).prod volume) S = 0 := by
    rw [show S = A ×ˢ univ from rfl, Measure.prod_prod, hAzero]
    simp
  have hpair : Measurable (ex_5_1_1_pair X Y) := measurable_ex_5_1_1_pair hX hY
  have hpre : ex_5_1_1_pair X Y ⁻¹' S = (univ : Set Ω) := by
    ext ω
    simp [S, A, ex_5_1_1_pair]
  have hjoint : Measure.map (ex_5_1_1_pair X Y) μ S = 1 := by
    rw [Measure.map_apply hpair hSmeas, hpre, measure_univ]
  rintro ⟨f, hf⟩
  have hdensezero : ((volume : Measure ℝ).prod volume).withDensity f S = 0 :=
    withDensity_absolutelyContinuous _ _ hSzero
  have hcontr : Measure.map (ex_5_1_1_pair X Y) μ S = 0 := by
    rw [hf]
    exact hdensezero
  rw [hjoint] at hcontr
  exact one_ne_zero hcontr

 
theorem ex_5_1_1 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (hXlaw : Measure.map X μ = ex_5_1_1_uniform)
    (hYlaw : Measure.map Y μ = ex_5_1_1_uniform)
    (hXY : ProbabilityTheory.IndepFun X Y μ) :
    (∀ᵐ z ∂Measure.map (ex_5_1_1_U ∘ X) μ, z ∈ Finset.Icc (0 : ℤ) 9) ∧
      NoAtoms (Measure.map (ex_5_1_1_V ∘ Y) μ) ∧
      ProbabilityTheory.IndepFun (ex_5_1_1_U ∘ X) (ex_5_1_1_V ∘ Y) μ ∧
      (∃ F : ℝ → ℝ → ℝ≥0∞, ∀ a b,
        F a b = μ {ω | (ex_5_1_1_U (X ω) : ℝ) ≤ a ∧ ex_5_1_1_V (Y ω) ≤ b}) ∧
      (¬ ∃ f : (ℝ × ℝ) → ℝ≥0∞,
        Measure.map (ex_5_1_1_pair X Y) μ =
          ((volume : Measure ℝ).prod volume).withDensity f) := by
  exact ⟨ex_5_1_1_U_finiteSupport_ae μ X hX hXlaw,
    ex_5_1_1_V_noAtoms μ Y hY hYlaw,
    ex_5_1_1_transformed_indep μ X Y hXY,
    ex_5_1_1_jointCDF_exists μ X Y,
    ex_5_1_1_no_jointDensity μ X Y hX hY⟩
