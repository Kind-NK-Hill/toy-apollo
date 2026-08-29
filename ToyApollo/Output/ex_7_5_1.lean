/-
TASK ID: ex_7_5_1
TYPE: Example_Proof
SOURCE PLAN: 29_chap7_product_expectation
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW
open MeasureTheory ProbabilityTheory

def Ex751Uncorrelated {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  ∫ ω, X ω * Y ω ∂μ = (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ

def Ex751Independent {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  ProbabilityTheory.IndepFun X Y μ

abbrev Ex751Ω := Fin 4 × Bool

instance : MeasurableSpace Ex751Ω := ⊤

noncomputable def ex751Measure : Measure Ex751Ω :=
  (PMF.uniformOfFintype Ex751Ω).toMeasure

def ex751ZVal (i : Fin 4) : ℝ :=
  if i = 0 then -1 else if i = 3 then 1 else 0

def ex751Z (ω : Ex751Ω) : ℝ :=
  ex751ZVal ω.1

def ex751U (ω : Ex751Ω) : Bool :=
  ω.2

def ex751USign (ω : Ex751Ω) : ℝ :=
  if ex751U ω then -1 else 1

def ex751X (ω : Ex751Ω) : ℝ :=
  ex751Z ω

def ex751Y (ω : Ex751Ω) : ℝ :=
  if ex751U ω then -ex751Z ω else ex751Z ω

theorem ex751USign_mem (ω : Ex751Ω) :
    ex751USign ω = -1 ∨ ex751USign ω = 1 := by
  rcases ω with ⟨i, u⟩
  cases u <;> simp [ex751USign, ex751U]

theorem ex751Y_eq_USign_mul_Z :
    ex751Y = fun ω => ex751USign ω * ex751Z ω := by
  funext ω
  rcases ω with ⟨i, u⟩
  cases u <;> simp [ex751Y, ex751USign, ex751U]

def ex751AbsEvent : Set Ex751Ω :=
  {ω | ω.1 = 0 ∨ ω.1 = 3}

def ex751AbsEventFinset : Finset Ex751Ω :=
  {(0, false), (0, true), (3, false), (3, true)}

theorem ex751X_eq_Z : ex751X = ex751Z := rfl

theorem ex751_mean_zero_Z :
    ∫ ω, ex751Z ω ∂ex751Measure = 0 := by
  rw [ex751Measure]
  erw [MeasureTheory.integral_fintype]
  · simp [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four,
      ex751Z, ex751ZVal, PMF.uniformOfFintype_apply, MeasureTheory.measureReal_def]
    ring_nf
  · exact Integrable.of_finite

theorem ex751_mean_zero_X :
    ∫ ω, ex751X ω ∂ex751Measure = 0 := by
  simpa [ex751X_eq_Z] using ex751_mean_zero_Z

theorem ex751_mean_zero_Y :
    ∫ ω, ex751Y ω ∂ex751Measure = 0 := by
  rw [ex751Measure]
  erw [MeasureTheory.integral_fintype]
  · simp [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four,
      ex751Y, ex751U, ex751Z, ex751ZVal, PMF.uniformOfFintype_apply, MeasureTheory.measureReal_def]
  · exact Integrable.of_finite

theorem ex751_product_mean_zero :
    ∫ ω, ex751X ω * ex751Y ω ∂ex751Measure = 0 := by
  rw [ex751Measure]
  erw [MeasureTheory.integral_fintype]
  · simp [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four,
      ex751X, ex751Y, ex751U, ex751Z, ex751ZVal, PMF.uniformOfFintype_apply,
      MeasureTheory.measureReal_def]
  · exact Integrable.of_finite

theorem ex751_uncorrelated :
    Ex751Uncorrelated ex751Measure ex751X ex751Y := by
  rw [Ex751Uncorrelated, ex751_product_mean_zero, ex751_mean_zero_X, ex751_mean_zero_Y]
  ring

theorem ex751_preimage_abs_one_X :
    ex751X ⁻¹' {x : ℝ | |x| = 1} = ex751AbsEvent := by
  ext ω
  rcases ω with ⟨i, u⟩
  fin_cases i <;> cases u <;>
    simp [ex751X, ex751Z, ex751ZVal, ex751AbsEvent]

theorem ex751_preimage_abs_one_Y :
    ex751Y ⁻¹' {x : ℝ | |x| = 1} = ex751AbsEvent := by
  ext ω
  rcases ω with ⟨i, u⟩
  fin_cases i <;> cases u <;>
    simp [ex751Y, ex751U, ex751Z, ex751ZVal, ex751AbsEvent]

theorem mem_ex751AbsEventFinset_iff (ω : Ex751Ω) :
    ω ∈ ex751AbsEventFinset ↔ ω ∈ ex751AbsEvent := by
  rcases ω with ⟨i, u⟩
  fin_cases i <;> cases u <;>
    simp [ex751AbsEventFinset, ex751AbsEvent]

theorem ex751_measure_absEvent :
    ex751Measure ex751AbsEvent = (1 / 2 : ENNReal) := by
  have hset : ex751AbsEvent = (ex751AbsEventFinset : Set Ex751Ω) := by
    ext ω
    exact (mem_ex751AbsEventFinset_iff ω).symm
  rw [hset, ex751Measure, PMF.toMeasure_apply_finset]
  simp [ex751AbsEventFinset, PMF.uniformOfFintype_apply]
  calc
    (4 : ENNReal) * 8⁻¹ = (4 / 8 : ENNReal) := by rw [div_eq_mul_inv]
    _ = (1 / 2 : ENNReal) := by
      have hdiv_ne_top : (4 / 8 : ENNReal) ≠ ⊤ :=
        ENNReal.div_ne_top (by simp) (by norm_num)
      have hhalf_ne_top : (1 / 2 : ENNReal) ≠ ⊤ :=
        ENNReal.div_ne_top (by simp) (by norm_num)
      apply (ENNReal.toReal_eq_toReal_iff' hdiv_ne_top hhalf_ne_top).1
      norm_num
    _ = (2 : ENNReal)⁻¹ := by
      have hhalf_ne_top : (1 / 2 : ENNReal) ≠ ⊤ :=
        ENNReal.div_ne_top (by simp) (by norm_num)
      have hinv_ne_top : (2 : ENNReal)⁻¹ ≠ ⊤ :=
        (ENNReal.inv_ne_top).2 (by norm_num)
      apply (ENNReal.toReal_eq_toReal_iff' hhalf_ne_top hinv_ne_top).1
      norm_num

private theorem ex751_four_mul_eight_inv :
    (4 : ENNReal) * 8⁻¹ = (2 : ENNReal)⁻¹ := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).1
  norm_num [ENNReal.toReal_add]

theorem ex751_measure_USign_eq_neg_one :
    ex751Measure (ex751USign ⁻¹' ({-1} : Set ℝ)) = (1 / 2 : ENNReal) := by
  have hOneNeNegOne : (1 : ℝ) ≠ -1 := by norm_num
  rw [ex751Measure, PMF.toMeasure_apply_fintype]
  simp [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four,
    Set.indicator, ex751USign, ex751U, PMF.uniformOfFintype_apply, hOneNeNegOne]
  exact ex751_four_mul_eight_inv

theorem ex751_measure_USign_eq_one :
    ex751Measure (ex751USign ⁻¹' ({1} : Set ℝ)) = (1 / 2 : ENNReal) := by
  have hNegOneNeOne : (-1 : ℝ) ≠ 1 := by norm_num
  rw [ex751Measure, PMF.toMeasure_apply_fintype]
  simp [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four,
    Set.indicator, ex751USign, ex751U, PMF.uniformOfFintype_apply, hNegOneNeOne]
  exact ex751_four_mul_eight_inv

theorem ex751_USign_independent_Z :
    ProbabilityTheory.IndepFun ex751USign ex751Z ex751Measure := by
  rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  rw [ex751Measure, PMF.toMeasure_apply_fintype, PMF.toMeasure_apply_fintype,
    PMF.toMeasure_apply_fintype]
  by_cases hUn : (-1 : ℝ) ∈ s
  all_goals by_cases hUp : (1 : ℝ) ∈ s
  all_goals by_cases hZn : (-1 : ℝ) ∈ t
  all_goals by_cases hZ0 : (0 : ℝ) ∈ t
  all_goals by_cases hZp : (1 : ℝ) ∈ t
  all_goals simp [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four,
    Set.indicator, ex751USign, ex751U, ex751Z, ex751ZVal,
    PMF.uniformOfFintype_apply, hUn, hUp, hZn, hZ0, hZp]
  all_goals rw [ex751_four_mul_eight_inv]
  all_goals apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).1
  all_goals norm_num [ENNReal.toReal_add]

theorem ex751_measure_abs_one_Z :
    ex751Measure (ex751Z ⁻¹' {z : ℝ | |z| = 1}) = (1 / 2 : ENNReal) := by
  rw [← ex751X_eq_Z, ex751_preimage_abs_one_X]
  exact ex751_measure_absEvent

theorem ex751_not_independent :
    ¬ Ex751Independent ex751Measure ex751X ex751Y := by
  intro hXY
  let s : Set ℝ := {x | |x| = 1}
  have hs : MeasurableSet s := measurableSet_eq_fun measurable_abs measurable_const
  have hmul :=
    (show ex751X ⟂ᵢ[ex751Measure] ex751Y by
      simpa [Ex751Independent] using hXY).measure_inter_preimage_eq_mul s s hs hs
  rw [ex751_preimage_abs_one_X, ex751_preimage_abs_one_Y, Set.inter_self] at hmul
  have hhalf : (1 / 2 : ENNReal) = (1 / 2 : ENNReal) * (1 / 2 : ENNReal) := by
    simpa [ex751_measure_absEvent] using hmul
  have hfalse : False := by
    have hreal : (1 / 2 : ℝ) = (1 / 2 : ℝ) * (1 / 2 : ℝ) := by
      simpa using congrArg ENNReal.toReal hhalf
    nlinarith
  exact hfalse.elim

theorem ex_7_5_1 :
    (∀ ω, ex751USign ω = -1 ∨ ex751USign ω = 1) ∧
      ex751Measure (ex751USign ⁻¹' ({-1} : Set ℝ)) = (1 / 2 : ENNReal) ∧
      ex751Measure (ex751USign ⁻¹' ({1} : Set ℝ)) = (1 / 2 : ENNReal) ∧
      ProbabilityTheory.IndepFun ex751USign ex751Z ex751Measure ∧
      ex751Measure (ex751Z ⁻¹' {z : ℝ | |z| = 1}) = (1 / 2 : ENNReal) ∧
      ∫ ω, ex751Z ω ∂ex751Measure = 0 ∧
      ex751X = ex751Z ∧
      ex751Y = (fun ω => ex751USign ω * ex751Z ω) ∧
      Ex751Uncorrelated ex751Measure ex751X ex751Y ∧
      ¬ Ex751Independent ex751Measure ex751X ex751Y := by
  refine ⟨ex751USign_mem, ex751_measure_USign_eq_neg_one, ex751_measure_USign_eq_one,
    ex751_USign_independent_Z, ex751_measure_abs_one_Z, ex751_mean_zero_Z, ex751X_eq_Z,
    ex751Y_eq_USign_mul_Z, ex751_uncorrelated, ex751_not_independent⟩
