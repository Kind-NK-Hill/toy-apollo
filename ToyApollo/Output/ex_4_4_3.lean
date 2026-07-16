/-
TASK ID: ex_4_4_3
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import Mathlib.Probability.Distributions.Gaussian.Fernique
import ToyApollo.Output.def_4_4_complex_random_variable

open MeasureTheory ProbabilityTheory

noncomputable section

noncomputable def complexGaussianHalfVariance : NNReal :=
  Real.toNNReal (1 / 2 : ℝ)

noncomputable def complexGaussianComponentLaw : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 complexGaussianHalfVariance

noncomputable def standardComplexGaussianPairLaw : Measure (ℝ × ℝ) :=
  complexGaussianComponentLaw.prod complexGaussianComponentLaw

noncomputable def standardComplexGaussianLaw : Measure ℂ :=
  Measure.map Complex.measurableEquivRealProd.symm standardComplexGaussianPairLaw

noncomputable abbrev standardComplexGaussianComponentVariance : NNReal :=
  complexGaussianHalfVariance

noncomputable abbrev standardComplexGaussianRealLaw : Measure ℝ :=
  complexGaussianComponentLaw

theorem complexGaussianHalfVariance_coe :
    (complexGaussianHalfVariance : ℝ) = (1 / 2 : ℝ) := by
  simpa [complexGaussianHalfVariance] using
    (Real.coe_toNNReal (1 / 2 : ℝ) (by norm_num : (0 : ℝ) ≤ 1 / 2))

instance complexGaussianComponentLaw_isProbabilityMeasure :
    IsProbabilityMeasure complexGaussianComponentLaw := by
  dsimp [complexGaussianComponentLaw]
  infer_instance

instance standardComplexGaussianPairLaw_isProbabilityMeasure :
    IsProbabilityMeasure standardComplexGaussianPairLaw := by
  dsimp [standardComplexGaussianPairLaw]
  infer_instance

instance standardComplexGaussianLaw_isProbabilityMeasure :
    IsProbabilityMeasure standardComplexGaussianLaw := by
  dsimp [standardComplexGaussianLaw]
  exact Measure.isProbabilityMeasure_map
    Complex.measurableEquivRealProd.symm.measurable.aemeasurable

def complexGaussianPairRV {Ω : Type*} [MeasurableSpace Ω] (Z : Ω → ℂ) : Ω → ℝ × ℝ :=
  fun ω => (complexRealPartRV Z ω, complexImagPartRV Z ω)

def rotatedComplexGaussianRV {Ω : Type*} [MeasurableSpace Ω]
    (θ : ℝ) (Z : Ω → ℂ) : Ω → ℂ :=
  fun ω => Complex.exp ((θ : ℂ) * Complex.I) * Z ω

theorem rotatedComplexGaussianRV_eq_equiv_rotation
    {Ω : Type*} [MeasurableSpace Ω] (θ : ℝ) (Z : Ω → ℂ) :
    rotatedComplexGaussianRV θ Z =
      fun ω => Complex.measurableEquivRealProd.symm
        ((ContinuousLinearMap.rotation (-θ) : ℝ × ℝ →L[ℝ] ℝ × ℝ)
          (complexGaussianPairRV Z ω)) := by
  funext ω
  apply Complex.ext
  · simp [rotatedComplexGaussianRV, complexGaussianPairRV, complexRealPartRV,
      complexImagPartRV, complexRealPart, complexImagPart,
      ContinuousLinearMap.rotation_apply, Complex.exp_mul_I, Complex.mul_re,
      Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
      Real.cos_neg, Real.sin_neg]
    ring
  · simp [rotatedComplexGaussianRV, complexGaussianPairRV, complexRealPartRV,
      complexImagPartRV, complexRealPart, complexImagPart,
      ContinuousLinearMap.rotation_apply, Complex.exp_mul_I, Complex.mul_re,
      Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
      Real.cos_neg, Real.sin_neg]
    ring

theorem isComplexRandomVariable_rotatedComplexGaussianRV
    {Ω : Type*} [MeasurableSpace Ω] {Z : Ω → ℂ}
    (hZ : IsComplexRandomVariable Z) (θ : ℝ) :
    IsComplexRandomVariable (rotatedComplexGaussianRV θ Z) := by
  rw [rotatedComplexGaussianRV_eq_equiv_rotation]
  have hPair : Measurable (complexGaussianPairRV Z) :=
    Measurable.prodMk (measurable_complexRealPartRV hZ)
      (measurable_complexImagPartRV hZ)
  have hRotation : Measurable
      (fun p : ℝ × ℝ =>
        (ContinuousLinearMap.rotation (-θ) : ℝ × ℝ →L[ℝ] ℝ × ℝ) p) :=
    (ContinuousLinearMap.rotation (-θ) : ℝ × ℝ →L[ℝ] ℝ × ℝ).continuous.measurable
  exact Complex.measurableEquivRealProd.symm.measurable.comp (hRotation.comp hPair)

def complexGaussianRealPartLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℂ) : Prop :=
  HasLaw (complexRealPartRV Z) complexGaussianComponentLaw P

def complexGaussianImagPartLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℂ) : Prop :=
  HasLaw (complexImagPartRV Z) complexGaussianComponentLaw P

def complexGaussianVarianceIntegrand {Ω : Type*} [MeasurableSpace Ω]
    (Z : Ω → ℂ) : Ω → ℝ :=
  fun ω => (complexRealPartRV Z ω) ^ 2 + (complexImagPartRV Z ω) ^ 2

def standardComplexGaussianVarianceFormula {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℂ) : Prop :=
  ∫ ω, complexGaussianVarianceIntegrand Z ω ∂P = 1

def complexGaussianCircularSymmetric {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℂ) : Prop :=
  ∀ θ : ℝ, Measure.map (rotatedComplexGaussianRV θ Z) P = Measure.map Z P

def complexNormalZeroOne {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℂ) : Prop :=
  HasLaw Z standardComplexGaussianLaw P

def StandardComplexGaussianRandomVariable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℂ) : Prop :=
  IsComplexRandomVariable Z ∧ complexNormalZeroOne P Z

theorem standardComplexGaussian_equivRealProdSymm_law :
    HasLaw
      (fun p : ℝ × ℝ => Complex.measurableEquivRealProd.symm p)
      standardComplexGaussianLaw standardComplexGaussianPairLaw := by
  refine ⟨Complex.measurableEquivRealProd.symm.measurable.aemeasurable, ?_⟩
  rfl

theorem standardComplexGaussian_equivRealProd_law :
    HasLaw
      (fun z : ℂ => Complex.measurableEquivRealProd z)
      standardComplexGaussianPairLaw standardComplexGaussianLaw := by
  refine ⟨Complex.measurableEquivRealProd.measurable.aemeasurable, ?_⟩
  change Measure.map Complex.measurableEquivRealProd
      (Measure.map Complex.measurableEquivRealProd.symm standardComplexGaussianPairLaw) =
    standardComplexGaussianPairLaw
  exact MeasurableEquiv.map_map_symm (ν := standardComplexGaussianPairLaw)
    Complex.measurableEquivRealProd

theorem standardComplexGaussian_pair_law_of_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℂ}
    (hZlaw : HasLaw Z standardComplexGaussianLaw P) :
    HasLaw (complexGaussianPairRV Z) standardComplexGaussianPairLaw P := by
  have hRaw := standardComplexGaussian_equivRealProd_law.comp hZlaw
  refine hRaw.congr (Filter.Eventually.of_forall ?_)
  intro ω
  simp [Function.comp_def, complexGaussianPairRV, complexRealPartRV,
    complexImagPartRV, complexRealPart, complexImagPart]

theorem standardComplexGaussian_realPart_normal
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℂ}
    (hZlaw : HasLaw Z standardComplexGaussianLaw P) :
    complexGaussianRealPartLaw P Z := by
  have hPair := standardComplexGaussian_pair_law_of_law hZlaw
  have hFst :
      HasLaw (Prod.fst : ℝ × ℝ → ℝ)
        complexGaussianComponentLaw standardComplexGaussianPairLaw :=
    MeasureTheory.measurePreserving_fst.hasLaw
  simpa [complexGaussianRealPartLaw, complexGaussianPairRV, Function.comp_def] using
    hFst.comp hPair

theorem standardComplexGaussian_imagPart_normal
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℂ}
    (hZlaw : HasLaw Z standardComplexGaussianLaw P) :
    complexGaussianImagPartLaw P Z := by
  have hPair := standardComplexGaussian_pair_law_of_law hZlaw
  have hSnd :
      HasLaw (Prod.snd : ℝ × ℝ → ℝ)
        complexGaussianComponentLaw standardComplexGaussianPairLaw :=
    MeasureTheory.measurePreserving_snd.hasLaw
  simpa [complexGaussianImagPartLaw, complexGaussianPairRV, Function.comp_def] using
    hSnd.comp hPair

theorem standardComplexGaussian_independent_parts
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℂ}
    (hZlaw : HasLaw Z standardComplexGaussianLaw P) :
    ProbabilityTheory.IndepFun
      (complexRealPartRV Z) (complexImagPartRV Z) P := by
  letI : IsProbabilityMeasure P := hZlaw.isProbabilityMeasure
  have hRe := standardComplexGaussian_realPart_normal hZlaw
  have hIm := standardComplexGaussian_imagPart_normal hZlaw
  have hPair := standardComplexGaussian_pair_law_of_law hZlaw
  apply (indepFun_iff_hasLaw_prodMk_prod hRe hIm).2
  exact hPair.congr (Filter.Eventually.of_forall (fun ω => by rfl))

theorem complexGaussianComponentLaw_second_moment :
    ∫ x : ℝ, x ^ 2 ∂complexGaussianComponentLaw = (1 / 2 : ℝ) := by
  have hmem : MemLp (id : ℝ → ℝ) 2 complexGaussianComponentLaw := by
    simpa [complexGaussianComponentLaw] using
      (memLp_id_gaussianReal (μ := (0 : ℝ))
        (v := complexGaussianHalfVariance) 2)
  have hvar := variance_eq_sub (μ := complexGaussianComponentLaw)
    (X := (id : ℝ → ℝ)) hmem
  have hGaussianVariance :
      Var[id; complexGaussianComponentLaw] = (complexGaussianHalfVariance : ℝ) := by
    simpa only [complexGaussianComponentLaw] using
      (ProbabilityTheory.variance_id_gaussianReal
        (μ := (0 : ℝ)) (v := complexGaussianHalfVariance))
  have hmean : ∫ x : ℝ, x ∂complexGaussianComponentLaw = 0 := by
    simpa only [complexGaussianComponentLaw] using
      (ProbabilityTheory.integral_id_gaussianReal
        (μ := (0 : ℝ)) (v := complexGaussianHalfVariance))
  rw [hGaussianVariance] at hvar
  simp [hmean] at hvar
  rw [complexGaussianHalfVariance_coe] at hvar
  norm_num at hvar ⊢
  exact hvar.symm

private theorem complexGaussian_component_memLp_of_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X complexGaussianComponentLaw P) :
    MemLp X 2 P := by
  have hbase : MemLp (id : ℝ → ℝ) 2 complexGaussianComponentLaw := by
    simpa [complexGaussianComponentLaw] using
      (memLp_id_gaussianReal (μ := (0 : ℝ))
        (v := complexGaussianHalfVariance) 2)
  have hmap : MemLp (id : ℝ → ℝ) 2 (Measure.map X P) := by
    rw [hX.map_eq]
    exact hbase
  simpa [Function.comp_def] using
    (memLp_map_measure_iff aestronglyMeasurable_id hX.aemeasurable).1 hmap

private theorem complexGaussian_component_square_integrable_of_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X complexGaussianComponentLaw P) :
    Integrable (fun ω => X ω ^ 2) P :=
  (complexGaussian_component_memLp_of_law hX).integrable_sq

private theorem complexGaussian_component_second_moment_of_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X complexGaussianComponentLaw P) :
    ∫ ω, X ω ^ 2 ∂P = (1 / 2 : ℝ) := by
  have hIntegral :=
    hX.integral_comp (E := ℝ) (f := fun x : ℝ => x ^ 2) (by fun_prop)
  simp only [Function.comp_apply] at hIntegral
  rw [hIntegral, complexGaussianComponentLaw_second_moment]

theorem standardComplexGaussian_real_square_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℂ}
    (hZlaw : HasLaw Z standardComplexGaussianLaw P) :
    Integrable (fun ω => (complexRealPartRV Z ω) ^ 2) P :=
  complexGaussian_component_square_integrable_of_law
    (standardComplexGaussian_realPart_normal hZlaw)

theorem standardComplexGaussian_imag_square_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℂ}
    (hZlaw : HasLaw Z standardComplexGaussianLaw P) :
    Integrable (fun ω => (complexImagPartRV Z ω) ^ 2) P :=
  complexGaussian_component_square_integrable_of_law
    (standardComplexGaussian_imagPart_normal hZlaw)

theorem standardComplexGaussian_variance_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℂ}
    (hZlaw : HasLaw Z standardComplexGaussianLaw P) :
    Integrable (complexGaussianVarianceIntegrand Z) P := by
  unfold complexGaussianVarianceIntegrand
  exact (standardComplexGaussian_real_square_integrable hZlaw).add
    (standardComplexGaussian_imag_square_integrable hZlaw)

theorem standardComplexGaussian_variance_eq_one
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℂ}
    (hZlaw : HasLaw Z standardComplexGaussianLaw P) :
    standardComplexGaussianVarianceFormula P Z := by
  have hReInt := standardComplexGaussian_real_square_integrable hZlaw
  have hImInt := standardComplexGaussian_imag_square_integrable hZlaw
  unfold standardComplexGaussianVarianceFormula complexGaussianVarianceIntegrand
  rw [integral_add hReInt hImInt]
  rw [complexGaussian_component_second_moment_of_law
    (standardComplexGaussian_realPart_normal hZlaw)]
  rw [complexGaussian_component_second_moment_of_law
    (standardComplexGaussian_imagPart_normal hZlaw)]
  norm_num

theorem standardComplexGaussianPairLaw_rotation_invariant (θ : ℝ) :
    Measure.map
      (ContinuousLinearMap.rotation θ : ℝ × ℝ →L[ℝ] ℝ × ℝ)
      standardComplexGaussianPairLaw =
      standardComplexGaussianPairLaw := by
  have hmean : complexGaussianComponentLaw[id] = 0 := by
    simp [complexGaussianComponentLaw]
  haveI : ProbabilityTheory.IsGaussian complexGaussianComponentLaw := by
    dsimp [complexGaussianComponentLaw]
    infer_instance
  simpa [standardComplexGaussianPairLaw] using
    (ProbabilityTheory.IsGaussian.map_rotation_eq_self
      (μ := complexGaussianComponentLaw) hmean θ)

theorem standardComplexGaussian_rotation_complex_law (θ : ℝ) :
    HasLaw
      (fun p : ℝ × ℝ =>
        Complex.measurableEquivRealProd.symm
          ((ContinuousLinearMap.rotation (-θ) : ℝ × ℝ →L[ℝ] ℝ × ℝ) p))
      standardComplexGaussianLaw standardComplexGaussianPairLaw := by
  have hRotation :
      HasLaw
        (fun p : ℝ × ℝ =>
          (ContinuousLinearMap.rotation (-θ) : ℝ × ℝ →L[ℝ] ℝ × ℝ) p)
        standardComplexGaussianPairLaw standardComplexGaussianPairLaw := by
    refine ⟨(ContinuousLinearMap.rotation (-θ) :
      ℝ × ℝ →L[ℝ] ℝ × ℝ).continuous.measurable.aemeasurable, ?_⟩
    exact standardComplexGaussianPairLaw_rotation_invariant (-θ)
  simpa [Function.comp_def] using
    standardComplexGaussian_equivRealProdSymm_law.comp hRotation

theorem standardComplexGaussian_rotated_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℂ}
    (hZlaw : HasLaw Z standardComplexGaussianLaw P) (θ : ℝ) :
    HasLaw (rotatedComplexGaussianRV θ Z) standardComplexGaussianLaw P := by
  have hPair := standardComplexGaussian_pair_law_of_law hZlaw
  have hRaw := (standardComplexGaussian_rotation_complex_law θ).comp hPair
  have hPairRotated :
      HasLaw
        (fun ω =>
          Complex.measurableEquivRealProd.symm
            ((ContinuousLinearMap.rotation (-θ) : ℝ × ℝ →L[ℝ] ℝ × ℝ)
              (complexGaussianPairRV Z ω)))
        standardComplexGaussianLaw P := by
    simpa [Function.comp_def] using hRaw
  refine hPairRotated.congr (Filter.Eventually.of_forall ?_)
  intro ω
  exact congrFun (rotatedComplexGaussianRV_eq_equiv_rotation θ Z) ω

theorem standardComplexGaussianLaw_rotation_invariant (θ : ℝ) :
    Measure.map (fun z : ℂ => Complex.exp ((θ : ℂ) * Complex.I) * z)
      standardComplexGaussianLaw =
      standardComplexGaussianLaw := by
  have hId :
      HasLaw (id : ℂ → ℂ) standardComplexGaussianLaw standardComplexGaussianLaw :=
    HasLaw.id
  have hRotated := standardComplexGaussian_rotated_law hId θ
  have hFunction :
      rotatedComplexGaussianRV θ (id : ℂ → ℂ) =
        fun z : ℂ => Complex.exp ((θ : ℂ) * Complex.I) * z := by
    funext z
    rfl
  rw [← hFunction]
  exact hRotated.map_eq

theorem standardComplexGaussian_circular_symmetric
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℂ}
    (hZlaw : HasLaw Z standardComplexGaussianLaw P) :
    complexGaussianCircularSymmetric P Z := by
  intro θ
  exact (standardComplexGaussian_rotated_law hZlaw θ).map_eq.trans hZlaw.map_eq.symm

theorem standardComplexGaussian_rotated_identDistrib
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℂ}
    (hZlaw : HasLaw Z standardComplexGaussianLaw P) (θ : ℝ) :
    Measure.map (rotatedComplexGaussianRV θ Z) P = Measure.map Z P :=
  standardComplexGaussian_circular_symmetric hZlaw θ

structure StandardComplexGaussianResult
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : Ω → ℂ) : Prop where
  is_complex_random_variable : IsComplexRandomVariable Z
  real_part_normal : complexGaussianRealPartLaw P Z
  imag_part_normal : complexGaussianImagPartLaw P Z
  independent_parts :
    ProbabilityTheory.IndepFun (complexRealPartRV Z) (complexImagPartRV Z) P
  real_square_integrable :
    Integrable (fun ω => (complexRealPartRV Z ω) ^ 2) P
  imag_square_integrable :
    Integrable (fun ω => (complexImagPartRV Z ω) ^ 2) P
  variance_integrable : Integrable (complexGaussianVarianceIntegrand Z) P
  variance_eq_one : standardComplexGaussianVarianceFormula P Z
  rotated_law :
    ∀ θ : ℝ,
      HasLaw (rotatedComplexGaussianRV θ Z) standardComplexGaussianLaw P
  circular_symmetric : complexGaussianCircularSymmetric P Z

theorem exercise_4_4_3
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℂ)
    (hZmeas : Measurable Z)
    (hZlaw : HasLaw Z standardComplexGaussianLaw P) :
    StandardComplexGaussianResult P Z := by
  exact
    { is_complex_random_variable := hZmeas
      real_part_normal := standardComplexGaussian_realPart_normal hZlaw
      imag_part_normal := standardComplexGaussian_imagPart_normal hZlaw
      independent_parts := standardComplexGaussian_independent_parts hZlaw
      real_square_integrable := standardComplexGaussian_real_square_integrable hZlaw
      imag_square_integrable := standardComplexGaussian_imag_square_integrable hZlaw
      variance_integrable := standardComplexGaussian_variance_integrable hZlaw
      variance_eq_one := standardComplexGaussian_variance_eq_one hZlaw
      rotated_law := standardComplexGaussian_rotated_law hZlaw
      circular_symmetric := standardComplexGaussian_circular_symmetric hZlaw }

theorem ex_4_4_3
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℂ)
    (hZmeas : Measurable Z)
    (hZlaw : HasLaw Z standardComplexGaussianLaw P) :
    StandardComplexGaussianResult P Z :=
  exercise_4_4_3 P Z hZmeas hZlaw
