import Mathlib
import ToyApollo.Output.def_13_4

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-!
Support lemmas for Problem 13.4.

These lemmas isolate the conditional-expectation interface work used by the
Gaussian regression route. They do not by themselves prove the jointly Gaussian
regression formula.
-/

theorem prob_13_4_indepFun_def_13_4_const {Ω S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (Y : Ω → S)
    (hZmeas : Measurable Z) (hYmeas : Measurable Y)
    (hZint : Integrable Z P) (hInd : IndepFun Z Y P) :
    def_13_4 P Y (def_13_4_sigma_subSigma_of_measurable hYmeas) Z
      (fun _ : Ω => ∫ ω, Z ω ∂P) := by
  unfold def_13_4 def_13_3 ConditionalExpectationSetFormula
  constructor
  · exact hZint
  constructor
  · exact integrable_const _
  constructor
  · unfold GMeasurable def_13_4_sigma
    exact measurable_const
  intro B hB
  have hleZ : def_13_4_sigma Z ≤ _ := def_13_4_sigma_subSigma_of_measurable hZmeas
  have hleY : def_13_4_sigma Y ≤ _ := def_13_4_sigma_subSigma_of_measurable hYmeas
  have hZstrong : StronglyMeasurable[def_13_4_sigma Z] Z := by
    rw [def_13_4_sigma]
    exact (comap_measurable Z).stronglyMeasurable
  have hIndSigma : Indep (def_13_4_sigma Z) (def_13_4_sigma Y) P := by
    simpa [def_13_4_sigma] using (ProbabilityTheory.IndepFun_iff_Indep Z Y P).mp hInd
  have hCE := MeasureTheory.condExp_indep_eq (μ := P)
      (m₁ := def_13_4_sigma Z) (m₂ := def_13_4_sigma Y)
      (m := inferInstance) hleZ hleY hZstrong hIndSigma
  calc
    ∫ ω in B, (fun _ : Ω => ∫ ω, Z ω ∂P) ω ∂P
        = ∫ ω in B, MeasureTheory.condExp (def_13_4_sigma Y) P Z ω ∂P := by
          exact integral_congr_ae (ae_restrict_of_ae hCE.symm)
    _ = ∫ ω in B, Z ω ∂P := by
          exact MeasureTheory.setIntegral_condExp (μ := P)
            (m := def_13_4_sigma Y) (m₀ := inferInstance)
            hleY hZint hB

theorem prob_13_4_centered_indep_add_def_13_4 {Ω S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (R A : Ω → ℝ) (Y : Ω → S)
    (hRmeas : Measurable R) (hYmeas : Measurable Y)
    (hRint : Integrable R P) (hAint : Integrable A P)
    (hAmeas : Measurable[def_13_4_sigma Y] A)
    (hInd : IndepFun R Y P)
    (hMeanR : ∫ ω, R ω ∂P = 0) :
    def_13_4 P Y (def_13_4_sigma_subSigma_of_measurable hYmeas)
      (fun ω => R ω + A ω) A := by
  unfold def_13_4 def_13_3 ConditionalExpectationSetFormula
  constructor
  · exact hRint.add hAint
  constructor
  · exact hAint
  constructor
  · exact hAmeas
  intro B hB
  have hRCE := prob_13_4_indepFun_def_13_4_const P R Y hRmeas hYmeas hRint hInd
  have hReq := hRCE.2.2.2 hB
  have hRzero : ∫ ω in B, R ω ∂P = 0 := by
    rw [← hReq]
    simp [hMeanR]
  have hRintB : Integrable R (P.restrict B) := hRint.mono_measure Measure.restrict_le_self
  have hAintB : Integrable A (P.restrict B) := hAint.mono_measure Measure.restrict_le_self
  have hAdd : (∫ ω in B, R ω + A ω ∂P) =
      (∫ ω in B, R ω ∂P) + ∫ ω in B, A ω ∂P := by
    exact integral_add hRintB hAintB
  calc
    ∫ ω in B, A ω ∂P = 0 + ∫ ω in B, A ω ∂P := by simp
    _ = (∫ ω in B, R ω ∂P) + ∫ ω in B, A ω ∂P := by rw [hRzero]
    _ = ∫ ω in B, R ω + A ω ∂P := by rw [hAdd]

theorem prob_13_4_centered_indep_residual_def_13_4 {Ω S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X R A : Ω → ℝ) (Y : Ω → S)
    (hXint : Integrable X P)
    (hRmeas : Measurable R) (hYmeas : Measurable Y)
    (hRint : Integrable R P) (hAint : Integrable A P)
    (hAmeas : Measurable[def_13_4_sigma Y] A)
    (hInd : IndepFun R Y P)
    (hMeanR : ∫ ω, R ω ∂P = 0)
    (hXeq : ∀ ω, X ω = R ω + A ω) :
    def_13_4 P Y (def_13_4_sigma_subSigma_of_measurable hYmeas) X A := by
  unfold def_13_4 def_13_3 ConditionalExpectationSetFormula
  constructor
  · exact hXint
  constructor
  · exact hAint
  constructor
  · exact hAmeas
  intro B hB
  have hCE :=
    prob_13_4_centered_indep_add_def_13_4 P R A Y hRmeas hYmeas
      hRint hAint hAmeas hInd hMeanR
  have hEq := hCE.2.2.2 hB
  have hBmeas : MeasurableSet B := (def_13_4_sigma_subSigma_of_measurable hYmeas) hB
  have hSetEq : (∫ ω in B, R ω + A ω ∂P) = ∫ ω in B, X ω ∂P := by
    exact setIntegral_congr_fun hBmeas (fun ω _ => (hXeq ω).symm)
  exact hEq.trans hSetEq

theorem prob_13_4_affine_residual_indep_def_13_4 {Ω : Type*}
    [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (a : ℝ)
    (hXmeas : Measurable X) (hYmeas : Measurable Y)
    (hXint : Integrable X P) (hYint : Integrable Y P)
    (hInd : IndepFun
      (fun ω => X ω - ((∫ ω, X ω ∂P) + a * (Y ω - ∫ ω, Y ω ∂P))) Y P) :
    def_13_4 P Y (def_13_4_sigma_subSigma_of_measurable hYmeas) X
      (fun ω => (∫ ω, X ω ∂P) + a * (Y ω - ∫ ω, Y ω ∂P)) := by
  let A : Ω → ℝ := fun ω => (∫ ω, X ω ∂P) + a * (Y ω - ∫ ω, Y ω ∂P)
  let R : Ω → ℝ := fun ω => X ω - A ω
  have hYsigma : Measurable[def_13_4_sigma Y] Y := by
    rw [def_13_4_sigma]
    exact comap_measurable Y
  have hAmeasSigma : Measurable[def_13_4_sigma Y] A := by
    dsimp [A]
    exact measurable_const.add ((hYsigma.sub measurable_const).const_mul a)
  have hAmeas : Measurable A := by
    dsimp [A]
    exact measurable_const.add ((hYmeas.sub measurable_const).const_mul a)
  have hAint : Integrable A P := by
    dsimp [A]
    exact (integrable_const _).add ((hYint.sub (integrable_const _)).const_mul a)
  have hRmeas : Measurable R := by
    dsimp [R]
    exact hXmeas.sub hAmeas
  have hRint : Integrable R P := by
    dsimp [R]
    exact hXint.sub hAint
  have hMeanA : ∫ ω, A ω ∂P = ∫ ω, X ω ∂P := by
    dsimp [A]
    have hYcenterInt : Integrable (fun ω => Y ω - ∫ ω, Y ω ∂P) P :=
      hYint.sub (integrable_const _)
    rw [integral_add (integrable_const _) (hYcenterInt.const_mul a)]
    rw [integral_const_mul]
    have hYcenterZero : ∫ ω, Y ω - ∫ ω, Y ω ∂P ∂P = 0 := by
      rw [integral_sub hYint (integrable_const _)]
      simp [integral_const]
    rw [hYcenterZero]
    simp [integral_const]
  have hMeanR : ∫ ω, R ω ∂P = 0 := by
    dsimp [R]
    rw [integral_sub hXint hAint, hMeanA]
    ring
  have hIndR : IndepFun R Y P := by
    dsimp [R, A]
    exact hInd
  exact prob_13_4_centered_indep_residual_def_13_4 P X R A Y hXint hRmeas
    hYmeas hRint hAint hAmeasSigma hIndR hMeanR
    (by intro ω; dsimp [R, A]; ring)

theorem prob_13_4_linear_residual_pair_gaussian {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Ω → ℝ} (a : ℝ)
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P) :
    HasGaussianLaw (fun ω => (X ω - a * Y ω, Y ω)) P := by
  let L : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ - a • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ))
  have hLin : HasGaussianLaw (fun ω => L (X ω, Y ω)) P := hXY.map_fun L
  refine hLin.congr ?_
  filter_upwards with ω
  rfl

theorem prob_13_4_linear_residual_cov_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X Y : Ω → ℝ}
    (hX2 : MemLp X 2 P) (hY2 : MemLp Y 2 P)
    (hVarY : Var[Y; P] ≠ 0) :
    cov[fun ω => X ω - (cov[X, Y; P] / Var[Y; P]) * Y ω, Y; P] = 0 := by
  change cov[X - (fun ω => (cov[X, Y; P] / Var[Y; P]) * Y ω), Y; P] = 0
  rw [covariance_sub_left hX2 (hY2.const_mul (cov[X, Y; P] / Var[Y; P])) hY2]
  rw [covariance_const_mul_left]
  rw [covariance_self hY2.aemeasurable]
  field_simp [hVarY]
  ring

theorem prob_13_4_residual_indep_of_jointGaussian {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ}
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
    (hVarY : Var[Y; P] ≠ 0) :
    IndepFun
      (fun ω => X ω - ((∫ ω, X ω ∂P) + (cov[X, Y; P] / Var[Y; P]) *
        (Y ω - ∫ ω, Y ω ∂P))) Y P := by
  haveI : IsProbabilityMeasure P := hXY.isProbabilityMeasure
  let a : ℝ := cov[X, Y; P] / Var[Y; P]
  have hX2 : MemLp X 2 P := hXY.fst.memLp_two
  have hY2 : MemLp Y 2 P := hXY.snd.memLp_two
  have hPair : HasGaussianLaw (fun ω => (X ω - a * Y ω, Y ω)) P :=
    prob_13_4_linear_residual_pair_gaussian a hXY
  have hCov : cov[fun ω => X ω - a * Y ω, Y; P] = 0 := by
    dsimp [a]
    exact prob_13_4_linear_residual_cov_zero hX2 hY2 hVarY
  have hLinInd : IndepFun (fun ω => X ω - a * Y ω) Y P :=
    hPair.indepFun_of_covariance_eq_zero hCov
  let c : ℝ := -(∫ ω, X ω ∂P) + a * (∫ ω, Y ω ∂P)
  have hShiftInd :
      IndepFun ((fun z : ℝ => z + c) ∘ (fun ω => X ω - a * Y ω))
        ((fun z : ℝ => z) ∘ Y) P :=
    hLinInd.comp (measurable_id.add_const c) measurable_id
  refine hShiftInd.congr ?_ ?_
  · filter_upwards with ω
    dsimp [a, c, Function.comp]
    ring
  · filter_upwards with ω
    rfl

theorem prob_13_4_jointlyGaussian_affine_condExp_regression {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ}
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
    (hXmeas : Measurable X) (hYmeas : Measurable Y)
    (hVarY : Var[Y; P] ≠ 0) :
    def_13_4 P Y (def_13_4_sigma_subSigma_of_measurable hYmeas) X
      (fun ω => (∫ ω, X ω ∂P) + (cov[X, Y; P] / Var[Y; P]) *
        (Y ω - ∫ ω, Y ω ∂P)) := by
  haveI : IsProbabilityMeasure P := hXY.isProbabilityMeasure
  have hXint : Integrable X P := hXY.fst.integrable
  have hYint : Integrable Y P := hXY.snd.integrable
  have hInd := prob_13_4_residual_indep_of_jointGaussian hXY hVarY
  exact prob_13_4_affine_residual_indep_def_13_4 P X Y (cov[X, Y; P] / Var[Y; P])
    hXmeas hYmeas hXint hYint hInd
