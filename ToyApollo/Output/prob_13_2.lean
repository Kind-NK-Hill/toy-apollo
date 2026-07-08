/-
TASK ID: prob_13_2
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.prob_13_2_support

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

theorem scratch_thresholdY_measurable (sigma : ℝ) :
    Measurable (fun x : ℝ => prob_13_2_thresholdY sigma x) := by
  unfold prob_13_2_thresholdY
  exact measurable_const.ite (measurableSet_lt measurable_id measurable_const)
    (measurable_const.ite (measurableSet_le measurable_id measurable_const)
      measurable_const)

theorem scratch_thresholdY_range {sigma x : ℝ} :
    prob_13_2_thresholdY sigma x = -1 ∨
      prob_13_2_thresholdY sigma x = 0 ∨
      prob_13_2_thresholdY sigma x = 1 := by
  unfold prob_13_2_thresholdY
  by_cases hleft : x < -sigma
  · simp [hleft]
  · by_cases hmid : x <= sigma
    · simp [hleft, hmid]
    · simp [hleft, hmid]

theorem scratch_answer_measurable (sigma : ℝ) :
    Measurable (fun y : ℝ => prob_13_2_E_X_given_Y_value sigma y) := by
  unfold prob_13_2_E_X_given_Y_value
  exact measurable_const.ite (measurableSet_singleton (-1 : ℝ))
    (measurable_const.ite (measurableSet_singleton (0 : ℝ))
      (measurable_const.ite (measurableSet_singleton (1 : ℝ))
        measurable_const))

theorem scratch_atom_left {Ω : Type*} (X : Ω → ℝ) {sigma : ℝ} :
    prob_13_2_observationAtom (fun ω => prob_13_2_thresholdY sigma (X ω)) 0 =
      {ω | X ω < -sigma} := by
  ext ω
  unfold prob_13_2_observationAtom prob_13_2_threeLabel prob_13_2_thresholdY
  by_cases hleft : X ω < -sigma
  · simp [hleft]
  · by_cases hmid : X ω <= sigma
    · simp [hleft, hmid]
    · have hge : -sigma <= X ω := le_of_not_gt hleft
      simp [hleft, hmid, hge] <;> norm_num

theorem scratch_atom_mid {Ω : Type*} (X : Ω → ℝ) {sigma : ℝ} :
    prob_13_2_observationAtom (fun ω => prob_13_2_thresholdY sigma (X ω)) 1 =
      {ω | -sigma <= X ω ∧ X ω <= sigma} := by
  ext ω
  unfold prob_13_2_observationAtom prob_13_2_threeLabel prob_13_2_thresholdY
  by_cases hleft : X ω < -sigma
  · have hnot : ¬ (-sigma <= X ω ∧ X ω <= sigma) := by
      intro h
      exact not_lt_of_ge h.1 hleft
    simp [hleft, hnot]
  · by_cases hmid : X ω <= sigma
    · have hge : -sigma <= X ω := le_of_not_gt hleft
      simp [hleft, hmid, hge] <;> norm_num
    · have hnot : ¬ (-sigma <= X ω ∧ X ω <= sigma) := by
        intro h
        exact hmid h.2
      simp [hleft, hmid, hnot]

theorem scratch_atom_right {Ω : Type*} (X : Ω → ℝ) {sigma : ℝ}
    (hsigma : 0 < sigma) :
    prob_13_2_observationAtom (fun ω => prob_13_2_thresholdY sigma (X ω)) 2 =
      {ω | sigma < X ω} := by
  ext ω
  unfold prob_13_2_observationAtom prob_13_2_threeLabel prob_13_2_thresholdY
  by_cases hleft : X ω < -sigma
  · have hnot : ¬ sigma < X ω := by
      intro h
      linarith
    simp [hleft, hnot] <;> norm_num
  · by_cases hmid : X ω <= sigma
    · have hnot : ¬ sigma < X ω := not_lt_of_ge hmid
      simp [hleft, hmid, hnot]
    · have hgt : sigma < X ω := lt_of_not_ge hmid
      simp [hleft, hmid, hgt] <;> norm_num

theorem scratch_standard_setIntegral_Ioi :
    (∫ z in Set.Ioi (1 : ℝ), z
        ∂ProbabilityTheory.gaussianReal 0 (1 : NNReal)) =
      prob_13_2_standardNormalPdfAtOne := by
  rw [← integral_indicator measurableSet_Ioi]
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul
    (μ := 0) (v := (1 : NNReal)) (hv := by norm_num)
    (f := Set.indicator (Set.Ioi (1 : ℝ)) (fun z : ℝ => z))]
  rw [show
      (fun z : ℝ =>
        ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z •
          Set.indicator (Set.Ioi (1 : ℝ)) (fun z : ℝ => z) z) =
        Set.indicator (Set.Ioi (1 : ℝ))
          (fun z : ℝ =>
            ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z • z) by
    funext z
    by_cases hz : z ∈ Set.Ioi (1 : ℝ) <;> simp [Set.indicator, hz]]
  rw [integral_indicator measurableSet_Ioi]
  calc
    (∫ z in Set.Ioi (1 : ℝ),
        ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z • z) =
        ∫ z in Set.Ioi (1 : ℝ),
          z * ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z := by
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro z _hz
      simp [smul_eq_mul, mul_comm]
    _ = prob_13_2_standardNormalPdfAtOne := by
      simpa [prob_13_2_standardNormalPdfAtOne] using
        prob_13_2_standardNormal_right_tail_numerator

theorem scratch_standard_setIntegral_Iio :
    (∫ z in Set.Iio (-(1 : ℝ)), z
        ∂ProbabilityTheory.gaussianReal 0 (1 : NNReal)) =
      -prob_13_2_standardNormalPdfAtOne := by
  rw [← integral_indicator measurableSet_Iio]
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul
    (μ := 0) (v := (1 : NNReal)) (hv := by norm_num)
    (f := Set.indicator (Set.Iio (-(1 : ℝ))) (fun z : ℝ => z))]
  rw [show
      (fun z : ℝ =>
        ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z •
          Set.indicator (Set.Iio (-(1 : ℝ))) (fun z : ℝ => z) z) =
        Set.indicator (Set.Iio (-(1 : ℝ)))
          (fun z : ℝ =>
            ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z • z) by
    funext z
    by_cases hz : z ∈ Set.Iio (-(1 : ℝ)) <;> simp [Set.indicator, hz]]
  rw [integral_indicator measurableSet_Iio]
  calc
    (∫ z in Set.Iio (-(1 : ℝ)),
        ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z • z) =
        ∫ z in Set.Iio (-(1 : ℝ)),
          z * ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z := by
      refine setIntegral_congr_fun measurableSet_Iio ?_
      intro z _hz
      simp [smul_eq_mul, mul_comm]
    _ = -prob_13_2_standardNormalPdfAtOne := by
      simpa [prob_13_2_standardNormalPdfAtOne] using
        prob_13_2_standardNormal_left_tail_numerator

theorem scratch_standard_setIntegral_Icc :
    (∫ z in Set.Icc (-(1 : ℝ)) (1 : ℝ), z
        ∂ProbabilityTheory.gaussianReal 0 (1 : NNReal)) = 0 := by
  rw [← integral_indicator measurableSet_Icc]
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul
    (μ := 0) (v := (1 : NNReal)) (hv := by norm_num)
    (f := Set.indicator (Set.Icc (-(1 : ℝ)) (1 : ℝ)) (fun z : ℝ => z))]
  rw [show
      (fun z : ℝ =>
        ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z •
          Set.indicator (Set.Icc (-(1 : ℝ)) (1 : ℝ)) (fun z : ℝ => z) z) =
        Set.indicator (Set.Icc (-(1 : ℝ)) (1 : ℝ))
          (fun z : ℝ =>
            ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z • z) by
    funext z
    by_cases hz : z ∈ Set.Icc (-(1 : ℝ)) (1 : ℝ) <;> simp [Set.indicator, hz]]
  rw [integral_indicator measurableSet_Icc]
  have hIcc :
      (∫ z in Set.Icc (-(1 : ℝ)) (1 : ℝ),
        ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z • z) =
        ∫ z in Set.Icc (-(1 : ℝ)) (1 : ℝ),
          z * ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) z := by
    refine setIntegral_congr_fun measurableSet_Icc ?_
    intro z _hz
    simp [smul_eq_mul, mul_comm]
  rw [hIcc]
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by norm_num : (-(1 : ℝ)) ≤ 1)]
  exact prob_13_2_central_atom_odd_integral_zero

theorem scratch_hasLaw_setIntegral_preimage {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : Ω → ℝ}
    (hZmeas : Measurable Z)
    (hZlaw : HasLaw Z (ProbabilityTheory.gaussianReal 0 (1 : NNReal)) P)
    {s : Set ℝ} (hs : MeasurableSet s) :
    (∫ ω in {ω | Z ω ∈ s}, Z ω ∂P) =
      ∫ z in s, z ∂ProbabilityTheory.gaussianReal 0 (1 : NNReal) := by
  have hmap := MeasureTheory.setIntegral_map (μ := P) (g := Z)
    (f := fun z : ℝ => z) (s := s) hs aestronglyMeasurable_id
    hZmeas.aemeasurable
  simpa [hZlaw.map_eq] using hmap.symm

theorem scratch_hasLaw_measure_preimage {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : Ω → ℝ}
    (hZmeas : Measurable Z)
    (hZlaw : HasLaw Z (ProbabilityTheory.gaussianReal 0 (1 : NNReal)) P)
    {s : Set ℝ} (hs : MeasurableSet s) :
    P {ω | Z ω ∈ s} =
      ProbabilityTheory.gaussianReal 0 (1 : NNReal) s := by
  have hmap := Measure.map_apply (μ := P) hZmeas hs
  rw [hZlaw.map_eq] at hmap
  simpa using hmap.symm

theorem scratch_scaled_setIntegral_Ioi {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : Ω → ℝ} {sigma : ℝ}
    (hZmeas : Measurable Z)
    (hZlaw : HasLaw Z (ProbabilityTheory.gaussianReal 0 (1 : NNReal)) P) :
    (∫ ω in {ω | Z ω ∈ Set.Ioi (1 : ℝ)}, sigma * Z ω ∂P) =
      sigma * prob_13_2_standardNormalPdfAtOne := by
  rw [show (fun ω : Ω => sigma * Z ω) = fun ω : Ω => sigma • Z ω by
    funext ω
    simp [smul_eq_mul]]
  rw [integral_smul]
  rw [scratch_hasLaw_setIntegral_preimage hZmeas hZlaw measurableSet_Ioi]
  rw [scratch_standard_setIntegral_Ioi]
  simp [smul_eq_mul]

theorem scratch_scaled_setIntegral_Iio {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : Ω → ℝ} {sigma : ℝ}
    (hZmeas : Measurable Z)
    (hZlaw : HasLaw Z (ProbabilityTheory.gaussianReal 0 (1 : NNReal)) P) :
    (∫ ω in {ω | Z ω ∈ Set.Iio (-(1 : ℝ))}, sigma * Z ω ∂P) =
      -sigma * prob_13_2_standardNormalPdfAtOne := by
  rw [show (fun ω : Ω => sigma * Z ω) = fun ω : Ω => sigma • Z ω by
    funext ω
    simp [smul_eq_mul]]
  rw [integral_smul]
  rw [scratch_hasLaw_setIntegral_preimage hZmeas hZlaw measurableSet_Iio]
  rw [scratch_standard_setIntegral_Iio]
  simp [smul_eq_mul]

theorem scratch_scaled_setIntegral_Icc {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : Ω → ℝ} {sigma : ℝ}
    (hZmeas : Measurable Z)
    (hZlaw : HasLaw Z (ProbabilityTheory.gaussianReal 0 (1 : NNReal)) P) :
    (∫ ω in {ω | Z ω ∈ Set.Icc (-(1 : ℝ)) (1 : ℝ)}, sigma * Z ω ∂P) = 0 := by
  rw [show (fun ω : Ω => sigma * Z ω) = fun ω : Ω => sigma • Z ω by
    funext ω
    simp [smul_eq_mul]]
  rw [integral_smul]
  rw [scratch_hasLaw_setIntegral_preimage hZmeas hZlaw measurableSet_Icc]
  rw [scratch_standard_setIntegral_Icc]
  simp

theorem scratch_measureReal_preimage_Ioi {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : Ω → ℝ}
    (hZmeas : Measurable Z)
    (hZlaw : HasLaw Z (ProbabilityTheory.gaussianReal 0 (1 : NNReal)) P) :
    P.real {ω | Z ω ∈ Set.Ioi (1 : ℝ)} =
      prob_13_2_standardNormalUpperTailMass := by
  rw [Measure.real_def]
  rw [scratch_hasLaw_measure_preimage hZmeas hZlaw measurableSet_Ioi]
  rfl

theorem scratch_measureReal_preimage_Iio {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : Ω → ℝ}
    (hZmeas : Measurable Z)
    (hZlaw : HasLaw Z (ProbabilityTheory.gaussianReal 0 (1 : NNReal)) P) :
    P.real {ω | Z ω ∈ Set.Iio (-(1 : ℝ))} =
      prob_13_2_standardNormalUpperTailMass := by
  rw [Measure.real_def]
  rw [scratch_hasLaw_measure_preimage hZmeas hZlaw measurableSet_Iio]
  rw [prob_13_2_standardNormal_left_tail_mass_eq_right_tail_mass]
  rfl

theorem scratch_X_left_atom_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {sigma : ℝ}
    (hsigma : 0 < sigma) (hXmeas : Measurable X)
    (hXlaw : HasLaw X
      (ProbabilityTheory.gaussianReal 0 (⟨sigma ^ 2, sq_nonneg sigma⟩ : NNReal)) P) :
    (∫ ω in prob_13_2_observationAtom
        (fun ω => prob_13_2_thresholdY sigma (X ω)) 0, X ω ∂P) =
      -sigma * prob_13_2_standardNormalPdfAtOne := by
  let Z : Ω → ℝ := fun ω => X ω / sigma
  have hZmeas : Measurable Z := hXmeas.div_const sigma
  have hZlaw : HasLaw Z (ProbabilityTheory.gaussianReal 0 (1 : NNReal)) P :=
    prob_13_2_gaussian_scale_to_standard hsigma hXlaw
  rw [scratch_atom_left X]
  rw [← prob_13_2_standard_threshold_left_event (X := X) (sigma := sigma) hsigma]
  have hset : MeasurableSet {ω : Ω | Z ω ∈ Set.Iio (-(1 : ℝ))} :=
    measurableSet_Iio.preimage hZmeas
  have hpoint : ∀ ω, X ω = sigma * Z ω := by
    intro ω
    dsimp [Z]
    field_simp [hsigma.ne']
  calc
    (∫ ω in {ω : Ω | X ω / sigma < -1}, X ω ∂P) =
        ∫ ω in {ω : Ω | Z ω ∈ Set.Iio (-(1 : ℝ))}, sigma * Z ω ∂P := by
      refine setIntegral_congr_fun hset ?_
      intro ω _hω
      exact hpoint ω
    _ = -sigma * prob_13_2_standardNormalPdfAtOne :=
      scratch_scaled_setIntegral_Iio hZmeas hZlaw

theorem scratch_X_right_atom_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {sigma : ℝ}
    (hsigma : 0 < sigma) (hXmeas : Measurable X)
    (hXlaw : HasLaw X
      (ProbabilityTheory.gaussianReal 0 (⟨sigma ^ 2, sq_nonneg sigma⟩ : NNReal)) P) :
    (∫ ω in prob_13_2_observationAtom
        (fun ω => prob_13_2_thresholdY sigma (X ω)) 2, X ω ∂P) =
      sigma * prob_13_2_standardNormalPdfAtOne := by
  let Z : Ω → ℝ := fun ω => X ω / sigma
  have hZmeas : Measurable Z := hXmeas.div_const sigma
  have hZlaw : HasLaw Z (ProbabilityTheory.gaussianReal 0 (1 : NNReal)) P :=
    prob_13_2_gaussian_scale_to_standard hsigma hXlaw
  rw [scratch_atom_right X hsigma]
  rw [← prob_13_2_standard_threshold_right_event (X := X) (sigma := sigma) hsigma]
  have hset : MeasurableSet {ω : Ω | Z ω ∈ Set.Ioi (1 : ℝ)} :=
    measurableSet_Ioi.preimage hZmeas
  have hpoint : ∀ ω, X ω = sigma * Z ω := by
    intro ω
    dsimp [Z]
    field_simp [hsigma.ne']
  calc
    (∫ ω in {ω : Ω | 1 < X ω / sigma}, X ω ∂P) =
        ∫ ω in {ω : Ω | Z ω ∈ Set.Ioi (1 : ℝ)}, sigma * Z ω ∂P := by
      refine setIntegral_congr_fun hset ?_
      intro ω _hω
      exact hpoint ω
    _ = sigma * prob_13_2_standardNormalPdfAtOne :=
      scratch_scaled_setIntegral_Ioi hZmeas hZlaw

theorem scratch_X_mid_atom_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {sigma : ℝ}
    (hsigma : 0 < sigma) (hXmeas : Measurable X)
    (hXlaw : HasLaw X
      (ProbabilityTheory.gaussianReal 0 (⟨sigma ^ 2, sq_nonneg sigma⟩ : NNReal)) P) :
    (∫ ω in prob_13_2_observationAtom
        (fun ω => prob_13_2_thresholdY sigma (X ω)) 1, X ω ∂P) = 0 := by
  let Z : Ω → ℝ := fun ω => X ω / sigma
  have hZmeas : Measurable Z := hXmeas.div_const sigma
  have hZlaw : HasLaw Z (ProbabilityTheory.gaussianReal 0 (1 : NNReal)) P :=
    prob_13_2_gaussian_scale_to_standard hsigma hXlaw
  rw [scratch_atom_mid X]
  rw [← prob_13_2_standard_threshold_central_event (X := X) (sigma := sigma) hsigma]
  have hset : MeasurableSet {ω : Ω | Z ω ∈ Set.Icc (-(1 : ℝ)) (1 : ℝ)} :=
    measurableSet_Icc.preimage hZmeas
  have hpoint : ∀ ω, X ω = sigma * Z ω := by
    intro ω
    dsimp [Z]
    field_simp [hsigma.ne']
  calc
    (∫ ω in {ω : Ω | -1 ≤ X ω / sigma ∧ X ω / sigma ≤ 1}, X ω ∂P) =
        ∫ ω in {ω : Ω | Z ω ∈ Set.Icc (-(1 : ℝ)) (1 : ℝ)}, sigma * Z ω ∂P := by
      refine setIntegral_congr_fun hset ?_
      intro ω _hω
      exact hpoint ω
    _ = 0 := scratch_scaled_setIntegral_Icc hZmeas hZlaw

theorem scratch_CEY_left_atom_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {sigma : ℝ}
    (hsigma : 0 < sigma) (hXmeas : Measurable X)
    (hXlaw : HasLaw X
      (ProbabilityTheory.gaussianReal 0 (⟨sigma ^ 2, sq_nonneg sigma⟩ : NNReal)) P) :
    (∫ ω in prob_13_2_observationAtom
        (fun ω => prob_13_2_thresholdY sigma (X ω)) 0,
        prob_13_2_E_X_given_Y_value sigma
          (prob_13_2_thresholdY sigma (X ω)) ∂P) =
      -sigma * prob_13_2_standardNormalPdfAtOne := by
  let Y : Ω → ℝ := fun ω => prob_13_2_thresholdY sigma (X ω)
  let Z : Ω → ℝ := fun ω => X ω / sigma
  have hZmeas : Measurable Z := hXmeas.div_const sigma
  have hZlaw : HasLaw Z (ProbabilityTheory.gaussianReal 0 (1 : NNReal)) P :=
    prob_13_2_gaussian_scale_to_standard hsigma hXlaw
  have hAtom : prob_13_2_observationAtom Y 0 = {ω | X ω < -sigma} := by
    exact scratch_atom_left X
  have hStd : {ω : Ω | X ω < -sigma} = {ω | Z ω ∈ Set.Iio (-(1 : ℝ))} := by
    rw [← prob_13_2_standard_threshold_left_event (X := X) (sigma := sigma) hsigma]
    rfl
  have hset : MeasurableSet {ω : Ω | X ω < -sigma} := by
    rw [hStd]
    exact measurableSet_Iio.preimage hZmeas
  rw [hAtom]
  calc
    (∫ ω in {ω : Ω | X ω < -sigma},
        prob_13_2_E_X_given_Y_value sigma (Y ω) ∂P) =
        ∫ _ω in {ω : Ω | X ω < -sigma},
          (-prob_13_2_positiveTailMean sigma) ∂P := by
      refine setIntegral_congr_fun hset ?_
      intro ω hω
      have hxlt : X ω < -sigma := hω
      have hYω : Y ω = -1 := by
        simp [Y, prob_13_2_thresholdY, hxlt]
      simp [prob_13_2_E_X_given_Y_value, hYω]
    _ = P.real {ω : Ω | X ω < -sigma} *
          (-prob_13_2_positiveTailMean sigma) := by
      rw [setIntegral_const]
      simp [smul_eq_mul]
    _ = prob_13_2_standardNormalUpperTailMass *
          (-prob_13_2_positiveTailMean sigma) := by
      have hm := scratch_measureReal_preimage_Iio hZmeas hZlaw
      rw [hStd]
      rw [hm]
    _ = -sigma * prob_13_2_standardNormalPdfAtOne := by
      have hmass : prob_13_2_standardNormalUpperTailMass ≠ 0 :=
        prob_13_2_standardNormal_right_tail_mass_toReal_ne_zero
      unfold prob_13_2_positiveTailMean
      field_simp [hmass]

theorem scratch_CEY_right_atom_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {sigma : ℝ}
    (hsigma : 0 < sigma) (hXmeas : Measurable X)
    (hXlaw : HasLaw X
      (ProbabilityTheory.gaussianReal 0 (⟨sigma ^ 2, sq_nonneg sigma⟩ : NNReal)) P) :
    (∫ ω in prob_13_2_observationAtom
        (fun ω => prob_13_2_thresholdY sigma (X ω)) 2,
        prob_13_2_E_X_given_Y_value sigma
          (prob_13_2_thresholdY sigma (X ω)) ∂P) =
      sigma * prob_13_2_standardNormalPdfAtOne := by
  let Y : Ω → ℝ := fun ω => prob_13_2_thresholdY sigma (X ω)
  let Z : Ω → ℝ := fun ω => X ω / sigma
  have hZmeas : Measurable Z := hXmeas.div_const sigma
  have hZlaw : HasLaw Z (ProbabilityTheory.gaussianReal 0 (1 : NNReal)) P :=
    prob_13_2_gaussian_scale_to_standard hsigma hXlaw
  have hAtom : prob_13_2_observationAtom Y 2 = {ω | sigma < X ω} := by
    exact scratch_atom_right X hsigma
  have hStd : {ω : Ω | sigma < X ω} = {ω | Z ω ∈ Set.Ioi (1 : ℝ)} := by
    rw [← prob_13_2_standard_threshold_right_event (X := X) (sigma := sigma) hsigma]
    rfl
  have hset : MeasurableSet {ω : Ω | sigma < X ω} := by
    rw [hStd]
    exact measurableSet_Ioi.preimage hZmeas
  rw [hAtom]
  calc
    (∫ ω in {ω : Ω | sigma < X ω},
        prob_13_2_E_X_given_Y_value sigma (Y ω) ∂P) =
        ∫ _ω in {ω : Ω | sigma < X ω},
          prob_13_2_positiveTailMean sigma ∂P := by
      refine setIntegral_congr_fun hset ?_
      intro ω hω
      have hxgt : sigma < X ω := hω
      have hnleft : ¬ X ω < -sigma := by
        intro hleft
        linarith [hsigma, hxgt, hleft]
      have hnmid : ¬ X ω <= sigma := not_le_of_gt hxgt
      have hYω : Y ω = 1 := by
        simp [Y, prob_13_2_thresholdY, hnleft, hnmid]
      norm_num [prob_13_2_E_X_given_Y_value, hYω]
    _ = P.real {ω : Ω | sigma < X ω} *
          prob_13_2_positiveTailMean sigma := by
      rw [setIntegral_const]
      simp [smul_eq_mul]
    _ = prob_13_2_standardNormalUpperTailMass *
          prob_13_2_positiveTailMean sigma := by
      have hm := scratch_measureReal_preimage_Ioi hZmeas hZlaw
      rw [hStd]
      rw [hm]
    _ = sigma * prob_13_2_standardNormalPdfAtOne := by
      have hmass : prob_13_2_standardNormalUpperTailMass ≠ 0 :=
        prob_13_2_standardNormal_right_tail_mass_toReal_ne_zero
      unfold prob_13_2_positiveTailMean
      field_simp [hmass]

theorem scratch_CEY_mid_atom_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {sigma : ℝ}
    (hsigma : 0 < sigma) (hXmeas : Measurable X) :
    (∫ ω in prob_13_2_observationAtom
        (fun ω => prob_13_2_thresholdY sigma (X ω)) 1,
        prob_13_2_E_X_given_Y_value sigma
          (prob_13_2_thresholdY sigma (X ω)) ∂P) = 0 := by
  let Y : Ω → ℝ := fun ω => prob_13_2_thresholdY sigma (X ω)
  have hAtom : prob_13_2_observationAtom Y 1 =
      {ω | -sigma <= X ω ∧ X ω <= sigma} := by
    exact scratch_atom_mid X
  have hset : MeasurableSet {ω : Ω | -sigma <= X ω ∧ X ω <= sigma} :=
    (measurableSet_le measurable_const hXmeas).inter
      (measurableSet_le hXmeas measurable_const)
  rw [hAtom]
  calc
    (∫ ω in {ω : Ω | -sigma <= X ω ∧ X ω <= sigma},
        prob_13_2_E_X_given_Y_value sigma (Y ω) ∂P) =
        ∫ _ω in {ω : Ω | -sigma <= X ω ∧ X ω <= sigma}, (0 : ℝ) ∂P := by
      refine setIntegral_congr_fun hset ?_
      intro ω hω
      have hnleft : ¬ X ω < -sigma := not_lt_of_ge hω.1
      simp [Y, prob_13_2_thresholdY, prob_13_2_E_X_given_Y_value, hnleft, hω.2]
    _ = 0 := by simp

theorem scratch_atom_sq_neg_empty {Ω : Type*} (X : Ω → ℝ) {sigma : ℝ} :
    prob_13_2_observationAtom
        (fun ω => (prob_13_2_thresholdY sigma (X ω)) ^ 2) 0 =
      (∅ : Set Ω) := by
  ext ω
  unfold prob_13_2_observationAtom prob_13_2_threeLabel prob_13_2_thresholdY
  by_cases hleft : X ω < -sigma
  · simp [hleft] <;> norm_num
  · by_cases hmid : X ω <= sigma
    · simp [hleft, hmid]
    · simp [hleft, hmid] <;> norm_num

theorem scratch_atom_sq_zero {Ω : Type*} (X : Ω → ℝ) {sigma : ℝ} :
    prob_13_2_observationAtom
        (fun ω => (prob_13_2_thresholdY sigma (X ω)) ^ 2) 1 =
      {ω | -sigma <= X ω ∧ X ω <= sigma} := by
  ext ω
  unfold prob_13_2_observationAtom prob_13_2_threeLabel prob_13_2_thresholdY
  by_cases hleft : X ω < -sigma
  · have hnot : ¬ (-sigma <= X ω ∧ X ω <= sigma) := by
      intro h
      exact not_lt_of_ge h.1 hleft
    simp [hleft, hnot]
  · by_cases hmid : X ω <= sigma
    · have hge : -sigma <= X ω := le_of_not_gt hleft
      simp [hleft, hmid, hge]
    · have hnot : ¬ (-sigma <= X ω ∧ X ω <= sigma) := by
        intro h
        exact hmid h.2
      simp [hleft, hmid, hnot]

theorem scratch_atom_sq_one {Ω : Type*} (X : Ω → ℝ) {sigma : ℝ}
    (hsigma : 0 < sigma) :
    prob_13_2_observationAtom
        (fun ω => (prob_13_2_thresholdY sigma (X ω)) ^ 2) 2 =
      {ω | X ω < -sigma} ∪ {ω | sigma < X ω} := by
  ext ω
  unfold prob_13_2_observationAtom prob_13_2_threeLabel prob_13_2_thresholdY
  by_cases hleft : X ω < -sigma
  · have hnright : ¬ sigma < X ω := by
      intro hright
      linarith [hsigma, hleft, hright]
    simp [hleft, hnright]
  · by_cases hmid : X ω <= sigma
    · have hnright : ¬ sigma < X ω := not_lt_of_ge hmid
      simp [hleft, hmid, hnright]
    · have hright : sigma < X ω := lt_of_not_ge hmid
      simp [hleft, hmid, hright]

theorem scratch_X_sq_neg_atom_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {sigma : ℝ} :
    (∫ ω in prob_13_2_observationAtom
        (fun ω => (prob_13_2_thresholdY sigma (X ω)) ^ 2) 0, X ω ∂P) = 0 := by
  rw [scratch_atom_sq_neg_empty X]
  simp

theorem scratch_X_sq_zero_atom_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {sigma : ℝ}
    (hsigma : 0 < sigma) (hXmeas : Measurable X)
    (hXlaw : HasLaw X
      (ProbabilityTheory.gaussianReal 0 (⟨sigma ^ 2, sq_nonneg sigma⟩ : NNReal)) P) :
    (∫ ω in prob_13_2_observationAtom
        (fun ω => (prob_13_2_thresholdY sigma (X ω)) ^ 2) 1, X ω ∂P) = 0 := by
  rw [scratch_atom_sq_zero X]
  rw [← scratch_atom_mid X]
  exact scratch_X_mid_atom_integral hsigma hXmeas hXlaw

theorem scratch_X_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {sigma : ℝ}
    (hXmeas : Measurable X)
    (hXlaw : HasLaw X
      (ProbabilityTheory.gaussianReal 0 (⟨sigma ^ 2, sq_nonneg sigma⟩ : NNReal)) P) :
    Integrable X P := by
  have hMapMem : MemLp id (1 : ℝ≥0∞)
      (ProbabilityTheory.gaussianReal 0 (⟨sigma ^ 2, sq_nonneg sigma⟩ : NNReal)) :=
    ProbabilityTheory.memLp_id_gaussianReal' (μ := 0)
      (v := (⟨sigma ^ 2, sq_nonneg sigma⟩ : NNReal)) (p := 1) (by norm_num)
  have hMapMem' : MemLp id (1 : ℝ≥0∞) (Measure.map X P) := by
    simpa [hXlaw.map_eq] using hMapMem
  have hXmem : MemLp X (1 : ℝ≥0∞) P := by
    simpa [Function.comp_def] using
      (memLp_map_measure_iff hMapMem'.aestronglyMeasurable hXlaw.aemeasurable).1 hMapMem'
  exact memLp_one_iff_integrable.mp hXmem

theorem scratch_X_sq_one_atom_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {sigma : ℝ}
    [IsProbabilityMeasure P]
    (hsigma : 0 < sigma) (hXmeas : Measurable X)
    (hXlaw : HasLaw X
      (ProbabilityTheory.gaussianReal 0 (⟨sigma ^ 2, sq_nonneg sigma⟩ : NNReal)) P) :
    (∫ ω in prob_13_2_observationAtom
        (fun ω => (prob_13_2_thresholdY sigma (X ω)) ^ 2) 2, X ω ∂P) = 0 := by
  let L : Set Ω := {ω | X ω < -sigma}
  let R : Set Ω := {ω | sigma < X ω}
  have hL : MeasurableSet L := measurableSet_lt hXmeas measurable_const
  have hR : MeasurableSet R := measurableSet_lt measurable_const hXmeas
  have hdisj : Disjoint L R := by
    rw [Set.disjoint_left]
    intro ω hLω hRω
    dsimp [L, R] at hLω hRω
    linarith [hsigma, hLω, hRω]
  have hXL : ∫ ω in L, X ω ∂P = -sigma * prob_13_2_standardNormalPdfAtOne := by
    dsimp [L]
    rw [← scratch_atom_left X]
    exact scratch_X_left_atom_integral hsigma hXmeas hXlaw
  have hXR : ∫ ω in R, X ω ∂P = sigma * prob_13_2_standardNormalPdfAtOne := by
    dsimp [R]
    rw [← scratch_atom_right X hsigma]
    exact scratch_X_right_atom_integral hsigma hXmeas hXlaw
  have hXint : Integrable X P := scratch_X_integrable hXmeas hXlaw
  have hXLint : IntegrableOn X L P := hXint.integrableOn
  have hXRint : IntegrableOn X R P := hXint.integrableOn
  rw [scratch_atom_sq_one X hsigma]
  rw [show ({ω | X ω < -sigma} ∪ {ω | sigma < X ω}) = L ∪ R by rfl]
  rw [setIntegral_union hdisj hR hXLint hXRint]
  rw [hXL, hXR]
  ring

theorem scratch_CEYsq_neg_atom_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {sigma : ℝ} :
    (∫ ω in prob_13_2_observationAtom
        (fun ω => (prob_13_2_thresholdY sigma (X ω)) ^ 2) 0, (0 : ℝ) ∂P) =
      ∫ ω in prob_13_2_observationAtom
        (fun ω => (prob_13_2_thresholdY sigma (X ω)) ^ 2) 0, X ω ∂P := by
  rw [scratch_X_sq_neg_atom_integral]
  simp

theorem scratch_CEYsq_zero_atom_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {sigma : ℝ}
    (hsigma : 0 < sigma) (hXmeas : Measurable X)
    (hXlaw : HasLaw X
      (ProbabilityTheory.gaussianReal 0 (⟨sigma ^ 2, sq_nonneg sigma⟩ : NNReal)) P) :
    (∫ ω in prob_13_2_observationAtom
        (fun ω => (prob_13_2_thresholdY sigma (X ω)) ^ 2) 1, (0 : ℝ) ∂P) =
      ∫ ω in prob_13_2_observationAtom
        (fun ω => (prob_13_2_thresholdY sigma (X ω)) ^ 2) 1, X ω ∂P := by
  rw [scratch_X_sq_zero_atom_integral hsigma hXmeas hXlaw]
  simp

theorem scratch_CEYsq_one_atom_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {sigma : ℝ}
    [IsProbabilityMeasure P]
    (hsigma : 0 < sigma) (hXmeas : Measurable X)
    (hXlaw : HasLaw X
      (ProbabilityTheory.gaussianReal 0 (⟨sigma ^ 2, sq_nonneg sigma⟩ : NNReal)) P) :
    (∫ ω in prob_13_2_observationAtom
        (fun ω => (prob_13_2_thresholdY sigma (X ω)) ^ 2) 2, (0 : ℝ) ∂P) =
      ∫ ω in prob_13_2_observationAtom
        (fun ω => (prob_13_2_thresholdY sigma (X ω)) ^ 2) 2, X ω ∂P := by
  rw [scratch_X_sq_one_atom_integral hsigma hXmeas hXlaw]
  simp

theorem scratch_answer_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {sigma : ℝ}
    (hXmeas : Measurable X) :
    Integrable
      (fun ω => prob_13_2_E_X_given_Y_value sigma
        (prob_13_2_thresholdY sigma (X ω))) P := by
  have hYmeas : Measurable (fun ω => prob_13_2_thresholdY sigma (X ω)) :=
    (scratch_thresholdY_measurable sigma).comp hXmeas
  have hCEmeas : Measurable
      (fun ω => prob_13_2_E_X_given_Y_value sigma
        (prob_13_2_thresholdY sigma (X ω))) :=
    (scratch_answer_measurable sigma).comp hYmeas
  refine Integrable.of_bound hCEmeas.aestronglyMeasurable
    (|prob_13_2_positiveTailMean sigma|) ?_
  refine ae_of_all _ ?_
  intro ω
  have hYrange :
      prob_13_2_thresholdY sigma (X ω) = -1 ∨
        prob_13_2_thresholdY sigma (X ω) = 0 ∨
        prob_13_2_thresholdY sigma (X ω) = 1 :=
    scratch_thresholdY_range
  rcases hYrange with hY | hY | hY <;>
    simp [hY, prob_13_2_E_X_given_Y_value] <;> norm_num

theorem prob_13_2 {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {sigma : ℝ}
    (hsigma : 0 < sigma) (hXmeas : Measurable X)
    (hXlaw : HasLaw X
      (ProbabilityTheory.gaussianReal 0 (⟨sigma ^ 2, sq_nonneg sigma⟩ : NNReal)) P) :
    def_13_4 P (fun ω => prob_13_2_thresholdY sigma (X ω))
      (def_13_4_sigma_subSigma_of_measurable
        ((scratch_thresholdY_measurable sigma).comp hXmeas)) X
      (fun ω => prob_13_2_E_X_given_Y_value sigma
        (prob_13_2_thresholdY sigma (X ω))) ∧
    def_13_4 P (fun ω => (prob_13_2_thresholdY sigma (X ω)) ^ 2)
      (def_13_4_sigma_subSigma_of_measurable
        (by
          have hYmeas : Measurable
              (fun ω => prob_13_2_thresholdY sigma (X ω)) :=
            (scratch_thresholdY_measurable sigma).comp hXmeas
          simpa [pow_two] using hYmeas.mul hYmeas)) X
      (fun ω => prob_13_2_E_X_given_Y_sq_value sigma
        ((prob_13_2_thresholdY sigma (X ω)) ^ 2)) := by
  let Y : Ω → ℝ := fun ω => prob_13_2_thresholdY sigma (X ω)
  let Ysq : Ω → ℝ := fun ω => (Y ω) ^ 2
  have hYmeas : Measurable Y :=
    (scratch_thresholdY_measurable sigma).comp hXmeas
  have hYsqmeas : Measurable Ysq := by
    simpa [Ysq, Y, pow_two] using hYmeas.mul hYmeas
  have hXint : Integrable X P := scratch_X_integrable hXmeas hXlaw
  have hCEint : Integrable
      (fun ω => prob_13_2_E_X_given_Y_value sigma (Y ω)) P := by
    simpa [Y] using scratch_answer_integrable (P := P) (X := X) (sigma := sigma) hXmeas
  have hYsigma : Measurable[def_13_4_sigma Y] Y := by
    rw [def_13_4_sigma]
    exact comap_measurable Y
  have hCEmeas : Measurable[def_13_4_sigma Y]
      (fun ω => prob_13_2_E_X_given_Y_value sigma (Y ω)) :=
    (scratch_answer_measurable sigma).comp hYsigma
  have hYrange : ∀ ω, Y ω = -1 ∨ Y ω = 0 ∨ Y ω = 1 := by
    intro ω
    exact scratch_thresholdY_range
  have hm :
      ∫ ω in prob_13_2_observationAtom Y 0,
          prob_13_2_E_X_given_Y_value sigma (Y ω) ∂P =
        ∫ ω in prob_13_2_observationAtom Y 0, X ω ∂P := by
    dsimp [Y]
    rw [scratch_CEY_left_atom_integral hsigma hXmeas hXlaw,
      scratch_X_left_atom_integral hsigma hXmeas hXlaw]
  have h0 :
      ∫ ω in prob_13_2_observationAtom Y 1,
          prob_13_2_E_X_given_Y_value sigma (Y ω) ∂P =
        ∫ ω in prob_13_2_observationAtom Y 1, X ω ∂P := by
    dsimp [Y]
    rw [scratch_CEY_mid_atom_integral hsigma hXmeas,
      scratch_X_mid_atom_integral hsigma hXmeas hXlaw]
  have h1 :
      ∫ ω in prob_13_2_observationAtom Y 2,
          prob_13_2_E_X_given_Y_value sigma (Y ω) ∂P =
        ∫ ω in prob_13_2_observationAtom Y 2, X ω ∂P := by
    dsimp [Y]
    rw [scratch_CEY_right_atom_integral hsigma hXmeas hXlaw,
      scratch_X_right_atom_integral hsigma hXmeas hXlaw]
  have hFirst :
      def_13_4 P Y (def_13_4_sigma_subSigma_of_measurable hYmeas) X
        (fun ω => prob_13_2_E_X_given_Y_value sigma (Y ω)) :=
    prob_13_2_finite_observation_def_13_4_atom_bridge
      hXint hCEint hYmeas hCEmeas hYrange hm h0 h1
  have hCEsqint : Integrable
      (fun ω => prob_13_2_E_X_given_Y_sq_value sigma (Ysq ω)) P := by
    simpa [prob_13_2_E_X_given_Y_sq_value] using
      (integrable_zero (α := Ω) (μ := P) (𝕜 := ℝ))
  have hCEsqmeas : Measurable[def_13_4_sigma Ysq]
      (fun ω => prob_13_2_E_X_given_Y_sq_value sigma (Ysq ω)) := by
    simpa [prob_13_2_E_X_given_Y_sq_value] using
      (measurable_const : Measurable[def_13_4_sigma Ysq] (fun _ : Ω => (0 : ℝ)))
  have hYsqrange : ∀ ω, Ysq ω = -1 ∨ Ysq ω = 0 ∨ Ysq ω = 1 := by
    intro ω
    have hYω : Y ω = -1 ∨ Y ω = 0 ∨ Y ω = 1 := hYrange ω
    rcases hYω with hYω | hYω | hYω
    · right; right; simp [Ysq, hYω]
    · right; left; simp [Ysq, hYω]
    · right; right; simp [Ysq, hYω]
  have hmSq :
      ∫ ω in prob_13_2_observationAtom Ysq 0,
          prob_13_2_E_X_given_Y_sq_value sigma (Ysq ω) ∂P =
        ∫ ω in prob_13_2_observationAtom Ysq 0, X ω ∂P := by
    dsimp [Ysq, Y]
    simpa [prob_13_2_E_X_given_Y_sq_value] using
      scratch_CEYsq_neg_atom_integral (P := P) (X := X) (sigma := sigma)
  have h0Sq :
      ∫ ω in prob_13_2_observationAtom Ysq 1,
          prob_13_2_E_X_given_Y_sq_value sigma (Ysq ω) ∂P =
        ∫ ω in prob_13_2_observationAtom Ysq 1, X ω ∂P := by
    dsimp [Ysq, Y]
    simpa [prob_13_2_E_X_given_Y_sq_value] using
      scratch_CEYsq_zero_atom_integral (P := P) (X := X)
        (sigma := sigma) hsigma hXmeas hXlaw
  have h1Sq :
      ∫ ω in prob_13_2_observationAtom Ysq 2,
          prob_13_2_E_X_given_Y_sq_value sigma (Ysq ω) ∂P =
        ∫ ω in prob_13_2_observationAtom Ysq 2, X ω ∂P := by
    dsimp [Ysq, Y]
    simpa [prob_13_2_E_X_given_Y_sq_value] using
      scratch_CEYsq_one_atom_integral (P := P) (X := X)
        (sigma := sigma) hsigma hXmeas hXlaw
  have hSecond :
      def_13_4 P Ysq (def_13_4_sigma_subSigma_of_measurable hYsqmeas) X
        (fun ω => prob_13_2_E_X_given_Y_sq_value sigma (Ysq ω)) :=
    prob_13_2_finite_observation_def_13_4_atom_bridge
      hXint hCEsqint hYsqmeas hCEsqmeas hYsqrange hmSq h0Sq h1Sq
  simpa [Y, Ysq] using And.intro hFirst hSecond
