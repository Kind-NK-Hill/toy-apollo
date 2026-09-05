/-
TASK ID: ex_8_1_2
TYPE: Example_Proof
SOURCE PLAN: 31_chap8_coupling
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_07.prob_7_2




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

noncomputable section

 
def gaussianWithStdDev (μ σ : ℝ) : Measure ℝ :=
  gaussianReal μ ⟨σ ^ 2, sq_nonneg σ⟩

instance (μ σ : ℝ) : IsGaussian (gaussianWithStdDev μ σ) := by
  dsimp [gaussianWithStdDev]
  infer_instance

 
def gaussianAffineTransport (μ₁ μ₂ σ₁ σ₂ : ℝ) : ℝ → ℝ :=
  fun x => (σ₂ / σ₁) * (x - μ₁) + μ₂

@[fun_prop]
lemma gaussianAffineTransport_measurable (μ₁ μ₂ σ₁ σ₂ : ℝ) :
    Measurable (gaussianAffineTransport μ₁ μ₂ σ₁ σ₂) := by
  unfold gaussianAffineTransport
  fun_prop

@[fun_prop]
lemma gaussianAffineTransport_continuous (μ₁ μ₂ σ₁ σ₂ : ℝ) :
    Continuous (gaussianAffineTransport μ₁ μ₂ σ₁ σ₂) := by
  unfold gaussianAffineTransport
  fun_prop

 
theorem gaussianAffineTransport_map (μ₁ μ₂ σ₁ σ₂ : ℝ) (hσ₁ : 0 < σ₁) :
    Measure.map (gaussianAffineTransport μ₁ μ₂ σ₁ σ₂)
        (gaussianWithStdDev μ₁ σ₁) =
      gaussianWithStdDev μ₂ σ₂ := by
  let a := σ₂ / σ₁
  calc
    Measure.map (gaussianAffineTransport μ₁ μ₂ σ₁ σ₂)
        (gaussianWithStdDev μ₁ σ₁) =
        Measure.map (fun z : ℝ => z + μ₂)
          (Measure.map (fun z : ℝ => a * z)
            (Measure.map (fun x : ℝ => x - μ₁)
              (gaussianWithStdDev μ₁ σ₁))) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop),
            Measure.map_map (by fun_prop) (by fun_prop)]
          congr 1
    _ = gaussianWithStdDev μ₂ σ₂ := by
      simp only [gaussianWithStdDev, gaussianReal_map_sub_const,
        gaussianReal_map_const_mul, gaussianReal_map_add_const]
      simp only [sub_self, mul_zero, zero_add]
      congr 2
      ext
      change a ^ 2 * σ₁ ^ 2 = σ₂ ^ 2
      dsimp [a]
      field_simp [ne_of_gt hσ₁]

 
def deterministicGaussianJoint (μ₁ μ₂ σ₁ σ₂ : ℝ) : Measure (ℝ × ℝ) :=
  Measure.map (fun x => (x, gaussianAffineTransport μ₁ μ₂ σ₁ σ₂ x))
    (gaussianWithStdDev μ₁ σ₁)

 
theorem deterministicGaussianJoint_fst (μ₁ μ₂ σ₁ σ₂ : ℝ) :
    Measure.map Prod.fst (deterministicGaussianJoint μ₁ μ₂ σ₁ σ₂) =
      gaussianWithStdDev μ₁ σ₁ := by
  rw [deterministicGaussianJoint,
    Measure.map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def]

 
theorem deterministicGaussianJoint_snd (μ₁ μ₂ σ₁ σ₂ : ℝ) (hσ₁ : 0 < σ₁) :
    Measure.map Prod.snd (deterministicGaussianJoint μ₁ μ₂ σ₁ σ₂) =
      gaussianWithStdDev μ₂ σ₂ := by
  rw [deterministicGaussianJoint,
    Measure.map_map (by fun_prop) (by fun_prop)]
  simpa [Function.comp_def] using
    gaussianAffineTransport_map μ₁ μ₂ σ₁ σ₂ hσ₁

 
theorem deterministicGaussianJoint_isGaussian (μ₁ μ₂ σ₁ σ₂ : ℝ) :
    IsGaussian (deterministicGaussianJoint μ₁ μ₂ σ₁ σ₂) := by
  let a : ℝ := σ₂ / σ₁
  let L : ℝ →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.id ℝ ℝ).prod (a • ContinuousLinearMap.id ℝ ℝ)
  let centered :=
    Measure.map (fun x : ℝ => x - μ₁) (gaussianWithStdDev μ₁ σ₁)
  let linearJoint := Measure.map L centered
  haveI : IsGaussian centered := by
    dsimp [centered, gaussianWithStdDev]
    infer_instance
  haveI : IsGaussian linearJoint := by
    dsimp [linearJoint]
    infer_instance
  have hmeasure :
      deterministicGaussianJoint μ₁ μ₂ σ₁ σ₂ =
        Measure.map (fun p : ℝ × ℝ => p + (μ₁, μ₂)) linearJoint := by
    dsimp [linearJoint, centered]
    rw [deterministicGaussianJoint,
      Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    ext <;> simp [Function.comp_def, L, a, gaussianAffineTransport]
  rw [hmeasure]
  infer_instance

 
def gaussianTransportGraph (μ₁ μ₂ σ₁ σ₂ : ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 = gaussianAffineTransport μ₁ μ₂ σ₁ σ₂ p.1}

lemma gaussianTransportGraph_measurable (μ₁ μ₂ σ₁ σ₂ : ℝ) :
    MeasurableSet (gaussianTransportGraph μ₁ μ₂ σ₁ σ₂) := by
  exact
    (isClosed_eq continuous_snd
      ((gaussianAffineTransport_continuous μ₁ μ₂ σ₁ σ₂).comp
        continuous_fst)).measurableSet

 
theorem gaussianTransportGraph_volume (μ₁ μ₂ σ₁ σ₂ : ℝ) :
    (volume : Measure (ℝ × ℝ)) (gaussianTransportGraph μ₁ μ₂ σ₁ σ₂) = 0 := by
  change (volume.prod volume) (gaussianTransportGraph μ₁ μ₂ σ₁ σ₂) = 0
  apply Measure.measure_prod_null_of_ae_null
    (gaussianTransportGraph_measurable μ₁ μ₂ σ₁ σ₂)
  filter_upwards [] with x
  have hsection :
      Prod.mk x ⁻¹' gaussianTransportGraph μ₁ μ₂ σ₁ σ₂ =
        {gaussianAffineTransport μ₁ μ₂ σ₁ σ₂ x} := by
    ext y
    simp [gaussianTransportGraph]
  simp [hsection]

 
theorem deterministicGaussianJoint_singular (μ₁ μ₂ σ₁ σ₂ : ℝ) :
    deterministicGaussianJoint μ₁ μ₂ σ₁ σ₂ ⟂ₘ
      (volume : Measure (ℝ × ℝ)) := by
  let G := gaussianTransportGraph μ₁ μ₂ σ₁ σ₂
  apply Measure.MutuallySingular.mk (s := Gᶜ) (t := G)
  · rw [deterministicGaussianJoint,
      Measure.map_apply (by fun_prop)
        (gaussianTransportGraph_measurable μ₁ μ₂ σ₁ σ₂).compl]
    simp [gaussianTransportGraph]
  · exact gaussianTransportGraph_volume μ₁ μ₂ σ₁ σ₂
  · simp [G]

 
theorem deterministicGaussian_not_independent
    (μ₁ μ₂ σ₁ σ₂ : ℝ) (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂) :
    ¬ IndepFun id (gaussianAffineTransport μ₁ μ₂ σ₁ σ₂)
      (gaussianWithStdDev μ₁ σ₁) := by
  let P := gaussianWithStdDev μ₁ σ₁
  let a := σ₂ / σ₁
  haveI : IsGaussian P := by
    dsimp [P, gaussianWithStdDev]
    infer_instance
  have hX : MemLp (id : ℝ → ℝ) 2 P := by
    dsimp [P, gaussianWithStdDev]
    simpa using
      memLp_id_gaussianReal (μ := μ₁)
        (v := ⟨σ₁ ^ 2, sq_nonneg σ₁⟩) 2
  have hcenter : MemLp (fun x : ℝ => id x - μ₁) 2 P :=
    hX.sub (memLp_const μ₁)
  have hscale : MemLp (fun x : ℝ => a * (id x - μ₁)) 2 P :=
    hcenter.const_mul a
  have hY : MemLp (gaussianAffineTransport μ₁ μ₂ σ₁ σ₂) 2 P := by
    have htarget : MemLp (id : ℝ → ℝ) 2 (gaussianWithStdDev μ₂ σ₂) := by
      dsimp [gaussianWithStdDev]
      simpa using
        memLp_id_gaussianReal (μ := μ₂)
          (v := ⟨σ₂ ^ 2, sq_nonneg σ₂⟩) 2
    have hpres :
        MeasurePreserving (gaussianAffineTransport μ₁ μ₂ σ₁ σ₂) P
          (gaussianWithStdDev μ₂ σ₂) :=
      ⟨gaussianAffineTransport_measurable μ₁ μ₂ σ₁ σ₂,
        gaussianAffineTransport_map μ₁ μ₂ σ₁ σ₂ hσ₁⟩
    simpa [Function.comp_def] using htarget.comp_measurePreserving hpres
  have hcov :
      cov[id, gaussianAffineTransport μ₁ μ₂ σ₁ σ₂; P] = σ₁ * σ₂ := by
    change cov[id, fun x : ℝ => a * (id x - μ₁) + μ₂; P] = σ₁ * σ₂
    rw [covariance_add_const_right (hscale.integrable (by norm_num)) μ₂]
    rw [covariance_const_mul_right]
    rw [covariance_sub_const_right (hX.integrable (by norm_num)) μ₁]
    rw [covariance_self measurable_id.aemeasurable]
    dsimp [P, gaussianWithStdDev]
    rw [variance_id_gaussianReal]
    change a * σ₁ ^ 2 = σ₁ * σ₂
    dsimp [a]
    field_simp [ne_of_gt hσ₁]
  intro hindep
  have hzero := hindep.covariance_eq_zero hX hY
  rw [hcov] at hzero
  nlinarith

 
def unitIntervalLaw : Measure ℝ :=
  volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure unitIntervalLaw := by
  rw [isProbabilityMeasure_iff]
  simp [unitIntervalLaw]

 
def unitSquareLaw : Measure (ℝ × ℝ) :=
  unitIntervalLaw.prod unitIntervalLaw

instance : IsProbabilityMeasure unitSquareLaw := by
  dsimp [unitSquareLaw]
  infer_instance

 
theorem unitSquare_fst_uniform :
    Measure.map Prod.fst unitSquareLaw = unitIntervalLaw :=
  measurePreserving_fst.map_eq

 
theorem unitSquare_snd_uniform :
    Measure.map Prod.snd unitSquareLaw = unitIntervalLaw :=
  measurePreserving_snd.map_eq

 
theorem unitSquare_coordinates_independent :
    IndepFun Prod.fst Prod.snd unitSquareLaw :=
  indepFun_prod measurable_id measurable_id

 
def gaussianRescale (μ σ : ℝ) : ℝ → ℝ :=
  fun z => μ + σ * z

@[fun_prop]
lemma gaussianRescale_measurable (μ σ : ℝ) :
    Measurable (gaussianRescale μ σ) := by
  unfold gaussianRescale
  fun_prop

 
theorem gaussianRescale_map (μ σ : ℝ) :
    Measure.map (gaussianRescale μ σ) (gaussianReal 0 1) =
      gaussianWithStdDev μ σ := by
  calc
    Measure.map (gaussianRescale μ σ) (gaussianReal 0 1) =
        Measure.map (fun z : ℝ => μ + z)
          (Measure.map (fun z : ℝ => σ * z) (gaussianReal 0 1)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
    _ = gaussianWithStdDev μ σ := by
      rw [gaussianReal_map_const_mul, gaussianReal_map_const_add]
      unfold gaussianWithStdDev
      simp only [mul_zero, zero_add, mul_one]
      congr 1

 
def gaussianPairRescale (μ₁ μ₂ σ₁ σ₂ : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  Prod.map (gaussianRescale μ₁ σ₁) (gaussianRescale μ₂ σ₂)

@[fun_prop]
lemma gaussianPairRescale_measurable (μ₁ μ₂ σ₁ σ₂ : ℝ) :
    Measurable (gaussianPairRescale μ₁ μ₂ σ₁ σ₂) := by
  unfold gaussianPairRescale
  fun_prop

 
def independentGaussianMap (μ₁ μ₂ σ₁ σ₂ : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  fun p => gaussianPairRescale μ₁ μ₂ σ₁ σ₂ (boxMullerMap p)

lemma independentGaussianMap_measurable (μ₁ μ₂ σ₁ σ₂ : ℝ) :
    Measurable (independentGaussianMap μ₁ μ₂ σ₁ σ₂) :=
  (gaussianPairRescale_measurable μ₁ μ₂ σ₁ σ₂).comp
    boxMullerMap_measurable

 
def boxMullerGaussianX (μ₁ σ₁ : ℝ) : ℝ × ℝ → ℝ :=
  fun p => (independentGaussianMap μ₁ 0 σ₁ 1 p).1

 
def boxMullerGaussianY (μ₂ σ₂ : ℝ) : ℝ × ℝ → ℝ :=
  fun p => (independentGaussianMap 0 μ₂ 1 σ₂ p).2

@[fun_prop]
lemma boxMullerGaussianX_measurable (μ₁ σ₁ : ℝ) :
    Measurable (boxMullerGaussianX μ₁ σ₁) :=
  measurable_fst.comp (independentGaussianMap_measurable μ₁ 0 σ₁ 1)

@[fun_prop]
lemma boxMullerGaussianY_measurable (μ₂ σ₂ : ℝ) :
    Measurable (boxMullerGaussianY μ₂ σ₂) :=
  measurable_snd.comp (independentGaussianMap_measurable 0 μ₂ 1 σ₂)

 
theorem independentGaussianMap_pushforward (μ₁ μ₂ σ₁ σ₂ : ℝ) :
    Measure.map (independentGaussianMap μ₁ μ₂ σ₁ σ₂) unitSquareLaw =
      (gaussianWithStdDev μ₁ σ₁).prod (gaussianWithStdDev μ₂ σ₂) := by
  calc
    Measure.map (independentGaussianMap μ₁ μ₂ σ₁ σ₂) unitSquareLaw =
        Measure.map (gaussianPairRescale μ₁ μ₂ σ₁ σ₂)
          (Measure.map boxMullerMap unitSquareLaw) := by
      rw [Measure.map_map
        (gaussianPairRescale_measurable μ₁ μ₂ σ₁ σ₂)
        boxMullerMap_measurable]
      rfl
    _ = Measure.map (gaussianPairRescale μ₁ μ₂ σ₁ σ₂)
          ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
      rw [unitSquareLaw, unitIntervalLaw, boxMuller_pushforward_uniform]
    _ = (Measure.map (gaussianRescale μ₁ σ₁) (gaussianReal 0 1)).prod
          (Measure.map (gaussianRescale μ₂ σ₂) (gaussianReal 0 1)) := by
      symm
      simpa [gaussianPairRescale] using
        Measure.map_prod_map (gaussianReal 0 1) (gaussianReal 0 1)
          (gaussianRescale_measurable μ₁ σ₁)
          (gaussianRescale_measurable μ₂ σ₂)
    _ = (gaussianWithStdDev μ₁ σ₁).prod
          (gaussianWithStdDev μ₂ σ₂) := by
      rw [gaussianRescale_map, gaussianRescale_map]

 
theorem boxMullerGaussianX_law (μ₁ σ₁ : ℝ) :
    Measure.map (boxMullerGaussianX μ₁ σ₁) unitSquareLaw =
      gaussianWithStdDev μ₁ σ₁ := by
  calc
    Measure.map (boxMullerGaussianX μ₁ σ₁) unitSquareLaw =
        Measure.map Prod.fst
          (Measure.map (independentGaussianMap μ₁ 0 σ₁ 1) unitSquareLaw) := by
      rw [Measure.map_map measurable_fst
        (independentGaussianMap_measurable μ₁ 0 σ₁ 1)]
      rfl
    _ = Measure.map Prod.fst
          ((gaussianWithStdDev μ₁ σ₁).prod (gaussianWithStdDev 0 1)) := by
      rw [independentGaussianMap_pushforward]
    _ = gaussianWithStdDev μ₁ σ₁ := measurePreserving_fst.map_eq

 
theorem boxMullerGaussianY_law (μ₂ σ₂ : ℝ) :
    Measure.map (boxMullerGaussianY μ₂ σ₂) unitSquareLaw =
      gaussianWithStdDev μ₂ σ₂ := by
  calc
    Measure.map (boxMullerGaussianY μ₂ σ₂) unitSquareLaw =
        Measure.map Prod.snd
          (Measure.map (independentGaussianMap 0 μ₂ 1 σ₂) unitSquareLaw) := by
      rw [Measure.map_map measurable_snd
        (independentGaussianMap_measurable 0 μ₂ 1 σ₂)]
      rfl
    _ = Measure.map Prod.snd
          ((gaussianWithStdDev 0 1).prod (gaussianWithStdDev μ₂ σ₂)) := by
      rw [independentGaussianMap_pushforward]
    _ = gaussianWithStdDev μ₂ σ₂ := measurePreserving_snd.map_eq

 
theorem boxMullerGaussian_coordinates_independent (μ₁ μ₂ σ₁ σ₂ : ℝ) :
    IndepFun (boxMullerGaussianX μ₁ σ₁) (boxMullerGaussianY μ₂ σ₂)
      unitSquareLaw := by
  rw [indepFun_iff_map_prod_eq_prod_map_map
    (boxMullerGaussianX_measurable μ₁ σ₁).aemeasurable
    (boxMullerGaussianY_measurable μ₂ σ₂).aemeasurable]
  rw [show
    (fun p => (boxMullerGaussianX μ₁ σ₁ p,
      boxMullerGaussianY μ₂ σ₂ p)) =
        independentGaussianMap μ₁ μ₂ σ₁ σ₂ by rfl]
  rw [independentGaussianMap_pushforward,
    boxMullerGaussianX_law, boxMullerGaussianY_law]

 
structure GaussianCouplingConclusions (μ₁ μ₂ σ₁ σ₂ : ℝ) : Prop where
  deterministicTransportLaw :
    Measure.map (gaussianAffineTransport μ₁ μ₂ σ₁ σ₂)
        (gaussianWithStdDev μ₁ σ₁) = gaussianWithStdDev μ₂ σ₂
  deterministicFirstMarginal :
    Measure.map Prod.fst (deterministicGaussianJoint μ₁ μ₂ σ₁ σ₂) =
      gaussianWithStdDev μ₁ σ₁
  deterministicSecondMarginal :
    Measure.map Prod.snd (deterministicGaussianJoint μ₁ μ₂ σ₁ σ₂) =
      gaussianWithStdDev μ₂ σ₂
  deterministicJointGaussian :
    IsGaussian (deterministicGaussianJoint μ₁ μ₂ σ₁ σ₂)
  deterministicJointSingular :
    deterministicGaussianJoint μ₁ μ₂ σ₁ σ₂ ⟂ₘ
      (volume : Measure (ℝ × ℝ))
  deterministicNotIndependent :
    ¬ IndepFun id (gaussianAffineTransport μ₁ μ₂ σ₁ σ₂)
      (gaussianWithStdDev μ₁ σ₁)
  squareFirstUniform :
    Measure.map Prod.fst unitSquareLaw = unitIntervalLaw
  squareSecondUniform :
    Measure.map Prod.snd unitSquareLaw = unitIntervalLaw
  squareCoordinatesIndependent :
    IndepFun Prod.fst Prod.snd unitSquareLaw
  independentJointLaw :
    Measure.map (independentGaussianMap μ₁ μ₂ σ₁ σ₂) unitSquareLaw =
      (gaussianWithStdDev μ₁ σ₁).prod (gaussianWithStdDev μ₂ σ₂)
  independentFirstLaw :
    Measure.map (boxMullerGaussianX μ₁ σ₁) unitSquareLaw =
      gaussianWithStdDev μ₁ σ₁
  independentSecondLaw :
    Measure.map (boxMullerGaussianY μ₂ σ₂) unitSquareLaw =
      gaussianWithStdDev μ₂ σ₂
  independentCoordinates :
    IndepFun (boxMullerGaussianX μ₁ σ₁) (boxMullerGaussianY μ₂ σ₂)
      unitSquareLaw



theorem ex_8_1_2 (μ₁ μ₂ σ₁ σ₂ : ℝ) (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂) :
    GaussianCouplingConclusions μ₁ μ₂ σ₁ σ₂ where
  deterministicTransportLaw :=
    gaussianAffineTransport_map μ₁ μ₂ σ₁ σ₂ hσ₁
  deterministicFirstMarginal :=
    deterministicGaussianJoint_fst μ₁ μ₂ σ₁ σ₂
  deterministicSecondMarginal :=
    deterministicGaussianJoint_snd μ₁ μ₂ σ₁ σ₂ hσ₁
  deterministicJointGaussian :=
    deterministicGaussianJoint_isGaussian μ₁ μ₂ σ₁ σ₂
  deterministicJointSingular :=
    deterministicGaussianJoint_singular μ₁ μ₂ σ₁ σ₂
  deterministicNotIndependent :=
    deterministicGaussian_not_independent μ₁ μ₂ σ₁ σ₂ hσ₁ hσ₂
  squareFirstUniform := unitSquare_fst_uniform
  squareSecondUniform := unitSquare_snd_uniform
  squareCoordinatesIndependent := unitSquare_coordinates_independent
  independentJointLaw :=
    independentGaussianMap_pushforward μ₁ μ₂ σ₁ σ₂
  independentFirstLaw := boxMullerGaussianX_law μ₁ σ₁
  independentSecondLaw := boxMullerGaussianY_law μ₂ σ₂
  independentCoordinates :=
    boxMullerGaussian_coordinates_independent μ₁ μ₂ σ₁ σ₂
