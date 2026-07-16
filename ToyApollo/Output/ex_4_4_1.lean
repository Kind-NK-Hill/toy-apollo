import Mathlib
import ToyApollo.Output.def_4_4_complex_random_variable
import ToyApollo.Output.def_4_4_polar_form

open Set MeasureTheory
open scoped ENNReal

noncomputable section

local instance unitDisc_twoPi_pos : Fact (0 < 2 * Real.pi) :=
  ⟨Real.two_pi_pos⟩

/--
Expose on the `Real.Angle` wrapper the measurable structure already carried
by its underlying additive circle.
-/
@[instance_reducible]
def unitDiscAngleMeasurableSpace :
    MeasurableSpace Real.Angle := by
  change MeasurableSpace (AddCircle (2 * Real.pi))
  exact QuotientAddGroup.measurableSpace _

attribute [local instance] unitDiscAngleMeasurableSpace

@[instance_reducible]
def unitDiscAngleBorelSpace : BorelSpace Real.Angle := by
  change BorelSpace (AddCircle (2 * Real.pi))
  infer_instance

attribute [local instance] unitDiscAngleBorelSpace

local instance unitDiscAngleCompactSpace : CompactSpace Real.Angle := by
  change CompactSpace (AddCircle (2 * Real.pi))
  infer_instance

local instance unitDiscAngleLocallyCompactSpace :
    LocallyCompactSpace Real.Angle := by
  change LocallyCompactSpace (AddCircle (2 * Real.pi))
  infer_instance

local instance unitDiscAngleHaarIsProbabilityMeasure :
    IsProbabilityMeasure
      (AddCircle.haarAddCircle : Measure Real.Angle) := by
  change IsProbabilityMeasure
    (@AddCircle.haarAddCircle (2 * Real.pi) unitDisc_twoPi_pos)
  infer_instance
local instance unitDiscAngleHaarIsAddHaarMeasure :
    MeasureTheory.Measure.IsAddHaarMeasure
      (AddCircle.haarAddCircle : Measure Real.Angle) := by
  change MeasureTheory.Measure.IsAddHaarMeasure
    (@AddCircle.haarAddCircle (2 * Real.pi) unitDisc_twoPi_pos)
  infer_instance

/-!
Example 4.4.1 is formalized from the actual uniform law on the open complex
unit disc.  The law is normalized planar volume, the radius computation uses
the strict open-ball event from the source, and the phase conclusion is
obtained from rotation invariance and uniqueness of normalized Haar measure.

The source's displayed factor `2πr²` is a typo for the planar area `πr²`.
The formal calculation below uses `Complex.volume_ball`, so the normalized
ratio is `πr² / π = r²`.
-/

/-- The open unit disc `D = {z : ℂ | ‖z‖ < 1}`. -/
def complexUnitDisc : Set ℂ :=
  Metric.ball (0 : ℂ) 1

/-- The strict radial subdisc `{z : ℂ | ‖z‖ < r}`. -/
def complexRadialSubdisc (r : ℝ) : Set ℂ :=
  {z | complexRadius z < r}

/-- The source radius random variable `|Z|`. -/
def unitDiscRadiusRV {Ω : Type*} (Z : Ω → ℂ) : Ω → ℝ :=
  fun ω => complexRadius (Z ω)

theorem complexRadialSubdisc_eq_ball (r : ℝ) :
    complexRadialSubdisc r = Metric.ball (0 : ℂ) r := by
  ext z
  simp [complexRadialSubdisc, complexRadius, complex_abs,
    Metric.mem_ball, dist_zero_right]

theorem measurableSet_complexUnitDisc :
    MeasurableSet complexUnitDisc := by
  simpa [complexUnitDisc] using
    (measurableSet_ball : MeasurableSet (Metric.ball (0 : ℂ) 1))

/-- Planar volume restricted to the open unit disc, packaged as a finite measure. -/
noncomputable def unitDiscFiniteMeasure : FiniteMeasure ℂ :=
  ⟨volume.restrict complexUnitDisc, by
    rw [isFiniteMeasure_restrict]
    simpa [complexUnitDisc] using
      (measure_ball_ne_top
        (μ := (volume : Measure ℂ)) (x := (0 : ℂ)) (r := (1 : ℝ)))⟩

/-- The probability normalization of restricted planar volume. -/
noncomputable def unitDiscProbability : ProbabilityMeasure ℂ :=
  unitDiscFiniteMeasure.normalize

/-- The uniform probability law on the open complex unit disc. -/
noncomputable def unitDiscLaw : Measure ℂ :=
  unitDiscProbability

instance unitDiscLaw_isProbabilityMeasure :
    IsProbabilityMeasure unitDiscLaw := by
  rw [unitDiscLaw]
  infer_instance

theorem unitDiscFiniteMeasure_mass :
    unitDiscFiniteMeasure.mass = NNReal.pi := by
  apply ENNReal.coe_injective
  rw [FiniteMeasure.ennreal_mass]
  change (volume.restrict complexUnitDisc) Set.univ =
    (NNReal.pi : ENNReal)
  simp [complexUnitDisc]

theorem unitDiscFiniteMeasure_ne_zero :
    unitDiscFiniteMeasure ≠ 0 := by
  apply unitDiscFiniteMeasure.mass_nonzero_iff.mp
  rw [unitDiscFiniteMeasure_mass]
  exact NNReal.pi_ne_zero

/-- The normalized `volume.restrict` law, exposed in measure form. -/
theorem unitDiscLaw_eq_normalized_restrict :
    unitDiscLaw =
      NNReal.pi⁻¹ • (volume.restrict complexUnitDisc : Measure ℂ) := by
  unfold unitDiscLaw unitDiscProbability
  rw [unitDiscFiniteMeasure.toMeasure_normalize_eq_of_nonzero
        unitDiscFiniteMeasure_ne_zero,
      unitDiscFiniteMeasure_mass]
  rfl

/-- Evaluation of the normalized law on a measurable set. -/
theorem unitDiscLaw_apply {A : Set ℂ} (hA : MeasurableSet A) :
    unitDiscLaw A =
      (NNReal.pi : ENNReal)⁻¹ * volume (A ∩ complexUnitDisc) := by
  rw [unitDiscLaw_eq_normalized_restrict,
      Measure.coe_nnreal_smul_apply,
      Measure.restrict_apply hA,
      ENNReal.coe_inv NNReal.pi_ne_zero]

/-- Normalized volume of a concentric strict subdisc. -/
theorem unitDiscLaw_ball
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    unitDiscLaw (Metric.ball (0 : ℂ) r) =
      ENNReal.ofReal (r ^ 2) := by
  have hsub :
      Metric.ball (0 : ℂ) r ⊆ complexUnitDisc := by
    simpa [complexUnitDisc] using
      (Metric.ball_subset_ball (x := (0 : ℂ)) hr1)
  have hpi0 : (NNReal.pi : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr NNReal.pi_ne_zero
  have hpitop : (NNReal.pi : ENNReal) ≠ ∞ :=
    ENNReal.coe_ne_top
  rw [unitDiscLaw_apply measurableSet_ball,
      inter_eq_left.mpr hsub,
      Complex.volume_ball]
  calc
    (NNReal.pi : ENNReal)⁻¹ *
          (ENNReal.ofReal r ^ 2 * (NNReal.pi : ENNReal)) =
        ENNReal.ofReal r ^ 2 * (NNReal.pi : ENNReal)⁻¹ *
          (NNReal.pi : ENNReal) := by
      ac_rfl
    _ = ENNReal.ofReal r ^ 2 :=
      ENNReal.inv_mul_cancel_right hpi0 hpitop
    _ = ENNReal.ofReal (r ^ 2) :=
      (ENNReal.ofReal_pow hr0 2).symm

/-- The strict-radius endpoint at `r = 0`. -/
theorem unitDiscLaw_ball_zero :
    unitDiscLaw (Metric.ball (0 : ℂ) 0) = 0 := by
  simpa using unitDiscLaw_ball 0 le_rfl zero_le_one

/-- The strict-radius endpoint at `r = 1`, equal to the full support mass. -/
theorem unitDiscLaw_ball_one :
    unitDiscLaw (Metric.ball (0 : ℂ) 1) = 1 := by
  simpa using unitDiscLaw_ball 1 zero_le_one le_rfl

theorem unitDiscLaw_complexUnitDisc :
    unitDiscLaw complexUnitDisc = 1 := by
  simpa [complexUnitDisc] using unitDiscLaw_ball_one

/-- The origin is null under normalized planar area. -/
theorem unitDiscLaw_singleton_zero :
    unitDiscLaw ({0} : Set ℂ) = 0 := by
  rw [unitDiscLaw_apply (measurableSet_singleton (0 : ℂ))]
  simp [complexUnitDisc]

theorem unitDiscLaw_ae_ne_zero :
    ∀ᵐ z ∂unitDiscLaw, z ≠ 0 := by
  rw [ae_iff]
  simpa only [not_ne_iff, Set.setOf_eq_eq_singleton] using
    unitDiscLaw_singleton_zero

/-- Transfer of the zero-null fact through a supplied unit-disc law. -/
theorem ae_ne_zero_of_hasLaw_unitDisc
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℂ)
    (hZlaw : ProbabilityTheory.HasLaw Z unitDiscLaw P) :
    ∀ᵐ ω ∂P, Z ω ≠ 0 := by
  have hzero :
      P {ω | Z ω = 0} = 0 := by
    calc
      P {ω | Z ω = 0} =
          unitDiscLaw {z : ℂ | z = 0} := by
        exact hZlaw.measure_eq
          (p := fun z : ℂ => z = 0) (by
            rw [Set.setOf_eq_eq_singleton]
            exact measurableSet_singleton (0 : ℂ))
      _ = unitDiscLaw ({0} : Set ℂ) := by
        rw [Set.setOf_eq_eq_singleton]
      _ = 0 := unitDiscLaw_singleton_zero
  rw [ae_iff]
  simpa only [not_ne_iff] using hzero

/-- The total, measurable angle representative used away from the null origin. -/
noncomputable def unitDiscRawPhase (z : ℂ) : Real.Angle :=
  (Complex.arg z : Real.Angle)

theorem measurable_unitDiscRawPhase :
    Measurable unitDiscRawPhase := by
  change Measurable (Function.comp Real.Angle.coe Complex.arg)
  exact Real.Angle.continuous_coe.measurable.comp Complex.measurable_arg

/-- The project's partial phase agrees almost everywhere with the total representative. -/
theorem complexPhaseRV_ae_eq_some_rawPhase
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℂ)
    (hZne : ∀ᵐ ω ∂P, Z ω ≠ 0) :
    complexPhaseRV Z =ᵐ[P]
      fun ω => some (unitDiscRawPhase (Z ω)) := by
  filter_upwards [hZne] with ω hω
  simpa [complexPhaseRV, unitDiscRawPhase,
      complexPrincipalArgument, complexArgumentDefined] using
    (complexPhase_some_of_defined (z := Z ω) hω)

/-- Root-`rotation` API specialized to the angle acting on `ℂ`. -/
noncomputable def unitDiscRotation (α : Real.Angle) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  rotation α.toCircle

@[simp]
theorem unitDiscRotation_apply (α : Real.Angle) (z : ℂ) :
    unitDiscRotation α z = (α.toCircle : ℂ) * z := by
  exact rotation_apply α.toCircle z

theorem unitDiscRotation_preimage_unitDisc (α : Real.Angle) :
    unitDiscRotation α ⁻¹' complexUnitDisc = complexUnitDisc := by
  change
    (rotation α.toCircle) ⁻¹' Metric.ball (0 : ℂ) 1 =
      Metric.ball (0 : ℂ) 1
  calc
    (rotation α.toCircle) ⁻¹' Metric.ball (0 : ℂ) 1 =
        Metric.ball ((rotation α.toCircle).symm 0) 1 :=
      (rotation α.toCircle).preimage_ball (0 : ℂ) (1 : ℝ)
    _ = Metric.ball (0 : ℂ) 1 := by
      rw [(rotation α.toCircle).symm.map_zero]

theorem unitDiscRotation_map_restricted_volume (α : Real.Angle) :
    Measure.map (unitDiscRotation α)
        (volume.restrict complexUnitDisc) =
      volume.restrict complexUnitDisc := by
  have hrestrict :=
    Measure.restrict_map
      (μ := (volume : Measure ℂ))
      (unitDiscRotation α).continuous.measurable
      measurableSet_complexUnitDisc
  rw [(LinearIsometryEquiv.measurePreserving
        (unitDiscRotation α)).map_eq,
      unitDiscRotation_preimage_unitDisc α] at hrestrict
  exact hrestrict.symm

theorem unitDiscLaw_map_unitDiscRotation (α : Real.Angle) :
    Measure.map (unitDiscRotation α) unitDiscLaw =
      unitDiscLaw := by
  calc
    Measure.map (unitDiscRotation α) unitDiscLaw =
        Measure.map (unitDiscRotation α)
          (NNReal.pi⁻¹ •
            (volume.restrict complexUnitDisc : Measure ℂ)) := by
      rw [unitDiscLaw_eq_normalized_restrict]
    _ = NNReal.pi⁻¹ •
        Measure.map (unitDiscRotation α)
          (volume.restrict complexUnitDisc) := by
      rw [Measure.map_smul]
    _ = NNReal.pi⁻¹ •
        (volume.restrict complexUnitDisc : Measure ℂ) := by
      rw [unitDiscRotation_map_restricted_volume]
    _ = unitDiscLaw :=
      unitDiscLaw_eq_normalized_restrict.symm

/-- Rotation invariance in the source-facing multiplication spelling. -/
theorem unitDiscLaw_map_rotation (α : Real.Angle) :
    Measure.map (fun z : ℂ => (α.toCircle : ℂ) * z)
        unitDiscLaw =
      unitDiscLaw := by
  rw [show (fun z : ℂ => (α.toCircle : ℂ) * z) =
      unitDiscRotation α by
    funext z
    symm
    exact unitDiscRotation_apply α z]
  exact unitDiscLaw_map_unitDiscRotation α

/-- Raw phase is equivariant under rotation away from the null origin. -/
theorem unitDiscRawPhase_ae_equivariant (α : Real.Angle) :
    (fun z : ℂ =>
      unitDiscRawPhase ((α.toCircle : ℂ) * z))
      =ᵐ[unitDiscLaw]
    (fun z : ℂ => α + unitDiscRawPhase z) := by
  filter_upwards [unitDiscLaw_ae_ne_zero] with z hz
  simpa [unitDiscRawPhase] using
    (Complex.arg_mul_coe_angle
      (Circle.coe_ne_zero α.toCircle) hz)

/-- Pushforward law of the total raw phase. -/
noncomputable def rawPhaseLaw : Measure Real.Angle :=
  Measure.map unitDiscRawPhase unitDiscLaw

instance rawPhaseLaw_isProbabilityMeasure :
    IsProbabilityMeasure rawPhaseLaw := by
  unfold rawPhaseLaw
  exact Measure.isProbabilityMeasure_map
    measurable_unitDiscRawPhase.aemeasurable

instance rawPhaseLaw_isAddLeftInvariant :
    MeasureTheory.Measure.IsAddLeftInvariant
      (G := Real.Angle) rawPhaseLaw where
  map_add_left_eq_self (α : Real.Angle) := by
    rw [rawPhaseLaw,
      Measure.map_map
        (measurable_const_add (M := Real.Angle) α)
        measurable_unitDiscRawPhase]
    calc
      Measure.map
          ((fun β : Real.Angle => α + β) ∘
            unitDiscRawPhase)
          unitDiscLaw =
        Measure.map
          (unitDiscRawPhase ∘ unitDiscRotation α)
          unitDiscLaw := by
        apply Measure.map_congr
        simpa [Function.comp_def] using
          (unitDiscRawPhase_ae_equivariant α).symm
      _ = Measure.map unitDiscRawPhase
          (Measure.map (unitDiscRotation α) unitDiscLaw) := by
        symm
        exact Measure.map_map
          measurable_unitDiscRawPhase
          (unitDiscRotation α).continuous.measurable
      _ = Measure.map unitDiscRawPhase unitDiscLaw := by
        rw [unitDiscLaw_map_unitDiscRotation]

instance rawPhaseLaw_isAddHaarMeasure :
    MeasureTheory.Measure.IsAddHaarMeasure
      (G := Real.Angle) rawPhaseLaw :=
  MeasureTheory.Measure.isAddHaarMeasure_of_isCompact_nonempty_interior
    (G := Real.Angle)
    rawPhaseLaw (Set.univ : Set Real.Angle)
    isCompact_univ (by simp) (by simp) (by simp)

/-- Rotation invariance identifies the raw phase law with normalized Haar measure. -/
theorem rawPhaseLaw_eq_haar :
    rawPhaseLaw =
      (AddCircle.haarAddCircle : Measure Real.Angle) := by
  exact @MeasureTheory.Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure
    Real.Angle
    inferInstance
    inferInstance
    inferInstance
    unitDiscAngleMeasurableSpace
    unitDiscAngleBorelSpace
    unitDiscAngleLocallyCompactSpace
    rawPhaseLaw
    (AddCircle.haarAddCircle : Measure Real.Angle)
    unitDiscAngleHaarIsProbabilityMeasure
    rawPhaseLaw_isProbabilityMeasure
    unitDiscAngleHaarIsAddHaarMeasure
    rawPhaseLaw_isAddHaarMeasure

/-- The measurable raw phase has normalized Haar law under `unitDiscLaw`. -/
theorem unitDiscRawPhase_hasLaw :
    ProbabilityTheory.HasLaw unitDiscRawPhase
      (AddCircle.haarAddCircle : Measure Real.Angle)
      unitDiscLaw where
  aemeasurable := measurable_unitDiscRawPhase.aemeasurable
  map_eq := by
    change rawPhaseLaw = (AddCircle.haarAddCircle : Measure Real.Angle)
    exact rawPhaseLaw_eq_haar

/-- A measurable Haar-uniform phase witness agreeing with the partial phase almost everywhere. -/
theorem exists_uniform_unitDisc_phase
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℂ)
    (hZmeas : Measurable Z)
    (hZlaw : ProbabilityTheory.HasLaw Z unitDiscLaw P) :
    ∃ Φ : Ω → Real.Angle,
      Measurable Φ ∧
      ProbabilityTheory.HasLaw Φ
        (AddCircle.haarAddCircle : Measure Real.Angle) P ∧
      complexPhaseRV Z =ᵐ[P] fun ω => some (Φ ω) := by
  let Φ : Ω → Real.Angle :=
    unitDiscRawPhase ∘ Z
  refine ⟨Φ, ?_, ?_, ?_⟩
  · exact measurable_unitDiscRawPhase.comp hZmeas
  · exact unitDiscRawPhase_hasLaw.comp hZlaw
  · simpa [Φ, Function.comp_def] using
      complexPhaseRV_ae_eq_some_rawPhase P Z
        (ae_ne_zero_of_hasLaw_unitDisc P Z hZlaw)

/-- Strict radius CDF, including the explicit `r = 0` and `r = 1` branches. -/
theorem unitDisc_strict_radius_cdf
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℂ)
    (hZmeas : Measurable Z)
    (hZlaw : ProbabilityTheory.HasLaw Z unitDiscLaw P) :
    ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      P {ω | complexRadius (Z ω) < r} =
        ENNReal.ofReal (r ^ 2) := by
  intro r hr0 hr1
  have hset_meas :
      MeasurableSet {z : ℂ | complexRadius z < r} := by
    change MeasurableSet (complexRadialSubdisc r)
    rw [complexRadialSubdisc_eq_ball]
    exact measurableSet_ball
  calc
    P {ω | complexRadius (Z ω) < r} =
        unitDiscLaw {z : ℂ | complexRadius z < r} :=
      hZlaw.measure_eq hset_meas
    _ = unitDiscLaw (Metric.ball (0 : ℂ) r) := by
      rw [← complexRadialSubdisc_eq_ball]
      rfl
    _ = ENNReal.ofReal (r ^ 2) := by
      by_cases hzero : r = 0
      · subst r
        simpa using unitDiscLaw_ball_zero
      by_cases hone : r = 1
      · subst r
        simpa using unitDiscLaw_ball_one
      exact unitDiscLaw_ball r hr0 hr1

/--
Example 4.4.1: a measurable random variable with the normalized unit-disc law
has a measurable Haar-uniform phase representative and strict radius CDF
`r²` on `[0,1]`.
-/
theorem ex_4_4_1
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℂ)
    (hZmeas : Measurable Z)
    (hZlaw : ProbabilityTheory.HasLaw Z unitDiscLaw P) :
    (∃ Φ : Ω → Real.Angle,
      Measurable Φ ∧
      ProbabilityTheory.HasLaw Φ
        (AddCircle.haarAddCircle : Measure Real.Angle) P ∧
      complexPhaseRV Z =ᵐ[P] fun ω => some (Φ ω)) ∧
    (∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      P {ω | complexRadius (Z ω) < r} =
        ENNReal.ofReal (r ^ 2)) := by
  exact ⟨exists_uniform_unitDisc_phase P Z hZmeas hZlaw,
    unitDisc_strict_radius_cdf P Z hZmeas hZlaw⟩

/-- Compatibility alias with the same source-facing type. -/
theorem exercise_4_4_1
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℂ)
    (hZmeas : Measurable Z)
    (hZlaw : ProbabilityTheory.HasLaw Z unitDiscLaw P) :
    (∃ Φ : Ω → Real.Angle,
      Measurable Φ ∧
      ProbabilityTheory.HasLaw Φ
        (AddCircle.haarAddCircle : Measure Real.Angle) P ∧
      complexPhaseRV Z =ᵐ[P] fun ω => some (Φ ω)) ∧
    (∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      P {ω | complexRadius (Z ω) < r} =
        ENNReal.ofReal (r ^ 2)) :=
  ex_4_4_1 P Z hZmeas hZlaw

/-! Compatibility names retained from the preceding public exercise file. -/

/-- Piecewise radius CDF as a real-valued display function. -/
noncomputable def unitDiscRadiusCdf (r : ℝ) : ℝ :=
  if r < 0 then 0 else if r ≤ 1 then r ^ 2 else 1

/-- Piecewise angle CDF as a real-valued display function. -/
noncomputable def unitDiscAngleCdf (θ : ℝ) : ℝ :=
  if θ < 0 then 0
  else if θ ≤ 2 * Real.pi then θ / (2 * Real.pi)
  else 1

theorem unitDiscRadiusCdf_on_unit_interval
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    unitDiscRadiusCdf r = r ^ 2 := by
  have hr_nonneg : ¬r < 0 := not_lt.mpr hr.1
  have hr_le_one : r ≤ 1 := hr.2
  simp [unitDiscRadiusCdf, hr_nonneg, hr_le_one]

theorem unitDiscAngleCdf_on_support
    {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    unitDiscAngleCdf θ = θ / (2 * Real.pi) := by
  have hθ_nonneg : ¬θ < 0 := not_lt.mpr hθ.1
  have hθ_le : θ ≤ 2 * Real.pi := hθ.2
  simp [unitDiscAngleCdf, hθ_nonneg, hθ_le]

theorem ex_4_4_1_cdf_formulas :
    (∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 →
      unitDiscRadiusCdf r = r ^ 2) ∧
    (∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) →
      unitDiscAngleCdf θ = θ / (2 * Real.pi)) := by
  exact ⟨fun _ hr => unitDiscRadiusCdf_on_unit_interval hr,
    fun _ hθ => unitDiscAngleCdf_on_support hθ⟩
