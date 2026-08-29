/-
TASK ID: thm_14_2
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter14-weak-convergence
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_10_4
import ToyApollo.Output.def_14_2
import ToyApollo.Output.thm_10_8
import ToyApollo.Output.thm_10_11
import ToyApollo.Output.thm_14_1

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set ProbabilityTheory Function
open scoped Topology

noncomputable section

def thm_14_2_randomVariableCdf
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : AEMeasurable X μ) :
    ℝ → ℝ :=
  measureCdf
    (⟨Measure.map X μ, Measure.isProbabilityMeasure_map hX⟩ :
      ProbabilityMeasure ℝ)

def thm_14_2_cdfConvergence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  RandomVariablesConvergeInDistribution (fun _ : ℕ => μ) Xseq μ X

def thm_14_2_weakConvergence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X) : Prop :=
  def_14_2 μ Xseq X hXseq hX

theorem thm_14_2_cdfConvergence_eq_def_10_4
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ) :
    thm_14_2_cdfConvergence μ Xseq X =
      RandomVariablesConvergeInDistribution (fun _ : ℕ => μ) Xseq μ X := by
  rfl

theorem thm_14_2_weak_iff_expectations
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Xseq : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X) :
    thm_14_2_weakConvergence μ Xseq X hXseq hX ↔
      ∀ h : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun n : ℕ => ∫ ω, h (Xseq n ω) ∂μ) atTop
          (𝓝 (∫ ω, h (X ω) ∂μ)) := by
  exact def_14_2_iff_expectations μ hXseq hX

def thm_14_2_ramp (a ε : ℝ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : ℝ =>
      (Set.projIcc (0 : ℝ) 1 (by norm_num) ((a - x) / ε) : ℝ))
    (by fun_prop)
    1
    (by
      intro x
      have hx :=
        (Set.projIcc (0 : ℝ) 1 (by norm_num) ((a - x) / ε)).property
      rw [Real.norm_eq_abs]
      exact abs_le.2 ⟨by linarith [hx.1], hx.2⟩)

theorem thm_14_2_ramp_nonneg (a ε x : ℝ) :
    0 ≤ thm_14_2_ramp a ε x :=
  (Set.projIcc (0 : ℝ) 1 (by norm_num) ((a - x) / ε)).property.1

theorem thm_14_2_ramp_le_one (a ε x : ℝ) :
    thm_14_2_ramp a ε x ≤ 1 :=
  (Set.projIcc (0 : ℝ) 1 (by norm_num) ((a - x) / ε)).property.2

theorem thm_14_2_ramp_eq_one {a ε x : ℝ} (hε : 0 < ε)
    (hx : x ≤ a - ε) : thm_14_2_ramp a ε x = 1 := by
  have hquot : 1 ≤ (a - x) / ε := (le_div_iff₀ hε).2 (by linarith)
  change
    (↑(Set.projIcc (0 : ℝ) 1 (by norm_num) ((a - x) / ε)) : ℝ) = 1
  rw [Set.projIcc_of_right_le (a := (0 : ℝ)) (b := 1)
    (by norm_num) hquot]

theorem thm_14_2_ramp_eq_zero {a ε x : ℝ} (hε : 0 < ε)
    (hx : a ≤ x) : thm_14_2_ramp a ε x = 0 := by
  have hquot : (a - x) / ε ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hx) hε.le
  change
    (↑(Set.projIcc (0 : ℝ) 1 (by norm_num) ((a - x) / ε)) : ℝ) = 0
  rw [Set.projIcc_of_le_left (a := (0 : ℝ)) (b := 1)
    (by norm_num) hquot]

theorem thm_14_2_indicator_Iic_sub_le_ramp {a ε : ℝ} (hε : 0 < ε)
    (x : ℝ) :
    (Set.Iic (a - ε)).indicator (1 : ℝ → ℝ) x ≤
      thm_14_2_ramp a ε x := by
  by_cases hx : x ∈ Set.Iic (a - ε)
  · rw [Set.indicator_of_mem hx, thm_14_2_ramp_eq_one hε hx]
    exact le_rfl
  · rw [Set.indicator_of_notMem hx]
    exact thm_14_2_ramp_nonneg a ε x

theorem thm_14_2_ramp_le_indicator_Iic {a ε : ℝ} (hε : 0 < ε)
    (x : ℝ) :
    thm_14_2_ramp a ε x ≤
      (Set.Iic a).indicator (1 : ℝ → ℝ) x := by
  by_cases hx : x ∈ Set.Iic a
  · rw [Set.indicator_of_mem hx]
    exact thm_14_2_ramp_le_one a ε x
  · rw [Set.indicator_of_notMem hx,
      thm_14_2_ramp_eq_zero hε (le_of_lt (lt_of_not_ge hx))]

theorem thm_14_2_cdf_sub_le_integral_ramp
    (P : ProbabilityMeasure ℝ) {a ε : ℝ} (hε : 0 < ε) :
    measureCdf P (a - ε) ≤
      ∫ x, thm_14_2_ramp a ε x ∂(P : Measure ℝ) := by
  rw [measureCdf, ← integral_indicator_one
    (μ := (P : Measure ℝ)) measurableSet_Iic]
  exact integral_mono
    ((integrable_const (1 : ℝ)).indicator measurableSet_Iic)
    ((thm_14_2_ramp a ε).integrable (P : Measure ℝ))
    (thm_14_2_indicator_Iic_sub_le_ramp hε)

theorem thm_14_2_integral_ramp_le_cdf
    (P : ProbabilityMeasure ℝ) {a ε : ℝ} (hε : 0 < ε) :
    (∫ x, thm_14_2_ramp a ε x ∂(P : Measure ℝ)) ≤
      measureCdf P a := by
  rw [measureCdf, ← integral_indicator_one
    (μ := (P : Measure ℝ)) measurableSet_Iic]
  exact integral_mono
    ((thm_14_2_ramp a ε).integrable (P : Measure ℝ))
    ((integrable_const (1 : ℝ)).indicator measurableSet_Iic)
    (thm_14_2_ramp_le_indicator_Iic hε)

theorem thm_14_2_atom_zero_of_cdf_continuous
    (μ : ProbabilityMeasure ℝ) {x : ℝ}
    (hcont : ContinuousAt (fun y : ℝ => measureCdf μ y) x) :
    (μ : Measure ℝ) {x} = 0 :=
  measure_singleton_eq_zero_of_measureCdf_continuousAt μ hcont

theorem thm_14_2_weak_to_cdfConvergence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Xseq : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X)
    (hWeak : thm_14_2_weakConvergence μ Xseq X hXseq hX) :
    thm_14_2_cdfConvergence μ Xseq X := by
  let Pseq : ℕ → ProbabilityMeasure ℝ := def_14_1_laws μ Xseq hXseq
  let P : ProbabilityMeasure ℝ := def_14_1_law μ X hX
  have hLawWeak : def_14_1 Pseq P := by
    simpa [Pseq, P, thm_14_2_weakConvergence, def_14_2,
      def_14_1, def_14_1_weakConvergence,
      def_14_1_randomVariableWeakConvergence, def_14_1_laws, def_14_1_law] using hWeak
  have hCdf : CdfConvergesInDistribution Pseq P := by
    intro a ha
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro b hb
      have hnear : {z : ℝ | b < measureCdf P z} ∈ 𝓝 a :=
        ha.eventually (eventually_gt_nhds hb)
      rcases mem_nhds_iff_exists_Ioo_subset.mp hnear with ⟨l, u, hau, hlu⟩
      let x : ℝ := (l + a) / 2
      have hxa : x < a := by
        dsimp [x]
        linarith [hau.1]
      have hxmem : x ∈ Set.Ioo l u := by
        constructor <;> dsimp [x] <;> linarith [hau.1, hau.2]
      have hFx : b < measureCdf P x := hlu hxmem
      let ε : ℝ := a - x
      have hε : 0 < ε := by
        dsimp [ε]
        linarith
      have hLower :
          measureCdf P x ≤
            ∫ z, thm_14_2_ramp a ε z ∂(P : Measure ℝ) := by
        simpa [ε] using
          thm_14_2_cdf_sub_le_integral_ramp P
            (a := a) (ε := ε) hε
      have hInt :
          b < ∫ z, thm_14_2_ramp a ε z ∂(P : Measure ℝ) :=
        hFx.trans_le hLower
      have hlim := hLawWeak (thm_14_2_ramp a ε)
      have hevent := hlim.eventually (eventually_gt_nhds hInt)
      filter_upwards [hevent] with n hn
      exact hn.trans_le (thm_14_2_integral_ramp_le_cdf (Pseq n) hε)
    · intro b hb
      have hnear : {z : ℝ | measureCdf P z < b} ∈ 𝓝 a :=
        ha.eventually (eventually_lt_nhds hb)
      rcases mem_nhds_iff_exists_Ioo_subset.mp hnear with ⟨l, u, hau, hlu⟩
      let y : ℝ := (a + u) / 2
      have hay : a < y := by
        dsimp [y]
        linarith [hau.2]
      have hymem : y ∈ Set.Ioo l u := by
        constructor <;> dsimp [y] <;> linarith [hau.1, hau.2]
      have hFy : measureCdf P y < b := hlu hymem
      let ε : ℝ := y - a
      have hε : 0 < ε := by
        dsimp [ε]
        linarith
      have hInt :
          (∫ z, thm_14_2_ramp y ε z ∂(P : Measure ℝ)) < b :=
        (thm_14_2_integral_ramp_le_cdf P hε).trans_lt hFy
      have hlim := hLawWeak (thm_14_2_ramp y ε)
      have hevent := hlim.eventually (eventually_lt_nhds hInt)
      filter_upwards [hevent] with n hn
      have hUpper :
          measureCdf (Pseq n) a ≤
            ∫ z, thm_14_2_ramp y ε z ∂(Pseq n : Measure ℝ) := by
        simpa [ε] using
          thm_14_2_cdf_sub_le_integral_ramp (Pseq n)
            (a := y) (ε := ε) hε
      exact hUpper.trans_lt hn
  have hTend : MeasuresConvergeInDistribution Pseq P :=
    (measuresConvergeInDistribution_iff_cdf Pseq P).2 hCdf
  refine ⟨fun n => (hXseq n).aemeasurable, hX.aemeasurable, ?_⟩
  change Tendsto Pseq atTop (𝓝 P)
  exact hTend

theorem thm_14_2_skorokhod_representation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Xseq : ℕ → Ω → ℝ} {X : Ω → ℝ}
    {hXseq : ∀ n : ℕ, Measurable (Xseq n)} {hX : Measurable X}
    (hDist : thm_14_2_cdfConvergence μ Xseq X) :
    SkorokhodRepresentation μ Xseq X := by
  exact thm_10_8 μ Xseq X hDist
    (fun n : ℕ => (hXseq n).aemeasurable) hX.aemeasurable

private theorem thm_14_2_scalar_continuous_mapping_almost_sure
    {Ω' : Type*} [MeasurableSpace Ω'] (ν : Measure Ω')
    [IsProbabilityMeasure ν]
    (Yn : ℕ → Ω' → ℝ) (Y : Ω' → ℝ)
    (h : BoundedContinuousFunction ℝ ℝ)
    (hAS : ConvergesAlmostSurely ν Yn Y) :
    ConvergesAlmostSurely ν
      (fun n ω => h (Yn n ω)) (fun ω => h (Y ω)) := by
  let Vn : ℕ → Ω' → Fin 1 → ℝ := fun n ω _ => Yn n ω
  let V : Ω' → Fin 1 → ℝ := fun ω _ => Y ω
  let f : (Fin 1 → ℝ) → (Fin 1 → ℝ) :=
    fun v _ => h (v 0)
  obtain ⟨hYn, hY, E, hEmeas, hEone, hEtend⟩ :=
    (convergesAlmostSurely_iff_exists_measure_one_event ν Yn Y).1 hAS
  have hVecAS : VectorConvergesAlmostSurely ν Vn V := by
    refine ⟨E, hEmeas, hEone, ?_⟩
    intro ω hω
    refine tendsto_pi_nhds.2 ?_
    intro i
    simpa [Vn, V] using hEtend ω hω
  have hf : Continuous f := by
    dsimp [f]
    exact continuous_pi fun _ =>
      h.continuous.comp (continuous_apply (0 : Fin 1))
  obtain ⟨E', hE'meas, hE'one, hE'tend⟩ :=
    thm_10_11_almost_sure ν Vn V f Set.univ
      (by simp) (by simp)
      (fun v _ => hf.continuousAt) hVecAS
  refine
    (convergesAlmostSurely_iff_exists_measure_one_event ν
      (fun n ω => h (Yn n ω)) (fun ω => h (Y ω))).2 ?_
  refine ⟨?_, ?_, E', hE'meas, hE'one, ?_⟩
  · intro n
    simpa only [Function.comp_def] using
      (h.continuous.measurable.comp_aemeasurable
        (hYn n).aemeasurable).aestronglyMeasurable
  · simpa only [Function.comp_def] using
      (h.continuous.measurable.comp_aemeasurable
        hY.aemeasurable).aestronglyMeasurable
  · intro ω hω
    have hcoord :=
      (tendsto_pi_nhds.1 (hE'tend ω hω)) (0 : Fin 1)
    simpa [Vn, V, f] using hcoord

theorem thm_14_2_distribution_to_weak
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    {Xseq : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (hXseq : ∀ n : ℕ, Measurable (Xseq n))
    (hX : Measurable X)
    (hDist : thm_14_2_cdfConvergence μ Xseq X) :
    thm_14_2_weakConvergence μ Xseq X hXseq hX := by
  obtain ⟨ν, hν, Yn, Y, hAS, hYnLaw, hYLaw⟩ :=
    thm_14_2_skorokhod_representation
      (μ := μ) (Xseq := Xseq) (X := X)
      (hXseq := hXseq) (hX := hX) hDist
  letI : IsProbabilityMeasure ν := hν

  -- The representation record stores laws rather than witness measurability;
  -- recover it because a nonmeasurable map would have zero pushforward.
  have hYn_ae (n : ℕ) : AEMeasurable (Yn n) ν := by
    apply AEMeasurable.of_map_ne_zero
    rw [hYnLaw n]
    exact
      (Measure.map_ne_zero_iff (hXseq n).aemeasurable).2
        (IsProbabilityMeasure.ne_zero μ)
  have hY_ae : AEMeasurable Y ν := by
    apply AEMeasurable.of_map_ne_zero
    rw [hYLaw]
    exact
      (Measure.map_ne_zero_iff hX.aemeasurable).2
        (IsProbabilityMeasure.ne_zero μ)

  have hCoupledAS : ConvergesAlmostSurely ν Yn Y :=
    ⟨fun n => (hYn_ae n).aestronglyMeasurable,
      hY_ae.aestronglyMeasurable, hAS⟩

  change def_14_2 μ Xseq X hXseq hX
  refine (def_14_2_iff_expectations μ hXseq hX).2 ?_
  intro h

  have hMappedAS :
      ConvergesAlmostSurely ν
        (fun n ω => h (Yn n ω)) (fun ω => h (Y ω)) :=
    thm_14_2_scalar_continuous_mapping_almost_sure
      ν Yn Y h hCoupledAS

  have hDCT :
      Tendsto (fun n : ℕ => ∫ ω, h (Yn n ω) ∂ν) atTop
        (𝓝 (∫ ω, h (Y ω) ∂ν)) := by
    exact MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := ν)
      (fun _ : ℝ => ‖h‖)
      hMappedAS.1
      (integrable_const (μ := ν) ‖h‖)
      (fun n => ae_of_all ν fun ω =>
        h.norm_coe_le_norm (Yn n ω))
      hMappedAS.2.2

  have hYnIntegral (n : ℕ) :
      (∫ ω, h (Yn n ω) ∂ν) =
        ∫ ω, h (Xseq n ω) ∂μ := by
    calc
      (∫ ω, h (Yn n ω) ∂ν) =
          ∫ x, h x ∂Measure.map (Yn n) ν := by
        exact
          (MeasureTheory.integral_map
            (hYn_ae n) h.continuous.aestronglyMeasurable).symm
      _ = ∫ x, h x ∂Measure.map (Xseq n) μ := by
        rw [hYnLaw n]
      _ = ∫ ω, h (Xseq n ω) ∂μ := by
        exact MeasureTheory.integral_map
          (hXseq n).aemeasurable
          h.continuous.aestronglyMeasurable

  have hYIntegral :
      (∫ ω, h (Y ω) ∂ν) =
        ∫ ω, h (X ω) ∂μ := by
    calc
      (∫ ω, h (Y ω) ∂ν) =
          ∫ x, h x ∂Measure.map Y ν := by
        exact
          (MeasureTheory.integral_map
            hY_ae h.continuous.aestronglyMeasurable).symm
      _ = ∫ x, h x ∂Measure.map X μ := by
        rw [hYLaw]
      _ = ∫ ω, h (X ω) ∂μ := by
        exact MeasureTheory.integral_map
          hX.aemeasurable h.continuous.aestronglyMeasurable

  have hseq :
      (fun n : ℕ => ∫ ω, h (Yn n ω) ∂ν) =
        fun n : ℕ => ∫ ω, h (Xseq n ω) ∂μ :=
    funext hYnIntegral
  rw [hseq, hYIntegral] at hDCT
  exact hDCT

theorem thm_14_2
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X) :
    thm_14_2_weakConvergence μ Xseq X hXseq hX ↔
      thm_14_2_cdfConvergence μ Xseq X := by
  constructor
  · intro hWeak
    exact thm_14_2_weak_to_cdfConvergence μ hXseq hX hWeak
  · intro hDist
    exact thm_14_2_distribution_to_weak μ hXseq hX hDist

theorem thm_14_2_levy_condition_one_to_two
    {P : ℕ → ProbabilityMeasure ℝ} {φ : ℝ → ℂ}
    (hφ : thm_14_1_pointwiseCharFunConvergence P φ) :
    thm_14_1_weakLimit P → thm_14_1_limitIsCharacteristic φ :=
  (thm_14_1_weak_iff_characteristic hφ).mp
