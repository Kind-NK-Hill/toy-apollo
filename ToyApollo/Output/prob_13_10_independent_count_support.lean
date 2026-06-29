/-
TASK ID: prob_13_10_independent_count_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.prob_13_10_stopped_sum_support

open MeasureTheory Filter
open scoped BigOperators ProbabilityTheory Topology

noncomputable section

def prob_13_10_waldIdentity (stoppedSum mean expectedT : ℝ) : Prop :=
  stoppedSum = mean * expectedT

def prob_13_10_countMass {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : Ω → ℕ) (m : ℕ) : ℝ :=
  (P {ω | T ω = m}).toReal

theorem prob_13_10_countMass_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : Ω → ℕ) (m : ℕ) :
    0 ≤ prob_13_10_countMass P T m :=
  ENNReal.toReal_nonneg

theorem prob_13_10_fixed_count_iid_sum_expectation {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (X : ℕ → Ω → ℝ) (μ : ℝ)
    (hIntegrable : ∀ k : ℕ, Integrable (X k) P)
    (hMean : ∀ k : ℕ, ∫ ω, X k ω ∂P = μ) (m : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range m, X (k + 1) ω) ∂P =
      (m : ℝ) * μ := by
  rw [integral_finset_sum]
  · calc
      (∑ k ∈ Finset.range m, ∫ ω, X (k + 1) ω ∂P)
          = ∑ k ∈ Finset.range m, μ := by
            refine Finset.sum_congr rfl ?_
            intro k _hk
            exact hMean (k + 1)
      _ = (m : ℝ) * μ := by
            simp [Finset.sum_const, nsmul_eq_mul]
  · intro k _hk
    exact hIntegrable (k + 1)

def prob_13_10_tailMass {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : Ω → ℕ) (n : ℕ) : ℝ :=
  (P {ω | n ≤ T ω}).toReal

theorem prob_13_10_tail_mass_summable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Ω → ℕ)
    (hTIntegrable : Integrable (fun ω => (T ω : ℝ)) P) :
    Summable (fun k : ℕ => prob_13_10_tailMass P T (k + 1)) := by
  letI : MeasureSpace Ω := ⟨P⟩
  have hnonneg : 0 ≤ fun ω => (T ω : ℝ) := by
    intro ω
    positivity
  have hENNRlt :
      (∑' j : ℕ, P {ω | (T ω : ℝ) ∈ Set.Ioi (j : ℝ)}) < ⊤ := by
    simpa using ProbabilityTheory.tsum_prob_mem_Ioi_lt_top
      (Ω := Ω) (X := fun ω => (T ω : ℝ)) hTIntegrable hnonneg
  let fNN : ℕ → NNReal :=
    fun k => (P {ω | (T ω : ℝ) ∈ Set.Ioi (k : ℝ)}).toNNReal
  have hENNReq :
      (∑' k : ℕ, (fNN k : ENNReal)) =
        ∑' k : ℕ, P {ω | (T ω : ℝ) ∈ Set.Ioi (k : ℝ)} := by
    apply tsum_congr
    intro k
    dsimp [fNN]
    exact ENNReal.coe_toNNReal (measure_ne_top P _)
  have hfNN : Summable fNN := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable]
    rw [hENNReq]
    exact ne_top_of_lt hENNRlt
  have hfReal : Summable (fun k : ℕ => (fNN k : ℝ)) := by
    exact (NNReal.summable_coe).2 hfNN
  refine hfReal.congr ?_
  intro k
  dsimp [fNN, prob_13_10_tailMass]
  have hset :
      {ω | (T ω : ℝ) ∈ Set.Ioi (k : ℝ)} =
        {ω | k + 1 ≤ T ω} := by
    apply Set.ext
    intro ω
    simp
  rw [hset]
  exact ENNReal.coe_toNNReal_eq_toReal _

theorem prob_13_10_integral_nat_count_eq_sum_countMass {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Ω → ℕ)
    (hTMeas : Measurable T)
    (hTIntegrable : Integrable (fun ω => (T ω : ℝ)) P) :
    ∫ ω, (T ω : ℝ) ∂P =
      ∑' m : ℕ, (m : ℝ) * prob_13_10_countMass P T m :=
by
  let μT : Measure ℕ := Measure.map T P
  haveI : IsProbabilityMeasure μT :=
    Measure.isProbabilityMeasure_map hTMeas.aemeasurable
  have hMapInt : Integrable (fun n : ℕ => (n : ℝ)) μT := by
    dsimp [μT]
    exact (integrable_map_measure
      (by
        fun_prop :
          AEStronglyMeasurable (fun n : ℕ => (n : ℝ)) (Measure.map T P))
      hTMeas.aemeasurable).2 hTIntegrable
  have hMapIntegral :
      ∫ n : ℕ, (n : ℝ) ∂μT = ∫ ω, (T ω : ℝ) ∂P := by
    dsimp [μT]
    exact integral_map hTMeas.aemeasurable
      (by
        fun_prop :
          AEStronglyMeasurable (fun n : ℕ => (n : ℝ)) (Measure.map T P))
  have hPMF :
      ∫ n : ℕ, (n : ℝ) ∂μT =
        ∑' n : ℕ, (μT.toPMF n).toReal • (n : ℝ) := by
    have hraw :=
      PMF.integral_eq_tsum μT.toPMF (fun n : ℕ => (n : ℝ)) (by
        simpa [Measure.toPMF_toMeasure] using hMapInt)
    simpa [Measure.toPMF_toMeasure] using hraw
  rw [← hMapIntegral]
  trans ∑' n : ℕ, (μT.toPMF n).toReal • (n : ℝ)
  · exact hPMF
  · apply tsum_congr
    intro n
    have hsingle : μT.toPMF n = μT {n} :=
      Measure.toPMF_apply μT n
    have hmap_single : μT {n} = P {ω | T ω = n} := by
      dsimp [μT]
      rw [Measure.map_apply hTMeas (measurableSet_singleton n)]
      rfl
    rw [hsingle, hmap_single]
    simp [prob_13_10_countMass, smul_eq_mul, mul_comm]

theorem prob_13_10_count_mass_summable {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Ω → ℕ)
    (hTMeas : Measurable T)
    (hTIntegrable : Integrable (fun ω => (T ω : ℝ)) P) :
    Summable (fun m : ℕ => (m : ℝ) * prob_13_10_countMass P T m) := by
  let μT : Measure ℕ := Measure.map T P
  have hMapInt : Integrable (fun n : ℕ => (n : ℝ)) μT := by
    dsimp [μT]
    exact (integrable_map_measure
      (by
        fun_prop :
          AEStronglyMeasurable (fun n : ℕ => (n : ℝ)) (Measure.map T P))
      hTMeas.aemeasurable).2 hTIntegrable
  rw [← Measure.sum_smul_dirac μT] at hMapInt
  have hs := hMapInt.summable_integral
  refine hs.congr ?_
  intro m
  dsimp [μT]
  rw [integral_smul_measure, integral_dirac]
  rw [Measure.map_apply hTMeas (measurableSet_singleton m)]
  have hpre : T ⁻¹' ({m} : Set ℕ) = {ω | T ω = m} := by
    ext ω
    simp
  rw [hpre]
  simp [prob_13_10_countMass,
    abs_of_nonneg (by positivity : 0 ≤ (m : ℝ)), mul_comm]

theorem prob_13_10_independent_count_conditional_expectation {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (X : ℕ → Ω → ℝ) (T : Ω → ℕ) (μ : ℝ)
    (hEventMeas : ∀ m : ℕ, MeasurableSet {ω | T ω = m})
    (hFixedIntegrable :
      ∀ m : ℕ, Integrable
        (fun ω => ∑ k ∈ Finset.range m, X (k + 1) ω) P)
    (hFixedMean :
      ∀ m : ℕ,
        ∫ ω, (∑ k ∈ Finset.range m, X (k + 1) ω) ∂P =
          (m : ℝ) * μ)
    (hIndependent :
      ∀ m : ℕ,
        ProbabilityTheory.IndepFun
          (fun ω => Set.indicator {ω | T ω = m} (fun _ => (1 : ℝ)) ω)
          (fun ω => ∑ k ∈ Finset.range m, X (k + 1) ω)
          P) :
    ∀ m : ℕ,
      ∫ ω,
        Set.indicator {ω | T ω = m}
          (fun ω => ∑ k ∈ Finset.range (T ω), X (k + 1) ω) ω ∂P =
        ((m : ℝ) * μ) * prob_13_10_countMass P T m := by
  intro m
  let E : Set Ω := {ω | T ω = m}
  have hPoint :
      (fun ω =>
        Set.indicator E
          (fun ω => ∑ k ∈ Finset.range (T ω), X (k + 1) ω) ω)
        =ᵐ[P]
      (fun ω =>
        (Set.indicator E (fun _ => (1 : ℝ)) ω) *
          (∑ k ∈ Finset.range m, X (k + 1) ω)) := by
    filter_upwards with ω
    by_cases hω : ω ∈ E
    · have hTω : T ω = m := hω
      simp [E, hω, hTω]
    · simp [E, hω]
  calc
    ∫ ω,
        Set.indicator E
          (fun ω => ∑ k ∈ Finset.range (T ω), X (k + 1) ω) ω ∂P
        = ∫ ω,
            (Set.indicator E (fun _ => (1 : ℝ)) ω) *
              (∑ k ∈ Finset.range m, X (k + 1) ω) ∂P := by
          exact integral_congr_ae hPoint
    _ = (∫ ω, Set.indicator E (fun _ => (1 : ℝ)) ω ∂P) *
          ∫ ω, (∑ k ∈ Finset.range m, X (k + 1) ω) ∂P := by
          have hIndSM :
              AEStronglyMeasurable
                (fun ω => Set.indicator E (fun _ => (1 : ℝ)) ω) P := by
            exact (measurable_const.indicator (hEventMeas m)).aestronglyMeasurable
          simpa [E] using
            (hIndependent m).integral_fun_mul_eq_mul_integral
              hIndSM (hFixedIntegrable m).aestronglyMeasurable
    _ = prob_13_10_countMass P T m * ((m : ℝ) * μ) := by
          have hMass :
              ∫ ω, Set.indicator E (fun _ => (1 : ℝ)) ω ∂P =
                prob_13_10_countMass P T m := by
            simpa [prob_13_10_countMass, E, Measure.real_def] using
              (integral_indicator_one (μ := P) (s := E) (hEventMeas m))
          rw [hFixedMean m]
          rw [hMass]
    _ = ((m : ℝ) * μ) * prob_13_10_countMass P T m := by
          ring

theorem prob_13_10_abs_fiber_bound_from_independence {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (X : ℕ → Ω → ℝ) (T : Ω → ℕ) (A : ℝ)
    (hEventMeas : ∀ m : ℕ, MeasurableSet {ω | T ω = m})
    (hXIntegrable : ∀ k : ℕ, Integrable (X k) P)
    (hAbsMeanBound : ∀ k : ℕ, ∫ ω, |X k ω| ∂P ≤ A)
    (hAbsIndependent :
      ∀ m k : ℕ,
        ProbabilityTheory.IndepFun
          (fun ω => Set.indicator {ω | T ω = m} (fun _ => (1 : ℝ)) ω)
          (fun ω => |X (k + 1) ω|)
          P) :
    ∀ m k : ℕ, k < m →
      ∫ ω in {ω | T ω = m}, |X (k + 1) ω| ∂P ≤
        A * prob_13_10_countMass P T m := by
  intro m k _hk
  let E : Set Ω := {ω | T ω = m}
  have hIndSM :
      AEStronglyMeasurable
        (fun ω => Set.indicator E (fun _ => (1 : ℝ)) ω) P := by
    exact (measurable_const.indicator (hEventMeas m)).aestronglyMeasurable
  have hPoint :
      (fun ω =>
        Set.indicator E (fun _ => (1 : ℝ)) ω * |X (k + 1) ω|) =
        Set.indicator E (fun ω => |X (k + 1) ω|) := by
    funext ω
    by_cases hω : ω ∈ E <;> simp [E, hω]
  calc
    ∫ ω in E, |X (k + 1) ω| ∂P
        = ∫ ω, Set.indicator E (fun ω => |X (k + 1) ω|) ω ∂P := by
          rw [integral_indicator (hEventMeas m)]
    _ = ∫ ω,
          Set.indicator E (fun _ => (1 : ℝ)) ω * |X (k + 1) ω| ∂P := by
          rw [← hPoint]
    _ = (∫ ω, Set.indicator E (fun _ => (1 : ℝ)) ω ∂P) *
          ∫ ω, |X (k + 1) ω| ∂P := by
          simpa [E] using
            (hAbsIndependent m k).integral_fun_mul_eq_mul_integral
              hIndSM (hXIntegrable (k + 1)).norm.aestronglyMeasurable
    _ = prob_13_10_countMass P T m * ∫ ω, |X (k + 1) ω| ∂P := by
          have hMass :
              ∫ ω, Set.indicator E (fun _ => (1 : ℝ)) ω ∂P =
                prob_13_10_countMass P T m := by
            simpa [prob_13_10_countMass, E, Measure.real_def] using
              (integral_indicator_one (μ := P) (s := E) (hEventMeas m))
          rw [hMass]
    _ ≤ prob_13_10_countMass P T m * A := by
          exact mul_le_mul_of_nonneg_left (hAbsMeanBound (k + 1))
            (prob_13_10_countMass_nonneg P T m)
    _ = A * prob_13_10_countMass P T m := by
          ring

theorem prob_13_10_fiber_norm_bound_from_abs_prefix {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (T : Ω → ℕ) (A : ℝ)
    (hTMeas : Measurable T)
    (hXIntegrable : ∀ k : ℕ, Integrable (X k) P)
    (hAbsFiberBound :
      ∀ m k : ℕ, k < m →
        ∫ ω in {ω | T ω = m}, |X (k + 1) ω| ∂P ≤
          A * prob_13_10_countMass P T m) :
    ∀ m : ℕ,
      ∫ ω in {ω | T ω = m}, ‖prob_13_10_stoppedSum X T ω‖ ∂P ≤
        A * ((m : ℝ) * prob_13_10_countMass P T m) := by
  intro m
  let s : Set Ω := {ω | T ω = m}
  have hs : MeasurableSet s := by
    exact hTMeas (measurableSet_singleton m)
  have hLeftInt :
      IntegrableOn (fun ω => ‖prob_13_10_stoppedSum X T ω‖) s P := by
    have hFixedIntegrable :
        Integrable (fun ω => ∑ k ∈ Finset.range m, X (k + 1) ω) P := by
      exact integrable_finset_sum (Finset.range m)
        (fun k _hk => hXIntegrable (k + 1))
    have hStoppedOn : IntegrableOn (prob_13_10_stoppedSum X T) s P := by
      refine hFixedIntegrable.integrableOn.congr_fun ?_ hs
      intro ω hω
      have hTω : T ω = m := hω
      simp [prob_13_10_stoppedSum, chapter13_stoppedNatSum, hTω]
    simpa using hStoppedOn.norm
  have hRightInt :
      IntegrableOn
        (fun ω => ∑ k ∈ Finset.range m, |X (k + 1) ω|) s P := by
    have hEach :
        ∀ k ∈ Finset.range m,
          IntegrableOn (fun ω => |X (k + 1) ω|) s P := by
      intro k _hk
      exact (hXIntegrable (k + 1)).norm.integrableOn
    exact integrable_finset_sum (Finset.range m) hEach
  have hPoint : ∀ ω ∈ s,
      ‖prob_13_10_stoppedSum X T ω‖ ≤
        ∑ k ∈ Finset.range m, |X (k + 1) ω| := by
    intro ω hω
    have hTω : T ω = m := hω
    calc
      ‖prob_13_10_stoppedSum X T ω‖
          = |∑ k ∈ Finset.range m, X (k + 1) ω| := by
            simp [prob_13_10_stoppedSum, chapter13_stoppedNatSum, hTω, Real.norm_eq_abs]
      _ ≤ ∑ k ∈ Finset.range m, |X (k + 1) ω| := by
            exact Finset.abs_sum_le_sum_abs _ _
  have hMono :
      ∫ ω in s, ‖prob_13_10_stoppedSum X T ω‖ ∂P ≤
        ∫ ω in s, (∑ k ∈ Finset.range m, |X (k + 1) ω|) ∂P := by
    exact setIntegral_mono_on hLeftInt hRightInt hs hPoint
  have hSumIntegral :
      ∫ ω in s, (∑ k ∈ Finset.range m, |X (k + 1) ω|) ∂P =
        ∑ k ∈ Finset.range m, ∫ ω in s, |X (k + 1) ω| ∂P := by
    rw [integral_finset_sum]
    intro k _hk
    exact (hXIntegrable (k + 1)).norm.integrableOn
  calc
    ∫ ω in s, ‖prob_13_10_stoppedSum X T ω‖ ∂P
        ≤ ∫ ω in s, (∑ k ∈ Finset.range m, |X (k + 1) ω|) ∂P := hMono
    _ = ∑ k ∈ Finset.range m, ∫ ω in s, |X (k + 1) ω| ∂P := hSumIntegral
    _ ≤ ∑ k ∈ Finset.range m, A * prob_13_10_countMass P T m := by
          exact Finset.sum_le_sum
            (fun k hk => hAbsFiberBound m k (Finset.mem_range.mp hk))
    _ = A * ((m : ℝ) * prob_13_10_countMass P T m) := by
          simp [Finset.sum_const, nsmul_eq_mul]
          ring

theorem prob_13_10_fiber_norm_summable_of_linear_bound {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (T : Ω → ℕ)
    (hTMeas : Measurable T)
    (hTIntegrable : Integrable (fun ω => (T ω : ℝ)) P)
    (C : ℝ)
    (hFiberNormBound :
      ∀ m : ℕ,
        ∫ ω in {ω | T ω = m}, ‖prob_13_10_stoppedSum X T ω‖ ∂P ≤
          C * ((m : ℝ) * prob_13_10_countMass P T m)) :
    Summable (fun m : ℕ =>
      ∫ ω in {ω | T ω = m}, ‖prob_13_10_stoppedSum X T ω‖ ∂P) := by
  have hMajor :
      Summable (fun m : ℕ =>
        C * ((m : ℝ) * prob_13_10_countMass P T m)) :=
    (prob_13_10_count_mass_summable P T hTMeas hTIntegrable).mul_left C
  exact hMajor.of_nonneg_of_le
    (fun m => integral_nonneg (fun ω => norm_nonneg _))
    hFiberNormBound

theorem prob_13_10_independent_count_stopped_sum_integrable {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (T : Ω → ℕ)
    (hTMeas : Measurable T)
    (hTIntegrable : Integrable (fun ω => (T ω : ℝ)) P)
    (hXIntegrable : ∀ k : ℕ, Integrable (X k) P)
    (A : ℝ)
    (hAbsMeanBound : ∀ k : ℕ, ∫ ω, |X k ω| ∂P ≤ A)
    (hAbsIndependent :
      ∀ m k : ℕ,
        ProbabilityTheory.IndepFun
          (fun ω => Set.indicator {ω | T ω = m} (fun _ => (1 : ℝ)) ω)
          (fun ω => |X (k + 1) ω|)
          P) :
    Integrable (prob_13_10_stoppedSum X T) P := by
  let s : ℕ → Set Ω := fun m => {ω | T ω = m}
  have hs : ∀ m : ℕ, MeasurableSet (s m) := by
    intro m
    exact hTMeas (measurableSet_singleton m)
  have hFiberIntegrable :
      ∀ m : ℕ, IntegrableOn (prob_13_10_stoppedSum X T) (s m) P := by
    intro m
    have hFixedIntegrable :
        Integrable (fun ω => ∑ k ∈ Finset.range m, X (k + 1) ω) P := by
      exact integrable_finset_sum (Finset.range m)
        (fun k _hk => hXIntegrable (k + 1))
    refine hFixedIntegrable.integrableOn.congr_fun ?_ (hs m)
    intro ω hω
    have hTω : T ω = m := hω
    simp [prob_13_10_stoppedSum, chapter13_stoppedNatSum, hTω]
  have hUnion : (⋃ m : ℕ, s m) = Set.univ := by
    ext ω
    simp [s]
  have hNormSummable :
      Summable (fun m : ℕ =>
        ∫ ω in s m, ‖prob_13_10_stoppedSum X T ω‖ ∂P) := by
    have hFiberNormBound :
        ∀ m : ℕ,
          ∫ ω in {ω | T ω = m},
              ‖prob_13_10_stoppedSum X T ω‖ ∂P ≤
            A * ((m : ℝ) * prob_13_10_countMass P T m) :=
      let hEventMeas : ∀ m : ℕ, MeasurableSet {ω | T ω = m} := by
        intro m
        exact hTMeas (measurableSet_singleton m)
      let hAbsFiberBound :
          ∀ m k : ℕ, k < m →
            ∫ ω in {ω | T ω = m}, |X (k + 1) ω| ∂P ≤
              A * prob_13_10_countMass P T m :=
        prob_13_10_abs_fiber_bound_from_independence
          (P := P) (X := X) (T := T) (A := A)
          hEventMeas hXIntegrable hAbsMeanBound hAbsIndependent
      prob_13_10_fiber_norm_bound_from_abs_prefix
        (P := P) (X := X) (T := T) (A := A)
        hTMeas hXIntegrable hAbsFiberBound
    simpa [s] using
      prob_13_10_fiber_norm_summable_of_linear_bound
        (P := P) (X := X) (T := T)
        hTMeas hTIntegrable A hFiberNormBound
  have hOn :
      IntegrableOn (prob_13_10_stoppedSum X T) (⋃ m : ℕ, s m) P :=
    integrableOn_iUnion_of_summable_integral_norm
      hFiberIntegrable hNormSummable
  rw [hUnion] at hOn
  simpa [IntegrableOn] using hOn

theorem prob_13_10_stopped_sum_count_decomposition {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (T : Ω → ℕ)
    (hTMeas : Measurable T)
    (hStoppedIntegrable : Integrable (prob_13_10_stoppedSum X T) P) :
    ∫ ω, prob_13_10_stoppedSum X T ω ∂P =
      ∑' m : ℕ,
        ∫ ω,
          Set.indicator {ω | T ω = m}
            (fun ω => prob_13_10_stoppedSum X T ω) ω ∂P := by
  let s : ℕ → Set Ω := fun m => {ω | T ω = m}
  have hs : ∀ m : ℕ, MeasurableSet (s m) := by
    intro m
    exact hTMeas (measurableSet_singleton m)
  have hdisj : Pairwise (fun i j => Disjoint (s i) (s j)) := by
    intro i j hij
    refine Set.disjoint_left.2 ?_
    intro ω hi hj
    exact hij (by
      have hi' : T ω = i := hi
      have hj' : T ω = j := hj
      exact hi'.symm.trans hj')
  have hUnion : (⋃ m : ℕ, s m) = Set.univ := by
    ext ω
    simp [s]
  have hfi : IntegrableOn
      (prob_13_10_stoppedSum X T) (⋃ m : ℕ, s m) P := by
    rw [hUnion]
    simpa [IntegrableOn] using hStoppedIntegrable
  have hSetIntegral :
      ∫ ω in (⋃ m : ℕ, s m), prob_13_10_stoppedSum X T ω ∂P =
        ∑' m : ℕ, ∫ ω in s m, prob_13_10_stoppedSum X T ω ∂P := by
    exact integral_iUnion hs hdisj hfi
  calc
    ∫ ω, prob_13_10_stoppedSum X T ω ∂P
        = ∫ ω in (⋃ m : ℕ, s m), prob_13_10_stoppedSum X T ω ∂P := by
          rw [hUnion, setIntegral_univ]
    _ = ∑' m : ℕ,
          ∫ ω in s m, prob_13_10_stoppedSum X T ω ∂P := hSetIntegral
    _ = ∑' m : ℕ,
          ∫ ω,
            Set.indicator {ω | T ω = m}
              (fun ω => prob_13_10_stoppedSum X T ω) ω ∂P := by
          apply tsum_congr
          intro m
          rw [integral_indicator (hs m)]

theorem prob_13_10_independent_count_wald {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (T : Ω → ℕ) (μ : ℝ)
    (hTMeas : Measurable T)
    (hTIntegrable : Integrable (fun ω => (T ω : ℝ)) P)
    (hXIntegrable : ∀ k : ℕ, Integrable (X k) P)
    (hMean : ∀ k : ℕ, ∫ ω, X k ω ∂P = μ)
    (A : ℝ)
    (hAbsMeanBound : ∀ k : ℕ, ∫ ω, |X k ω| ∂P ≤ A)
    (hAbsIndependent :
      ∀ m k : ℕ,
        ProbabilityTheory.IndepFun
          (fun ω => Set.indicator {ω | T ω = m} (fun _ => (1 : ℝ)) ω)
          (fun ω => |X (k + 1) ω|)
          P)
    (hIndependent :
      ∀ m : ℕ,
        ProbabilityTheory.IndepFun
          (fun ω => Set.indicator {ω | T ω = m} (fun _ => (1 : ℝ)) ω)
          (fun ω => ∑ k ∈ Finset.range m, X (k + 1) ω)
          P) :
    prob_13_10_waldIdentity
      (∫ ω, prob_13_10_stoppedSum X T ω ∂P)
      μ
      (∫ ω, (T ω : ℝ) ∂P) := by
  unfold prob_13_10_waldIdentity
  have hEventMeas : ∀ m : ℕ, MeasurableSet {ω | T ω = m} := by
    intro m
    exact hTMeas (measurableSet_singleton m)
  have hFixedIntegrable :
      ∀ m : ℕ,
        Integrable
          (fun ω => ∑ k ∈ Finset.range m, X (k + 1) ω) P := by
    intro m
    exact integrable_finset_sum (Finset.range m)
      (fun k _hk => hXIntegrable (k + 1))
  have hFixedMean :
      ∀ m : ℕ,
        ∫ ω, (∑ k ∈ Finset.range m, X (k + 1) ω) ∂P =
          (m : ℝ) * μ := by
    intro m
    exact prob_13_10_fixed_count_iid_sum_expectation
      (P := P) (X := X) (μ := μ) hXIntegrable hMean m
  have hConditional :
      ∀ m : ℕ,
        ∫ ω,
          Set.indicator {ω | T ω = m}
            (fun ω => prob_13_10_stoppedSum X T ω) ω ∂P =
          ((m : ℝ) * μ) * prob_13_10_countMass P T m :=
    prob_13_10_independent_count_conditional_expectation
      (P := P) (X := X) (T := T) (μ := μ)
      hEventMeas hFixedIntegrable hFixedMean hIndependent
  have hStoppedIntegrable :
      Integrable (prob_13_10_stoppedSum X T) P :=
    prob_13_10_independent_count_stopped_sum_integrable
      (P := P) (X := X) (T := T)
      hTMeas hTIntegrable hXIntegrable A hAbsMeanBound hAbsIndependent
  have hStoppedDecomposition :
      ∫ ω, prob_13_10_stoppedSum X T ω ∂P =
        ∑' m : ℕ,
          ∫ ω,
            Set.indicator {ω | T ω = m}
              (fun ω => prob_13_10_stoppedSum X T ω) ω ∂P :=
    prob_13_10_stopped_sum_count_decomposition P X T hTMeas
      hStoppedIntegrable
  calc
    ∫ ω, prob_13_10_stoppedSum X T ω ∂P
        = ∑' m : ℕ,
            ∫ ω,
              Set.indicator {ω | T ω = m}
                (fun ω => prob_13_10_stoppedSum X T ω) ω ∂P :=
          hStoppedDecomposition
    _ = ∑' m : ℕ, ((m : ℝ) * μ) * prob_13_10_countMass P T m := by
          apply tsum_congr
          intro m
          exact hConditional m
    _ = ∑' m : ℕ, μ * ((m : ℝ) * prob_13_10_countMass P T m) := by
          apply tsum_congr
          intro m
          ring
    _ = μ * (∑' m : ℕ, (m : ℝ) * prob_13_10_countMass P T m) := by
          rw [tsum_mul_left]
    _ = μ * ∫ ω, (T ω : ℝ) ∂P := by
          rw [prob_13_10_integral_nat_count_eq_sum_countMass P T hTMeas hTIntegrable]

theorem prob_13_10_sequence_independent_count_prefix_independent {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (T : Ω → ℕ)
    (hSeqInd :
      ProbabilityTheory.IndepFun T (fun ω => fun n : ℕ => X n ω) P) :
    ∀ m : ℕ,
      ProbabilityTheory.IndepFun
        (fun ω => Set.indicator {ω | T ω = m} (fun _ => (1 : ℝ)) ω)
        (fun ω => ∑ k ∈ Finset.range m, X (k + 1) ω)
        P := by
  intro m
  let φ : ℕ → ℝ :=
    fun t => Set.indicator ({m} : Set ℕ) (fun _ => (1 : ℝ)) t
  let ψ : (ℕ → ℝ) → ℝ :=
    fun xs => ∑ k ∈ Finset.range m, xs (k + 1)
  have hφ : Measurable φ := by
    exact measurable_const.indicator (measurableSet_singleton m)
  have hψ : Measurable ψ := by
    dsimp [ψ]
    fun_prop
  have h := hSeqInd.comp hφ hψ
  have hleft :
      (fun ω => φ (T ω)) =ᶠ[ae P]
        (fun ω => Set.indicator {ω | T ω = m} (fun _ => (1 : ℝ)) ω) := by
    filter_upwards with ω
    rfl
  have hright :
      (fun ω => ψ ((fun ω => fun n : ℕ => X n ω) ω)) =ᶠ[ae P]
        (fun ω => ∑ k ∈ Finset.range m, X (k + 1) ω) := by
    filter_upwards with ω
    rfl
  exact h.congr hleft hright

theorem prob_13_10_sequence_independent_abs_summand_independent {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (T : Ω → ℕ)
    (hSeqInd :
      ProbabilityTheory.IndepFun T (fun ω => fun n : ℕ => X n ω) P) :
    ∀ m k : ℕ,
      ProbabilityTheory.IndepFun
        (fun ω => Set.indicator {ω | T ω = m} (fun _ => (1 : ℝ)) ω)
        (fun ω => |X (k + 1) ω|)
        P := by
  intro m k
  let φ : ℕ → ℝ :=
    fun t => Set.indicator ({m} : Set ℕ) (fun _ => (1 : ℝ)) t
  let ψ : (ℕ → ℝ) → ℝ := fun xs => |xs (k + 1)|
  have hφ : Measurable φ := by
    exact measurable_const.indicator (measurableSet_singleton m)
  have hψ : Measurable ψ := by
    dsimp [ψ]
    fun_prop
  have h := hSeqInd.comp hφ hψ
  have hleft :
      (fun ω => φ (T ω)) =ᶠ[ae P]
        (fun ω => Set.indicator {ω | T ω = m} (fun _ => (1 : ℝ)) ω) := by
    filter_upwards with ω
    rfl
  have hright :
      (fun ω => ψ ((fun ω => fun n : ℕ => X n ω) ω)) =ᶠ[ae P]
        (fun ω => |X (k + 1) ω|) := by
    filter_upwards with ω
    rfl
  exact h.congr hleft hright

theorem prob_13_10_integrable_from_identDistrib {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ)
    (hX1Integrable : Integrable (X 1) P)
    (hIdent : ∀ k : ℕ, ProbabilityTheory.IdentDistrib (X k) (X 1) P P) :
    ∀ k : ℕ, Integrable (X k) P := by
  intro k
  exact (hIdent k).integrable_iff.2 hX1Integrable

theorem prob_13_10_mean_from_identDistrib {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (μ : ℝ)
    (hMeanOne : ∫ ω, X 1 ω ∂P = μ)
    (hIdent : ∀ k : ℕ, ProbabilityTheory.IdentDistrib (X k) (X 1) P P) :
    ∀ k : ℕ, ∫ ω, X k ω ∂P = μ := by
  intro k
  rw [(hIdent k).integral_eq, hMeanOne]

theorem prob_13_10_abs_mean_bound_from_identDistrib {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ)
    (hIdent : ∀ k : ℕ, ProbabilityTheory.IdentDistrib (X k) (X 1) P P) :
    ∀ k : ℕ, ∫ ω, |X k ω| ∂P ≤ ∫ ω, |X 1 ω| ∂P := by
  intro k
  have hAbsIdent :
      ProbabilityTheory.IdentDistrib
        (fun ω => |X k ω|) (fun ω => |X 1 ω|) P P := by
    simpa [Function.comp_def] using (hIdent k).comp measurable_abs
  rw [hAbsIdent.integral_eq]

theorem prob_13_10_independent_count_wald_source {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (T : Ω → ℕ) (μ : ℝ)
    (hTMeas : Measurable T)
    (hTIntegrable : Integrable (fun ω => (T ω : ℝ)) P)
    (hX1Integrable : Integrable (X 1) P)
    (hMeanOne : ∫ ω, X 1 ω ∂P = μ)
    (hIdent : ∀ k : ℕ, ProbabilityTheory.IdentDistrib (X k) (X 1) P P)
    (hSeqInd :
      ProbabilityTheory.IndepFun T (fun ω => fun n : ℕ => X n ω) P) :
    prob_13_10_waldIdentity
      (∫ ω, prob_13_10_stoppedSum X T ω ∂P)
      μ
      (∫ ω, (T ω : ℝ) ∂P) := by
  have hXIntegrable : ∀ k : ℕ, Integrable (X k) P :=
    prob_13_10_integrable_from_identDistrib
      (P := P) (X := X) hX1Integrable hIdent
  have hMean : ∀ k : ℕ, ∫ ω, X k ω ∂P = μ :=
    prob_13_10_mean_from_identDistrib
      (P := P) (X := X) (μ := μ) hMeanOne hIdent
  have hAbsMeanBound :
      ∀ k : ℕ, ∫ ω, |X k ω| ∂P ≤ ∫ ω, |X 1 ω| ∂P :=
    prob_13_10_abs_mean_bound_from_identDistrib
      (P := P) (X := X) hIdent
  have hAbsIndependent :
      ∀ m k : ℕ,
        ProbabilityTheory.IndepFun
          (fun ω => Set.indicator {ω | T ω = m} (fun _ => (1 : ℝ)) ω)
          (fun ω => |X (k + 1) ω|)
          P :=
    prob_13_10_sequence_independent_abs_summand_independent
      (P := P) (X := X) (T := T) hSeqInd
  have hIndependent :
      ∀ m : ℕ,
        ProbabilityTheory.IndepFun
          (fun ω => Set.indicator {ω | T ω = m} (fun _ => (1 : ℝ)) ω)
          (fun ω => ∑ k ∈ Finset.range m, X (k + 1) ω)
          P :=
    prob_13_10_sequence_independent_count_prefix_independent
      (P := P) (X := X) (T := T) hSeqInd
  exact
    prob_13_10_independent_count_wald
      (P := P) (X := X) (T := T) (μ := μ)
      hTMeas hTIntegrable hXIntegrable hMean
      (∫ ω, |X 1 ω| ∂P) hAbsMeanBound hAbsIndependent hIndependent
