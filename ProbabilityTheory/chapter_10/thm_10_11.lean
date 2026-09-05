/-
TASK ID: thm_10_11
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter10-continuous-mapping
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_10.thm_10_10
import ProbabilityTheory.chapter_10.def_10_1
import ProbabilityTheory.chapter_10.def_10_2
import ProbabilityTheory.chapter_10.def_10_6




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology



theorem tendstoInMeasure_of_vectorConvergesInProbability {Ω : Type*}
    [MeasurableSpace Ω] {d : ℕ} (μ : Measure Ω)
    (Vn : ℕ → Ω → Fin d → ℝ) (V : Ω → Fin d → ℝ)
    (hProb : VectorConvergesInProbability μ Vn V) :
    TendstoInMeasure μ Vn atTop V := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hprob_half := hProb (ε / 2) hhalf
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hprob_half
    (fun _ => bot_le) ?_
  intro n
  apply measure_mono
  intro ω hω
  have hstrict : ε / 2 < ‖Vn n ω - V ω‖ := by
    have hle : ε ≤ ‖Vn n ω - V ω‖ := by simpa using hω
    linarith
  have hstrict_euclidean :
      ε / 2 < vectorEuclideanNorm (Vn n ω - V ω) :=
    hstrict.trans_le (piNorm_le_vectorEuclideanNorm (Vn n ω - V ω))
  simpa [vectorDeviationEvent] using hstrict_euclidean



theorem vectorConvergesInProbability_of_tendstoInMeasure {Ω : Type*}
    [MeasurableSpace Ω] {d : ℕ} (μ : Measure Ω)
    (Vn : ℕ → Ω → Fin d → ℝ) (V : Ω → Fin d → ℝ)
    (h : TendstoInMeasure μ Vn atTop V) :
    VectorConvergesInProbability μ Vn V := by
  intro ε hε
  by_cases hd : d = 0
  · subst d
    simpa [vectorDeviationEvent, vectorEuclideanNorm, not_lt.mpr hε.le] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (nhds 0))
  · have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
    have hsqrt_pos : 0 < Real.sqrt d :=
      Real.sqrt_pos.2 (Nat.cast_pos.2 hd_pos)
    let δ : ℝ := ε / (2 * Real.sqrt d)
    have hδ : 0 < δ := div_pos hε (mul_pos zero_lt_two hsqrt_pos)
    have hnorm :=
      (tendstoInMeasure_iff_norm (μ := μ) (f := Vn) (g := V)).mp h δ hδ
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hnorm
      (fun _ => bot_le) ?_
    intro n
    apply measure_mono
    intro ω hω
    obtain ⟨i, hi⟩ :=
      exists_abs_apply_gt_div_sqrt_of_vectorEuclideanNorm_gt
        hd_pos (Vn n ω - V ω) hε hω
    have hi_sup :
        ε / Real.sqrt d < ‖Vn n ω - V ω‖ :=
      hi.trans_le (by
        simpa [Real.norm_eq_abs] using
          norm_le_pi_norm (Vn n ω - V ω) i)
    have hδ_lt : δ < ε / Real.sqrt d := by
      dsimp [δ]
      calc
        ε / (2 * Real.sqrt d) = (ε / Real.sqrt d) / 2 := by ring
        _ < ε / Real.sqrt d := by
          linarith [div_pos hε hsqrt_pos]
    exact le_of_lt (hδ_lt.trans hi_sup)

private theorem thm_10_11_continuous_vectorEuclideanNorm {d : ℕ} :
    Continuous (@vectorEuclideanNorm d) := by
  have heq : (@vectorEuclideanNorm d) =
      fun v => ‖(EuclideanSpace.equiv (Fin d) ℝ).symm v‖ := by
    funext v
    exact vectorEuclideanNorm_eq_euclideanSpaceNorm v
  rw [heq]
  exact continuous_norm.comp (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous

 
theorem thm_10_11_almost_sure {Ω : Type*} [MeasurableSpace Ω]
    {d m : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Vn : ℕ → Ω → Fin d → ℝ) (V : Ω → Fin d → ℝ)
    (f : (Fin d → ℝ) → (Fin m → ℝ)) (S : Set (Fin d → ℝ))
    (hS_meas : MeasurableSet {ω : Ω | V ω ∈ S})
    (hS_measure : μ {ω : Ω | V ω ∈ S} = 1)
    (hf_cont : ∀ v ∈ S, ContinuousAt f v)
    (hV : VectorConvergesAlmostSurely μ Vn V) :
    VectorConvergesAlmostSurely μ (fun n ω => f (Vn n ω)) (fun ω => f (V ω)) := by
  classical
  rcases hV with ⟨B, hB_meas, hB_measure, hB_tendsto⟩
  let A : Set Ω := {ω : Ω | V ω ∈ S}
  let C : ℕ → Set Ω := fun n =>
    if n = 0 then A else if n = 1 then B else Set.univ
  have hC_meas : ∀ n, MeasurableSet (C n) := by
    intro n
    by_cases h0 : n = 0
    · simp [C, h0, A, hS_meas]
    · by_cases h1 : n = 1
      · simp [C, h0, h1, hB_meas]
      · simp [C, h0, h1]
  have hC_measure : ∀ n, μ (C n) = 1 := by
    intro n
    by_cases h0 : n = 0
    · simpa [C, h0, A] using hS_measure
    · by_cases h1 : n = 1
      · simpa [C, h0, h1] using hB_measure
      · simp [C, h0, h1, MeasureTheory.IsProbabilityMeasure.measure_univ]
  have hC_inter_measure : μ (⋂ n, C n) = 1 := by
    rw [MeasureTheory.measure_congr, MeasureTheory.IsProbabilityMeasure.measure_univ]
    simp_all +decide [Set.compl_iInter]
  refine ⟨⋂ n, C n, MeasurableSet.iInter hC_meas, hC_inter_measure, ?_⟩
  intro ω hω
  have hAω : ω ∈ A := by
    have hmem : ω ∈ C 0 := Set.mem_iInter.mp hω 0
    simpa [C, A] using hmem
  have hBω : ω ∈ B := by
    have hmem : ω ∈ C 1 := Set.mem_iInter.mp hω 1
    simpa [C] using hmem
  exact (hf_cont (V ω) hAω).tendsto.comp (hB_tendsto ω hBω)

 
theorem thm_10_11_probability {Ω : Type*} [MeasurableSpace Ω]
    {d m : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Vn : ℕ → Ω → Fin d → ℝ) (V : Ω → Fin d → ℝ)
    (f : (Fin d → ℝ) → (Fin m → ℝ)) (S : Set (Fin d → ℝ))
    (hVn_meas : ∀ n : ℕ, AEStronglyMeasurable (Vn n) μ)
    (hS_meas : MeasurableSet {ω : Ω | V ω ∈ S})
    (hS_measure : μ {ω : Ω | V ω ∈ S} = 1)
    (hf_cont : ∀ v ∈ S, ContinuousAt f v)
    (hV : VectorConvergesInProbability μ Vn V) :
    VectorConvergesInProbability μ (fun n ω => f (Vn n ω)) (fun ω => f (V ω)) := by
  classical
  let A : Set Ω := {ω : Ω | V ω ∈ S}
  have hS_ae : ∀ᵐ ω ∂μ, V ω ∈ S := by
    rw [MeasureTheory.ae_iff]
    have hA_meas : MeasurableSet A := by
      simpa [A] using hS_meas
    have hA_measure : μ A = 1 := by
      simpa [A] using hS_measure
    have hfin : μ A ≠ ⊤ := by
      rw [hA_measure]
      simp
    have hcompl : μ Aᶜ = 0 := by
      rw [MeasureTheory.measure_compl hA_meas hfin]
      simp [hA_measure, MeasureTheory.IsProbabilityMeasure.measure_univ]
    simpa [A, Set.compl_setOf] using hcompl
  have hV_meas : AEStronglyMeasurable V μ :=
    (tendstoInMeasure_of_vectorConvergesInProbability μ Vn V hV).aestronglyMeasurable
      hVn_meas
  intro ε hε
  let r : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  let bad : ℕ → Set (Fin d → ℝ) := fun j =>
    {v | ∃ w,
      vectorEuclideanNorm (w - v) < 2 * r j ∧
      ε < vectorEuclideanNorm (f w - f v)}
  let C : ℕ → Set Ω := fun j => {ω | V ω ∈ bad j}
  let B : ℕ → Set Ω := fun j => {ω | V ω ∈ S} ∩ C j
  have hr_pos (j : ℕ) : 0 < r j := by
    dsimp [r]
    positivity
  have hr_anti : Antitone r := by
    intro j k hjk
    dsimp [r]
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast Nat.add_le_add_right hjk 1
  have hbad_anti : Antitone bad := by
    intro j k hjk v hv
    rcases hv with ⟨w, hw_near, hw_far⟩
    exact ⟨w, hw_near.trans_le (mul_le_mul_of_nonneg_left (hr_anti hjk) (by norm_num)),
      hw_far⟩
  have hbad_interior :
      ∀ j v, v ∈ S → v ∈ bad j → v ∈ interior (bad j) := by
    intro j v hvS hvbad
    rcases hvbad with ⟨w, hw_near, hw_far⟩
    apply mem_interior_iff_mem_nhds.2
    have hnear_cont :
        ContinuousAt (fun u : Fin d → ℝ => vectorEuclideanNorm (w - u)) v :=
      thm_10_11_continuous_vectorEuclideanNorm.continuousAt.comp
        (continuousAt_const.sub continuousAt_id)
    have hfar_cont :
        ContinuousAt (fun u : Fin d → ℝ => vectorEuclideanNorm (f w - f u)) v :=
      thm_10_11_continuous_vectorEuclideanNorm.continuousAt.comp
        (continuousAt_const.sub (hf_cont v hvS))
    have hnear_event :
        {u : Fin d → ℝ | vectorEuclideanNorm (w - u) < 2 * r j} ∈ 𝓝 v :=
      hnear_cont (Iio_mem_nhds hw_near)
    have hfar_event :
        {u : Fin d → ℝ | ε < vectorEuclideanNorm (f w - f u)} ∈ 𝓝 v :=
      hfar_cont (Ioi_mem_nhds hw_far)
    filter_upwards [hnear_event, hfar_event] with u hu_near hu_far
    exact ⟨w, hu_near, hu_far⟩
  have hB_eq (j : ℕ) :
      B j = {ω : Ω | V ω ∈ S} ∩ V ⁻¹' interior (bad j) := by
    ext ω
    change (V ω ∈ S ∧ V ω ∈ bad j) ↔
      (V ω ∈ S ∧ V ω ∈ interior (bad j))
    constructor
    · rintro ⟨hSω, hbadω⟩
      exact ⟨hSω, hbad_interior j (V ω) hSω hbadω⟩
    · rintro ⟨hSω, hintω⟩
      exact ⟨hSω, interior_subset hintω⟩
  have hB_null : ∀ j, NullMeasurableSet (B j) μ := by
    intro j
    rw [hB_eq j]
    exact hS_meas.nullMeasurableSet.inter
      (hV_meas.aemeasurable.nullMeasurableSet_preimage
        isOpen_interior.measurableSet)
  have hC_anti : Antitone C := by
    intro j k hjk ω hω
    exact hbad_anti hjk hω
  have hB_anti : Antitone B := by
    intro j k hjk ω hω
    exact ⟨hω.1, hC_anti hjk hω.2⟩
  have hB_inter : (⋂ j, B j) = ∅ := by
    apply Set.Subset.antisymm
    · intro ω hω
      have hall : ∀ j, ω ∈ B j := Set.mem_iInter.mp hω
      have hSω : V ω ∈ S := (hall 0).1
      have hout_cont :
          ContinuousAt (fun w : Fin d → ℝ =>
            vectorEuclideanNorm (f w - f (V ω))) (V ω) :=
        thm_10_11_continuous_vectorEuclideanNorm.continuousAt.comp
          ((hf_cont (V ω) hSω).sub continuousAt_const)
      have hzero : vectorEuclideanNorm (f (V ω) - f (V ω)) < ε := by
        simpa [vectorEuclideanNorm] using hε
      have hgood_nhds :
          {w : Fin d → ℝ | vectorEuclideanNorm (f w - f (V ω)) < ε} ∈ 𝓝 (V ω) :=
        hout_cont (Iio_mem_nhds hzero)
      rcases Metric.mem_nhds_iff.1 hgood_nhds with ⟨ρ, hρ, hball⟩
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt (half_pos hρ)
      have h2r : 2 * r j < ρ := by
        dsimp [r]
        linarith
      have hbadω : V ω ∈ bad j := (hall j).2
      rcases hbadω with ⟨w, hw_near, hw_far⟩
      have hnorm : ‖w - V ω‖ < ρ :=
        (piNorm_le_vectorEuclideanNorm (w - V ω)).trans_lt
          (hw_near.trans h2r)
      have hw_ball : w ∈ Metric.ball (V ω) ρ := by
        simpa [dist_eq_norm] using hnorm
      have hw_good := hball hw_ball
      change vectorEuclideanNorm (f w - f (V ω)) < ε at hw_good
      have : False := by linarith
      exact this.elim
    · exact Set.empty_subset _
  have hB_tendsto : Tendsto (fun j => μ (B j)) atTop (𝓝 0) := by
    have hmeasure := tendsto_measure_iInter_atTop hB_null hB_anti
      ⟨0, measure_ne_top μ (B 0)⟩
    rw [hB_inter, measure_empty] at hmeasure
    simpa [Function.comp_def] using hmeasure
  have hCB_measure (j : ℕ) : μ (C j) = μ (B j) := by
    apply measure_congr
    filter_upwards [hS_ae] with ω hSω
    apply propext
    change (V ω ∈ bad j) ↔ (V ω ∈ S ∧ V ω ∈ bad j)
    simp [hSω]
  have hC_tendsto : Tendsto (fun j => μ (C j)) atTop (𝓝 0) := by
    convert hB_tendsto using 1
    ext j
    exact hCB_measure j
  rw [ENNReal.tendsto_atTop_zero]
  intro η hη
  have hη_half : 0 < η / 2 := ENNReal.half_pos hη.ne'
  obtain ⟨j, hj⟩ :=
    (ENNReal.tendsto_atTop_zero.mp hC_tendsto) (η / 2) hη_half
  obtain ⟨N, hN⟩ :=
    (ENNReal.tendsto_atTop_zero.mp (hV (r j) (hr_pos j))) (η / 2) hη_half
  refine ⟨N, fun n hn => ?_⟩
  have hsubset :
      vectorDeviationEvent (fun n ω => f (Vn n ω)) (fun ω => f (V ω)) n ε ⊆
        C j ∪ vectorDeviationEvent Vn V n (r j) := by
    intro ω hout
    by_cases hfar : ω ∈ vectorDeviationEvent Vn V n (r j)
    · exact Or.inr hfar
    · apply Or.inl
      have hle : vectorEuclideanNorm (Vn n ω - V ω) ≤ r j := by
        simpa [vectorDeviationEvent] using not_lt.mp hfar
      change V ω ∈ bad j
      refine ⟨Vn n ω, ?_, ?_⟩
      · exact lt_of_le_of_lt hle (by linarith [hr_pos j])
      · simpa [vectorDeviationEvent] using hout
  calc
    μ (vectorDeviationEvent (fun n ω => f (Vn n ω)) (fun ω => f (V ω)) n ε) ≤
        μ (C j ∪ vectorDeviationEvent Vn V n (r j)) := measure_mono hsubset
    _ ≤ μ (C j) + μ (vectorDeviationEvent Vn V n (r j)) := measure_union_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add (hj j le_rfl) (hN n hn)
    _ = η := ENNReal.add_halves η



theorem thm_10_11 {Ω : Type*} [MeasurableSpace Ω]
    {d m : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Vn : ℕ → Ω → Fin d → ℝ) (V : Ω → Fin d → ℝ)
    (f : (Fin d → ℝ) → (Fin m → ℝ)) (S : Set (Fin d → ℝ))
    (hVn_meas : ∀ n : ℕ, AEStronglyMeasurable (Vn n) μ)
    (hS_meas : MeasurableSet {ω : Ω | V ω ∈ S})
    (hS_measure : μ {ω : Ω | V ω ∈ S} = 1)
    (hf_cont : ∀ v ∈ S, ContinuousAt f v) :
    (VectorConvergesAlmostSurely μ Vn V →
      VectorConvergesAlmostSurely μ
        (fun n ω => f (Vn n ω)) (fun ω => f (V ω))) ∧
    (VectorConvergesInProbability μ Vn V →
      VectorConvergesInProbability μ
        (fun n ω => f (Vn n ω)) (fun ω => f (V ω))) := by
  constructor
  · exact thm_10_11_almost_sure μ Vn V f S hS_meas hS_measure hf_cont
  · exact thm_10_11_probability μ Vn V f S hVn_meas hS_meas hS_measure
      hf_cont
