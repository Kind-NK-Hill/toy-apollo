/-
TASK ID: thm_10_10
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter10-random-vectors
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_10.def_10_6
import ProbabilityTheory.chapter_10.def_10_1
import ProbabilityTheory.chapter_10.def_10_2
import ProbabilityTheory.chapter_02.prob_2_4




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology



theorem vectorEuclideanNorm_eq_euclideanSpaceNorm {d : ℕ} (v : Fin d → ℝ) :
    vectorEuclideanNorm v =
      ‖(EuclideanSpace.equiv (Fin d) ℝ).symm v‖ := by
  simp [vectorEuclideanNorm, EuclideanSpace.norm_eq, Real.norm_eq_abs]

 
theorem abs_apply_le_vectorEuclideanNorm {d : ℕ} (v : Fin d → ℝ) (i : Fin d) :
    |v i| ≤ vectorEuclideanNorm v := by
  rw [vectorEuclideanNorm_eq_euclideanSpaceNorm]
  simpa [Real.norm_eq_abs] using
    (PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin d) ℝ).symm v) i)



theorem piNorm_le_vectorEuclideanNorm {d : ℕ} (v : Fin d → ℝ) :
    ‖v‖ ≤ vectorEuclideanNorm v := by
  have hnonneg : 0 ≤ vectorEuclideanNorm v := by
    exact Real.sqrt_nonneg _
  apply (pi_norm_le_iff_of_nonneg hnonneg).2
  intro i
  simpa only [Real.norm_eq_abs] using abs_apply_le_vectorEuclideanNorm v i



theorem vectorEuclideanNorm_le_sqrt_card_mul {d : ℕ} (v : Fin d → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hcoord : ∀ i : Fin d, |v i| ≤ δ) :
    vectorEuclideanNorm v ≤ Real.sqrt d * δ := by
  have hsum :
      ∑ i : Fin d, (v i) ^ 2 ≤ (d : ℝ) * δ ^ 2 := by
    calc
      ∑ i : Fin d, (v i) ^ 2
          ≤ ∑ _i : Fin d, δ ^ 2 := by
            apply Finset.sum_le_sum
            intro i _hi
            simpa only [sq_abs] using
              (sq_le_sq₀ (abs_nonneg (v i)) hδ).2 (hcoord i)
      _ = (d : ℝ) * δ ^ 2 := by simp
  rw [vectorEuclideanNorm]
  calc
    Real.sqrt (∑ i : Fin d, (v i) ^ 2)
        ≤ Real.sqrt ((d : ℝ) * δ ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * Real.sqrt (δ ^ 2) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg d)]
    _ = Real.sqrt d * δ := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hδ]



theorem exists_abs_apply_gt_div_sqrt_of_vectorEuclideanNorm_gt
    {d : ℕ} (hd : 0 < d) (v : Fin d → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hnorm : ε < vectorEuclideanNorm v) :
    ∃ i : Fin d, ε / Real.sqrt d < |v i| := by
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 (Nat.cast_pos.2 hd)
  by_contra hnone
  push_neg at hnone
  have hbound :=
    vectorEuclideanNorm_le_sqrt_card_mul v (div_nonneg hε.le hsqrt.le) hnone
  have hcancel : Real.sqrt d * (ε / Real.sqrt d) = ε := by
    field_simp
  linarith



theorem thm_10_10 {d : ℕ} (Vn : ℕ → Fin d → ℝ) (V : Fin d → ℝ) :
    Tendsto Vn atTop (nhds V) ↔
      ∀ i : Fin d, Tendsto (fun n : ℕ => Vn n i) atTop (nhds (V i)) := by
  exact tendsto_pi_nhds



theorem thm_10_10_vector_as_to_component {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Vn : ℕ → Ω → Fin d → ℝ) (V : Ω → Fin d → ℝ)
    (hVn_meas :
      ∀ n : ℕ, ∀ i : Fin d, AEStronglyMeasurable (fun ω => Vn n ω i) μ)
    (hV_meas : ∀ i : Fin d, AEStronglyMeasurable (fun ω => V ω i) μ)
    (hV : VectorConvergesAlmostSurely μ Vn V) :
    ∀ i : Fin d,
      ConvergesAlmostSurelyOnEvent μ
        (fun n ω => Vn n ω i) (fun ω => V ω i) := by
  rcases hV with ⟨E, hE_meas, hE_measure, hE_tendsto⟩
  intro i
  apply (convergesAlmostSurelyOnEvent_iff μ
    (fun n ω => Vn n ω i) (fun ω => V ω i)).2
  apply (convergesAlmostSurely_iff_exists_measure_one_event μ
    (fun n ω => Vn n ω i) (fun ω => V ω i)).2
  refine ⟨fun n => hVn_meas n i, hV_meas i, E, hE_meas, hE_measure, ?_⟩
  intro ω hω
  exact (thm_10_10 (fun n : ℕ => Vn n ω) (V ω)).mp (hE_tendsto ω hω) i



theorem thm_10_10_component_as_to_vector_on_event {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (μ : Measure Ω) (Vn : ℕ → Ω → Fin d → ℝ) (V : Ω → Fin d → ℝ)
    (E : Set Ω) (hE_meas : MeasurableSet E) (hE_measure : μ E = 1)
    (hE_tendsto :
      ∀ ω ∈ E, ∀ i : Fin d,
        Tendsto (fun n : ℕ => Vn n ω i) atTop (nhds (V ω i))) :
    VectorConvergesAlmostSurely μ Vn V := by
  refine ⟨E, hE_meas, hE_measure, ?_⟩
  intro ω hω
  exact (thm_10_10 (fun n : ℕ => Vn n ω) (V ω)).mpr (hE_tendsto ω hω)



theorem thm_10_10_component_as_to_vector {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Vn : ℕ → Ω → Fin d → ℝ) (V : Ω → Fin d → ℝ)
    (hcomp :
      ∀ i : Fin d,
        ConvergesAlmostSurelyOnEvent μ
          (fun n ω => Vn n ω i) (fun ω => V ω i)) :
    VectorConvergesAlmostSurely μ Vn V := by
  classical
  have hcomp_one :
      ∀ i : Fin d,
        ∃ E : Set Ω, MeasurableSet E ∧ μ E = 1 ∧
          ∀ ω ∈ E,
            Tendsto (fun n : ℕ => Vn n ω i) atTop (nhds (V ω i)) := by
    intro i
    exact
      ((convergesAlmostSurely_iff_exists_measure_one_event μ
        (fun n ω => Vn n ω i) (fun ω => V ω i)).1
          ((convergesAlmostSurelyOnEvent_iff μ
            (fun n ω => Vn n ω i) (fun ω => V ω i)).1 (hcomp i))).2.2
  let E : Fin d → Set Ω := fun i => Classical.choose (hcomp_one i)
  have hE_meas : ∀ i, MeasurableSet (E i) := fun i =>
    (Classical.choose_spec (hcomp_one i)).1
  have hE_measure : ∀ i, μ (E i) = 1 := fun i =>
    (Classical.choose_spec (hcomp_one i)).2.1
  have hE_tendsto :
      ∀ i, ∀ ω ∈ E i,
        Tendsto (fun n : ℕ => Vn n ω i) atTop (nhds (V ω i)) := fun i =>
    (Classical.choose_spec (hcomp_one i)).2.2
  let B : ℕ → Set Ω := fun n =>
    if h : n < d then E ⟨n, h⟩ else Set.univ
  have hB_meas : ∀ n, MeasurableSet (B n) := by
    intro n
    by_cases h : n < d
    · simp [B, h, hE_meas]
    · simp [B, h]
  have hB_measure : ∀ n, μ (B n) = 1 := by
    intro n
    by_cases h : n < d
    · simpa [B, h] using hE_measure ⟨n, h⟩
    · simp [B, h, MeasureTheory.IsProbabilityMeasure.measure_univ]
  have hB_inter_measure : μ (⋂ n, B n) = 1 := by
    rw [MeasureTheory.measure_congr, MeasureTheory.IsProbabilityMeasure.measure_univ]
    simp_all +decide [Set.compl_iInter]
  refine thm_10_10_component_as_to_vector_on_event μ Vn V (⋂ n, B n)
    (MeasurableSet.iInter hB_meas)
    hB_inter_measure ?_
  intro ω hω i
  have hmemB : ω ∈ B i.1 := Set.mem_iInter.mp hω i.1
  have hmemE : ω ∈ E i := by
    simpa [B, i.2] using hmemB
  exact hE_tendsto i ω hmemE



theorem thm_10_10_vector_prob_to_component {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Vn : ℕ → Ω → Fin d → ℝ) (V : Ω → Fin d → ℝ)
    (hVn_meas : ∀ n : ℕ, ∀ i : Fin d, Measurable (fun ω => Vn n ω i))
    (hV_meas : ∀ i : Fin d, Measurable (fun ω => V ω i))
    (hV : VectorConvergesInProbability μ Vn V) :
    ∀ i : Fin d,
      ConvergesInProbability μ
        (fun n ω => Vn n ω i) (fun ω => V ω i) := by
  intro i
  refine ⟨fun n => hVn_meas n i, hV_meas i, ?_⟩
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hV ε hε)
    (fun _ => zero_le) ?_
  intro n
  apply measure_mono
  intro ω hω
  have hcoord : ‖(Vn n ω - V ω) i‖ > ε := by
    simpa [deviationEvent, Pi.sub_apply, Real.norm_eq_abs] using hω
  exact lt_of_lt_of_le hcoord (by
    simpa [Real.norm_eq_abs] using
      abs_apply_le_vectorEuclideanNorm (Vn n ω - V ω) i)



theorem thm_10_10_component_prob_to_vector {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Vn : ℕ → Ω → Fin d → ℝ) (V : Ω → Fin d → ℝ)
    (hcomp :
      ∀ i : Fin d,
        ConvergesInProbability μ
          (fun n ω => Vn n ω i) (fun ω => V ω i)) :
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
    have hthreshold : 0 < ε / Real.sqrt d := div_pos hε hsqrt_pos
    have hsum :
        Tendsto
          (fun n : ℕ =>
            ∑ i : Fin d,
              μ (deviationEvent (fun n ω => Vn n ω i) (fun ω => V ω i) n
                (ε / Real.sqrt d)))
          atTop (nhds 0) := by
      simpa using
        (tendsto_finset_sum (s := (Finset.univ : Finset (Fin d)))
          (fun i _hi => (hcomp i).2.2 (ε / Real.sqrt d) hthreshold))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => zero_le) ?_
    intro n
    calc
      μ (vectorDeviationEvent Vn V n ε)
          ≤ μ (⋃ i : Fin d,
              deviationEvent (fun n ω => Vn n ω i) (fun ω => V ω i) n
                (ε / Real.sqrt d)) := by
            apply measure_mono
            intro ω hω
            obtain ⟨i, hi⟩ :=
              exists_abs_apply_gt_div_sqrt_of_vectorEuclideanNorm_gt
                hd_pos (Vn n ω - V ω) hε hω
            rw [Set.mem_iUnion]
            exact ⟨i, by
              simpa [deviationEvent, Pi.sub_apply, Real.norm_eq_abs] using hi⟩
        _ ≤ ∑' i : Fin d,
              μ (deviationEvent (fun n ω => Vn n ω i) (fun ω => V ω i) n
                (ε / Real.sqrt d)) :=
            measure_iUnion_le _
        _ = ∑ i : Fin d,
              μ (deviationEvent (fun n ω => Vn n ω i) (fun ω => V ω i) n
                (ε / Real.sqrt d)) := by
            rw [tsum_fintype]

 
theorem thm_10_10_almost_sure_iff {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Vn : ℕ → Ω → Fin d → ℝ) (V : Ω → Fin d → ℝ)
    (hVn_meas :
      ∀ n : ℕ, ∀ i : Fin d, AEStronglyMeasurable (fun ω => Vn n ω i) μ)
    (hV_meas : ∀ i : Fin d, AEStronglyMeasurable (fun ω => V ω i) μ) :
    VectorConvergesAlmostSurely μ Vn V ↔
      ∀ i : Fin d,
        ConvergesAlmostSurelyOnEvent μ
          (fun n ω => Vn n ω i) (fun ω => V ω i) := by
  constructor
  · exact thm_10_10_vector_as_to_component μ Vn V hVn_meas hV_meas
  · exact thm_10_10_component_as_to_vector μ Vn V

 
theorem thm_10_10_probability_iff {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Vn : ℕ → Ω → Fin d → ℝ) (V : Ω → Fin d → ℝ)
    (hVn_meas : ∀ n : ℕ, ∀ i : Fin d, Measurable (fun ω => Vn n ω i))
    (hV_meas : ∀ i : Fin d, Measurable (fun ω => V ω i)) :
    VectorConvergesInProbability μ Vn V ↔
      ∀ i : Fin d,
        ConvergesInProbability μ
          (fun n ω => Vn n ω i) (fun ω => V ω i) := by
  constructor
  · exact thm_10_10_vector_prob_to_component μ Vn V hVn_meas hV_meas
  · exact thm_10_10_component_prob_to_vector μ Vn V
