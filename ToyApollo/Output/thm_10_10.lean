/-
TASK ID: thm_10_10
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter10-random-vectors
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_10_6
import ToyApollo.Output.def_10_1
import ToyApollo.Output.def_10_2
import ToyApollo.Output.prob_2_4

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology

theorem thm_10_10 {d : ℕ} (Vn : ℕ → Fin d → ℝ) (V : Fin d → ℝ) :
    Tendsto Vn atTop (nhds V) ↔
      ∀ i : Fin d, Tendsto (fun n : ℕ => Vn n i) atTop (nhds (V i)) := by
  exact tendsto_pi_nhds

theorem thm_10_10_vector_as_to_component {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (μ : Measure Ω) (Vn : ℕ → Ω → Fin d → ℝ) (V : Ω → Fin d → ℝ)
    (hV : VectorConvergesAlmostSurely μ Vn V) :
    ∀ i : Fin d,
      ConvergesAlmostSurelyOnEvent μ
        (fun n ω => Vn n ω i) (fun ω => V ω i) := by
  rcases hV with ⟨E, hE_meas, hE_measure, hE_tendsto⟩
  intro i
  refine ⟨E, hE_meas, hE_measure, ?_⟩
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
  let E : Fin d → Set Ω := fun i => Classical.choose (hcomp i)
  have hE_meas : ∀ i, MeasurableSet (E i) := fun i =>
    (Classical.choose_spec (hcomp i)).1
  have hE_measure : ∀ i, μ (E i) = 1 := fun i =>
    (Classical.choose_spec (hcomp i)).2.1
  have hE_tendsto :
      ∀ i, ∀ ω ∈ E i,
        Tendsto (fun n : ℕ => Vn n ω i) atTop (nhds (V ω i)) := fun i =>
    (Classical.choose_spec (hcomp i)).2.2
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
    {d : ℕ} (μ : Measure Ω) (Vn : ℕ → Ω → Fin d → ℝ) (V : Ω → Fin d → ℝ)
    (hV : VectorConvergesInProbability μ Vn V) :
    ∀ i : Fin d,
      ConvergesInProbability μ
        (fun n ω => Vn n ω i) (fun ω => V ω i) := by
  intro i ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hV ε hε)
    (fun n => zero_le _) ?_
  intro n
  apply measure_mono
  intro ω hω
  have hcoord : ‖(Vn n ω - V ω) i‖ > ε := by
    simpa [deviationEvent, Pi.sub_apply, Real.norm_eq_abs] using hω
  exact lt_of_lt_of_le hcoord (norm_le_pi_norm (Vn n ω - V ω) i)

theorem thm_10_10_component_prob_to_vector {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (μ : Measure Ω) (Vn : ℕ → Ω → Fin d → ℝ) (V : Ω → Fin d → ℝ)
    (hcomp :
      ∀ i : Fin d,
        ConvergesInProbability μ
          (fun n ω => Vn n ω i) (fun ω => V ω i)) :
    VectorConvergesInProbability μ Vn V := by
  intro ε hε
  have hsum :
      Tendsto
        (fun n : ℕ =>
          ∑ i : Fin d,
            μ (deviationEvent (fun n ω => Vn n ω i) (fun ω => V ω i) n ε))
        atTop (nhds 0) := by
    simpa using
      (tendsto_finset_sum (s := (Finset.univ : Finset (Fin d)))
        (fun i _hi => hcomp i ε hε))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun n => zero_le _) ?_
  intro n
  calc
    μ (vectorDeviationEvent Vn V n ε)
        ≤ μ (⋃ i : Fin d,
            deviationEvent (fun n ω => Vn n ω i) (fun ω => V ω i) n ε) := by
          apply measure_mono
          intro ω hω
          rw [Set.mem_iUnion]
          by_contra hnone
          have hall :
              ∀ i : Fin d, ‖(Vn n ω - V ω) i‖ ≤ ε := by
            intro i
            exact le_of_not_gt fun hi =>
              hnone ⟨i, by
                simpa [deviationEvent, Pi.sub_apply, Real.norm_eq_abs] using hi⟩
          have hle : ‖Vn n ω - V ω‖ ≤ ε :=
            (pi_norm_le_iff_of_nonneg hε.le).mpr hall
          exact not_le_of_gt hω hle
      _ ≤ ∑' i : Fin d,
            μ (deviationEvent (fun n ω => Vn n ω i) (fun ω => V ω i) n ε) :=
          measure_iUnion_le _
      _ = ∑ i : Fin d,
            μ (deviationEvent (fun n ω => Vn n ω i) (fun ω => V ω i) n ε) := by
          rw [tsum_fintype]

theorem thm_10_10_almost_sure_iff {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Vn : ℕ → Ω → Fin d → ℝ) (V : Ω → Fin d → ℝ) :
    VectorConvergesAlmostSurely μ Vn V ↔
      ∀ i : Fin d,
        ConvergesAlmostSurelyOnEvent μ
          (fun n ω => Vn n ω i) (fun ω => V ω i) := by
  constructor
  · exact thm_10_10_vector_as_to_component μ Vn V
  · exact thm_10_10_component_as_to_vector μ Vn V

theorem thm_10_10_probability_iff {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (μ : Measure Ω)
    (Vn : ℕ → Ω → Fin d → ℝ) (V : Ω → Fin d → ℝ) :
    VectorConvergesInProbability μ Vn V ↔
      ∀ i : Fin d,
        ConvergesInProbability μ
          (fun n ω => Vn n ω i) (fun ω => V ω i) := by
  constructor
  · exact thm_10_10_vector_prob_to_component μ Vn V
  · exact thm_10_10_component_prob_to_vector μ Vn V
