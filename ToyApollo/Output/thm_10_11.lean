/-
TASK ID: thm_10_11
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter10-continuous-mapping
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_10_10
import ToyApollo.Output.def_10_1
import ToyApollo.Output.def_10_2
import ToyApollo.Output.def_10_6

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
    (fun _ => zero_le _) ?_
  intro n
  apply measure_mono
  intro ω hω
  have hstrict : ε / 2 < ‖Vn n ω - V ω‖ := by
    have hle : ε ≤ ‖Vn n ω - V ω‖ := by simpa using hω
    linarith
  simpa [vectorDeviationEvent] using hstrict

theorem vectorConvergesInProbability_of_tendstoInMeasure {Ω : Type*}
    [MeasurableSpace Ω] {d : ℕ} (μ : Measure Ω)
    (Vn : ℕ → Ω → Fin d → ℝ) (V : Ω → Fin d → ℝ)
    (h : TendstoInMeasure μ Vn atTop V) :
    VectorConvergesInProbability μ Vn V := by
  intro ε hε
  have hnorm := (tendstoInMeasure_iff_norm (μ := μ) (f := Vn) (g := V)).mp h ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hnorm
    (fun _ => zero_le _) ?_
  intro n
  apply measure_mono
  intro ω hω
  have hle : ε ≤ ‖Vn n ω - V ω‖ := le_of_lt hω
  simpa [vectorDeviationEvent] using hle

theorem tendstoInMeasure_comp_of_ae_continuousAt {Ω : Type*} [MeasurableSpace Ω]
    {d m : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (Vn : ℕ → Ω → Fin d → ℝ) (V : Ω → Fin d → ℝ)
    (f : (Fin d → ℝ) → (Fin m → ℝ)) (S : Set (Fin d → ℝ))
    (hVn_meas : ∀ n : ℕ, AEStronglyMeasurable (Vn n) μ)
    (hcomp_meas : ∀ n : ℕ, AEStronglyMeasurable (fun ω => f (Vn n ω)) μ)
    (hV : TendstoInMeasure μ Vn atTop V)
    (hS_ae : ∀ᵐ ω ∂μ, V ω ∈ S)
    (hf_cont : ∀ v ∈ S, ContinuousAt f v) :
    TendstoInMeasure μ (fun n ω => f (Vn n ω)) atTop (fun ω => f (V ω)) := by
  rw [MeasureTheory.exists_seq_tendstoInMeasure_atTop_iff hcomp_meas]
  intro ns hns
  obtain ⟨ns', hns', hsub_ae⟩ :=
    (MeasureTheory.exists_seq_tendstoInMeasure_atTop_iff hVn_meas).mp hV ns hns
  refine ⟨ns', hns', ?_⟩
  filter_upwards [hsub_ae, hS_ae] with ω hlim hSω
  exact (hf_cont (V ω) hSω).tendsto.comp hlim

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
    (hcomp_meas : ∀ n : ℕ, AEStronglyMeasurable (fun ω => f (Vn n ω)) μ)
    (hS_meas : MeasurableSet {ω : Ω | V ω ∈ S})
    (hS_measure : μ {ω : Ω | V ω ∈ S} = 1)
    (hf_cont : ∀ v ∈ S, ContinuousAt f v)
    (hV : VectorConvergesInProbability μ Vn V) :
    VectorConvergesInProbability μ (fun n ω => f (Vn n ω)) (fun ω => f (V ω)) := by
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
  exact vectorConvergesInProbability_of_tendstoInMeasure μ
    (fun n ω => f (Vn n ω)) (fun ω => f (V ω)) <|
      tendstoInMeasure_comp_of_ae_continuousAt μ Vn V f S hVn_meas hcomp_meas
        (tendstoInMeasure_of_vectorConvergesInProbability μ Vn V hV) hS_ae hf_cont

theorem thm_10_11 {Ω : Type*} [MeasurableSpace Ω]
    {d m : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Vn : ℕ → Ω → Fin d → ℝ) (V : Ω → Fin d → ℝ)
    (f : (Fin d → ℝ) → (Fin m → ℝ)) (S : Set (Fin d → ℝ))
    (hVn_meas : ∀ n : ℕ, AEStronglyMeasurable (Vn n) μ)
    (hcomp_meas : ∀ n : ℕ, AEStronglyMeasurable (fun ω => f (Vn n ω)) μ)
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
  · exact thm_10_11_probability μ Vn V f S hVn_meas hcomp_meas hS_meas hS_measure
      hf_cont
