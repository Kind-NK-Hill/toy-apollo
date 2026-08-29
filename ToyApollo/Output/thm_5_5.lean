/-
TASK ID: thm_5_5
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_3_10
import ToyApollo.Output.thm_3_7

open MeasureTheory

theorem piSystem_isPiSystem {C : Set (Set ℝ)} (h : PiSystem C) : IsPiSystem C :=
  fun _A hA _B hB _ => h hA hB

def productIdentityDynkin {Ω : Type _} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    {s : Set Ω} (hs : MeasurableSet s) : MeasurableSpace.DynkinSystem Ω where
  Has := fun t => MeasurableSet t ∧ μ (s ∩ t) = μ s * μ t
  has_empty := ⟨MeasurableSet.empty, by simp⟩
  has_compl := by
    rintro t ⟨ht, hprod⟩
    refine ⟨ht.compl, ?_⟩
    have h1 : μ (s ∩ t) + μ (s ∩ tᶜ) = μ s := by
      rw [← Set.diff_eq]
      exact measure_inter_add_diff s ht
    have h2 : μ s * μ t + μ s * μ tᶜ = μ s := by
      rw [← mul_add, measure_add_measure_compl ht, measure_univ, mul_one]
    have h3 : μ (s ∩ t) + μ (s ∩ tᶜ) = μ (s ∩ t) + μ s * μ tᶜ := by
      rw [h1, hprod]
      exact h2.symm
    exact (ENNReal.add_right_inj (measure_ne_top μ _)).1 h3
  has_iUnion_nat := by
    rintro f hdisj hf
    have hfm : ∀ i, MeasurableSet (f i) := fun i => (hf i).1
    refine ⟨MeasurableSet.iUnion hfm, ?_⟩
    have hdisj' : Pairwise (Function.onFun Disjoint fun i => s ∩ f i) := fun i j hij =>
      (hdisj hij).mono Set.inter_subset_right Set.inter_subset_right
    calc μ (s ∩ ⋃ i, f i) = μ (⋃ i, s ∩ f i) := by rw [Set.inter_iUnion]
      _ = ∑' i, μ (s ∩ f i) := measure_iUnion hdisj' fun i => hs.inter (hfm i)
      _ = ∑' i, μ s * μ (f i) := tsum_congr fun i => (hf i).2
      _ = μ s * ∑' i, μ (f i) := ENNReal.tsum_mul_left
      _ = μ s * μ (⋃ i, f i) := by rw [measure_iUnion hdisj hfm]

theorem thm_5_5_lambda_stage {Ω : Type _} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    {s : Set Ω} (hs : MeasurableSet s) {P : Set (Set Ω)} (hP : IsPiSystem P)
    (hPmeas : ∀ u ∈ P, MeasurableSet u)
    (hPprod : ∀ u ∈ P, μ (s ∩ u) = μ s * μ u) :
    ∀ t, MeasurableSet[MeasurableSpace.generateFrom P] t → μ (s ∩ t) = μ s * μ t :=
  fun t ht =>
    (thm_3_7 (L := productIdentityDynkin μ hs) hP
      (fun u hu => ⟨hPmeas u hu, hPprod u hu⟩) t ht).2

theorem thm_5_5 {Ω : Type _} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsZeroOrProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (C : Set (Set ℝ)) (hpi : IsPiSystem C)
    (hgen : borel ℝ = MeasurableSpace.generateFrom C)
    (hindep : ∀ A B, A ∈ C → B ∈ C → ProbabilityTheory.IndepSet (X ⁻¹' A) (Y ⁻¹' B) μ) :
    ProbabilityTheory.IndepFun X Y μ := by
  refine (ProbabilityTheory.IndepFun_iff_Indep X Y μ).2 ?_
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμP
  · -- Degenerate zero-measure case: every product identity is `0 = 0`.
    rw [ProbabilityTheory.Indep_iff]
    intro t1 t2 _ _
    simp
  · haveI := hμP
    let πX : Set (Set Ω) := Set.preimage X '' C
    let πY : Set (Set Ω) := Set.preimage Y '' C
    have hC_meas : ∀ A, A ∈ C → MeasurableSet A := by
      intro A hA
      have : @MeasurableSet ℝ (borel ℝ) A := by
        rw [hgen]
        exact MeasurableSpace.measurableSet_generateFrom hA
      simpa using this
    have hπX_meas : ∀ s ∈ πX, MeasurableSet s := by
      intro s hs
      rcases hs with ⟨A, hA, rfl⟩
      exact hX (hC_meas A hA)
    have hπY_meas : ∀ t ∈ πY, MeasurableSet t := by
      intro t ht
      rcases ht with ⟨B, hB, rfl⟩
      exact hY (hC_meas B hB)
    have hπX_pi : IsPiSystem πX := by
      rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hne
      rcases hne with ⟨ω, hωA, hωB⟩
      exact ⟨A ∩ B, hpi A hA B hB ⟨X ω, hωA, hωB⟩, rfl⟩
    have hπY_pi : IsPiSystem πY := by
      rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hne
      rcases hne with ⟨ω, hωA, hωB⟩
      exact ⟨A ∩ B, hpi A hA B hB ⟨Y ω, hωA, hωB⟩, rfl⟩
    have hπX_gen : MeasurableSpace.comap X (borel ℝ) = MeasurableSpace.generateFrom πX := by
      rw [hgen, MeasurableSpace.comap_generateFrom]
    have hπY_gen : MeasurableSpace.comap Y (borel ℝ) = MeasurableSpace.generateFrom πY := by
      rw [hgen, MeasurableSpace.comap_generateFrom]
    -- Source stage 1: fix a generator event `s ∈ πX`.  The events satisfying the
    -- product identity with `s` form the λ-system `productIdentityDynkin`, which
    -- contains `πY` by the `hindep` hypothesis; Theorem 3.7 (π-λ) extends the
    -- identity from `πY` to all of `σ(πY)`.
    have stage1 : ∀ s ∈ πX, ∀ t, MeasurableSet[MeasurableSpace.comap Y (borel ℝ)] t →
        μ (s ∩ t) = μ s * μ t := by
      rintro s hsX t ht
      rw [hπY_gen] at ht
      refine thm_5_5_lambda_stage μ (hπX_meas s hsX) hπY_pi hπY_meas ?_ t ht
      rintro u ⟨B, hB, rfl⟩
      obtain ⟨A, hA, rfl⟩ := hsX
      exact
        (ProbabilityTheory.indepSet_iff_measure_inter_eq_mul
          (hπX_meas _ ⟨A, hA, rfl⟩) (hπY_meas _ ⟨B, hB, rfl⟩) (μ := μ)).1
          (hindep A B hA hB)
    -- Source stage 2: fix an arbitrary event `t ∈ σ(πY)`.  By stage 1 the events
    -- satisfying the product identity with `t` include all of `πX`; they again
    -- form the λ-system `productIdentityDynkin`, so Theorem 3.7 extends the
    -- identity from `πX` to all of `σ(πX)`.
    have stage2 : ∀ t, MeasurableSet[MeasurableSpace.comap Y (borel ℝ)] t →
        ∀ s, MeasurableSet[MeasurableSpace.comap X (borel ℝ)] s →
        μ (s ∩ t) = μ s * μ t := by
      intro t ht s hs
      have hcomap_le : MeasurableSpace.comap Y (borel ℝ) ≤ ‹MeasurableSpace Ω› := by
        rw [← BorelSpace.measurable_eq (α := ℝ)]
        exact hY.comap_le
      have htm : MeasurableSet t := hcomap_le t ht
      rw [hπX_gen] at hs
      have h := thm_5_5_lambda_stage μ htm hπX_pi hπX_meas
        (fun u hu => by rw [Set.inter_comm, mul_comm]; exact stage1 u hu t ht) s hs
      rw [Set.inter_comm s t, mul_comm (μ s)]
      exact h
    rw [ProbabilityTheory.Indep_iff]
    intro t1 t2 h1 h2
    exact stage2 t2 h2 t1 h1

theorem thm_5_5_of_piSystem {Ω : Type _} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsZeroOrProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (C : Set (Set ℝ)) (hpi : PiSystem C)
    (hgen : borel ℝ = MeasurableSpace.generateFrom C)
    (hindep : ∀ A B, A ∈ C → B ∈ C → ProbabilityTheory.IndepSet (X ⁻¹' A) (Y ⁻¹' B) μ) :
    ProbabilityTheory.IndepFun X Y μ :=
  thm_5_5 μ X Y hX hY C (piSystem_isPiSystem hpi) hgen hindep
