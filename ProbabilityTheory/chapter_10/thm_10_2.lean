/-
TASK ID: thm_10_2
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter10-almost-sure-probability
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_10.thm_10_1
import ProbabilityTheory.chapter_10.def_10_2




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set



private theorem convergesInProbability_of_tail_null {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXn : ∀ n : ℕ, Measurable (Xn n)) (hX : Measurable X)
    (hAS : ConvergesAlmostSurely μ Xn X) :
    ConvergesInProbability μ Xn X := by
  refine ⟨hXn, hX, ?_⟩
  intro ε hε
  let A : ℕ → Set Ω := fun n => deviationEvent Xn X n ε
  let B : ℕ → Set Ω := fun n => {ω : Ω | ∃ m : ℕ, n ≤ m ∧ ω ∈ A m}
  have htail_null : μ (deviationInfinitelyOften Xn X ε) = 0 :=
    ((thm_10_1 μ Xn X).1 hAS).2.2 ε hε
  have hX_ae : AEStronglyMeasurable X μ := hX.aestronglyMeasurable
  have hA_null : ∀ n, NullMeasurableSet (A n) μ := by
    intro n
    have hdiff : AEStronglyMeasurable (fun ω => Xn n ω - X ω) μ :=
      (hXn n).aestronglyMeasurable.sub hX_ae
    have habs : AEStronglyMeasurable (fun ω => |Xn n ω - X ω|) μ := by
      simpa [Real.norm_eq_abs] using hdiff.norm
    simpa [A, deviationEvent] using
      (AEStronglyMeasurable.nullMeasurableSet_lt
        (stronglyMeasurable_const.aestronglyMeasurable :
          AEStronglyMeasurable (fun _ : Ω => ε) μ)
        habs)
  have hB_null : ∀ n, NullMeasurableSet (B n) μ := by
    intro n
    have hB_eq : B n = ⋃ m : ℕ, if n ≤ m then A m else ∅ := by
      ext ω
      simp [B]
    rw [hB_eq]
    exact NullMeasurableSet.iUnion fun m => by
      by_cases hnm : n ≤ m
      · simpa [hnm] using hA_null m
      · simp [hnm]
  have hB_anti : Antitone B := by
    intro n k hnk ω hω
    rcases hω with ⟨m, hm, hAm⟩
    exact ⟨m, le_trans hnk hm, hAm⟩
  have hInter_eq : {ω : Ω | ∀ n : ℕ, ω ∈ B n} = deviationInfinitelyOften Xn X ε := by
    ext ω
    constructor
    · intro h
      rw [deviationInfinitelyOften, mem_limsup_iff_frequently_mem]
      rw [frequently_atTop]
      intro n
      have hn : ω ∈ B n := by exact h n
      rcases hn with ⟨m, hnm, hAm⟩
      exact ⟨m, hnm, by
        simpa [A, deviationEvent, almostSureDeviationEvent] using hAm⟩
    · intro h
      rw [deviationInfinitelyOften, mem_limsup_iff_frequently_mem] at h
      rw [frequently_atTop] at h
      intro n
      rcases h n with ⟨m, hnm, hAm⟩
      exact ⟨m, hnm, by
        simpa [A, deviationEvent, almostSureDeviationEvent] using hAm⟩
  have hB_tendsto :
      Tendsto (fun n : ℕ => μ (B n)) atTop (nhds 0) := by
    have hcont :=
      tendsto_measure_iInter_atTop (μ := μ) (s := B) hB_null hB_anti
        ⟨0, measure_ne_top μ (B 0)⟩
    have hSetEq : (⋂ n : ℕ, B n) = deviationInfinitelyOften Xn X ε := by
      rw [← hInter_eq]
      ext ω
      simp only [mem_iInter, mem_setOf_eq]
    rw [hSetEq, htail_null] at hcont
    change Tendsto (μ ∘ B) atTop (nhds 0)
    exact hcont
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB_tendsto
    (fun _ => zero_le) ?_
  intro n
  exact measure_mono (by
    intro ω hω
    exact ⟨n, le_rfl, hω⟩)

 
theorem thm_10_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXn : ∀ n : ℕ, Measurable (Xn n)) (hX : Measurable X)
    (hAS : ConvergesAlmostSurely μ Xn X) :
    ConvergesInProbability μ Xn X := by
  exact convergesInProbability_of_tail_null μ Xn X hXn hX hAS
