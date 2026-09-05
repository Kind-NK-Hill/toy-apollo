/-
TASK ID: thm_10_1
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter10-almost-sure-probability
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_10.def_10_1




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set

 
def almostSureDeviationEvent {Ω : Type*} (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (n : ℕ)
    (ε : ℝ) : Set Ω :=
  {ω : Ω | |Xn n ω - X ω| > ε}

 
def deviationInfinitelyOften {Ω : Type*} (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (ε : ℝ) :
    Set Ω :=
  limsup (fun n : ℕ => almostSureDeviationEvent Xn X n ε) atTop

private lemma not_mem_deviationInfinitelyOften_of_tendsto {Ω : Type*}
    {Xn : ℕ → Ω → ℝ} {X : Ω → ℝ} {ω : Ω} {ε : ℝ} (hε : 0 < ε)
    (hω : Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))) :
    ω ∉ deviationInfinitelyOften Xn X ε := by
  rw [deviationInfinitelyOften, mem_limsup_iff_frequently_mem]
  refine Filter.not_frequently.2 ?_
  rcases (Metric.tendsto_atTop.mp hω) ε hε with ⟨N, hN⟩
  refine eventually_atTop.2 ⟨N, ?_⟩
  intro n hn
  have hdist : dist (Xn n ω) (X ω) < ε := hN n hn
  have habs : |Xn n ω - X ω| < ε := by
    simpa [Real.dist_eq] using hdist
  exact not_lt.mpr habs.le

private lemma tendsto_of_not_mem_deviationInfinitelyOften_all {Ω : Type*}
    {Xn : ℕ → Ω → ℝ} {X : Ω → ℝ} {ω : Ω}
    (hω : ∀ k : ℕ, ω ∉ deviationInfinitelyOften Xn X (1 / ((k : ℝ) + 1))) :
    Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω)) := by
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  rcases Real.exists_nat_pos_inv_lt hε with ⟨k, hk_pos, hk_lt⟩
  have hk_cast_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk_pos
  have hthreshold_lt : 1 / ((k : ℝ) + 1) < ε := by
    calc
      1 / ((k : ℝ) + 1) < (k : ℝ)⁻¹ := by
        simpa [one_div] using one_div_lt_one_div_of_lt hk_cast_pos (lt_add_one (k : ℝ))
      _ < ε := hk_lt
  have hnfreq : ¬ ∃ᶠ n : ℕ in atTop,
      ω ∈ almostSureDeviationEvent Xn X n (1 / ((k : ℝ) + 1)) := by
    intro hfreq
    exact hω k (mem_limsup_iff_frequently_mem.2 hfreq)
  have hev : ∀ᶠ n : ℕ in atTop,
      ¬ ω ∈ almostSureDeviationEvent Xn X n (1 / ((k : ℝ) + 1)) :=
    Filter.not_frequently.1 hnfreq
  rcases eventually_atTop.1 hev with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hnot := hN n hn
  have hle : |Xn n ω - X ω| ≤ 1 / ((k : ℝ) + 1) := by
    exact not_lt.1 hnot
  calc
    dist (Xn n ω) (X ω) = |Xn n ω - X ω| := by simp [Real.dist_eq]
    _ ≤ 1 / ((k : ℝ) + 1) := hle
    _ < ε := hthreshold_lt



theorem thm_10_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) :
    ConvergesAlmostSurely μ Xn X ↔
      (∀ n : ℕ, AEStronglyMeasurable (Xn n) μ) ∧
        AEStronglyMeasurable X μ ∧
          ∀ ε : ℝ, 0 < ε → μ (deviationInfinitelyOften Xn X ε) = 0 := by
  constructor
  · rintro ⟨hXn, hX, has⟩
    refine ⟨hXn, hX, ?_⟩
    intro ε hε
    have hbad : μ {ω : Ω | ¬ Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))} = 0 :=
      ae_iff.1 has
    refine MeasureTheory.measure_mono_null ?_ hbad
    intro ω hω hconv
    exact not_mem_deviationInfinitelyOften_of_tendsto hε hconv hω
  · rintro ⟨hXn, hX, hio⟩
    refine ⟨hXn, hX, ae_iff.2 ?_⟩
    have hbad_subset :
        {ω : Ω | ¬ Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))} ⊆
          ⋃ k : ℕ, deviationInfinitelyOften Xn X (1 / ((k : ℝ) + 1)) := by
      intro ω hω_bad
      by_contra hnot
      have hnot_each :
          ∀ k : ℕ, ω ∉ deviationInfinitelyOften Xn X (1 / ((k : ℝ) + 1)) := by
        intro k hk
        exact hnot (mem_iUnion.2 ⟨k, hk⟩)
      exact hω_bad (tendsto_of_not_mem_deviationInfinitelyOften_all hnot_each)
    refine MeasureTheory.measure_mono_null hbad_subset ?_
    refine MeasureTheory.measure_iUnion_null ?_
    intro k
    have hk_pos : 0 < (1 / ((k : ℝ) + 1) : ℝ) := by positivity
    exact hio (1 / ((k : ℝ) + 1)) hk_pos
