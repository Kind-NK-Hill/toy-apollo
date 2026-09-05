/-
TASK ID: prob_12_2
TYPE: Problem
SOURCE PLAN: chapter12-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_12.def_12_2
import ProbabilityTheory.chapter_12.def_12_3
import ProbabilityTheory.chapter_12.thm_12_1
import ProbabilityTheory.chapter_12.thm_12_2




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology InnerProductSpace



theorem prob_12_2_norm_difference_bound {E : Type*} [NormedAddCommGroup E]
    (X Y : E) :
    |‖X‖ - ‖Y‖| ≤ ‖X - Y‖ :=
  abs_norm_sub_norm_le X Y



theorem prob_12_2_a {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {Xseq : ℕ → E} {X : E}
    (hX : Tendsto (fun k => ‖Xseq k - X‖) atTop (𝓝 0)) :
    Tendsto (fun k => ‖Xseq k‖) atTop (𝓝 ‖X‖) := by
  have hXseq : Tendsto Xseq atTop (𝓝 X) :=
    tendsto_iff_norm_sub_tendsto_zero.2 hX
  exact tendsto_norm.comp hXseq



theorem prob_12_2_a_textbook {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {Xseq : ℕ → E} {X : E}
    (hX : Tendsto (fun k => ‖Xseq k - X‖) atTop (𝓝 0)) :
    TextbookConvergentSequence (fun k => (‖Xseq k‖ : ℝ)) :=
  textbookConvergentSequence_of_tendsto (prob_12_2_a (𝕜 := 𝕜) hX)



theorem prob_12_2_b {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {Xseq : ℕ → E}
    (hX : TextbookCauchySequence Xseq) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, ‖Xseq k‖ ≤ M := by
  rcases hX 1 (by norm_num) with ⟨N, hN⟩
  let initial : ℝ := (Finset.range N).sum (fun k => ‖Xseq k‖)
  let M : ℝ := initial + ‖Xseq N‖ + 1
  have h_initial_nonneg : 0 ≤ initial := by
    exact Finset.sum_nonneg fun k _ => norm_nonneg (Xseq k)
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  refine ⟨M, hM_nonneg, ?_⟩
  intro k
  by_cases hk : k < N
  · have hk_mem : k ∈ Finset.range N := Finset.mem_range.mpr hk
    have hk_initial : ‖Xseq k‖ ≤ initial := by
      exact Finset.single_le_sum (fun i _ => norm_nonneg (Xseq i)) hk_mem
    calc
      ‖Xseq k‖ ≤ initial := hk_initial
      _ ≤ M := by
        dsimp [M]
        linarith [norm_nonneg (Xseq N)]
  · have hkN : N ≤ k := le_of_not_gt hk
    have htail : ‖Xseq k - Xseq N‖ ≤ 1 := hN k N hkN le_rfl
    have htri : ‖Xseq k‖ ≤ ‖Xseq k - Xseq N‖ + ‖Xseq N‖ := by
      calc
        ‖Xseq k‖ = ‖(Xseq k - Xseq N) + Xseq N‖ := by
          rw [sub_add_cancel]
        _ ≤ ‖Xseq k - Xseq N‖ + ‖Xseq N‖ :=
          thm_12_2 (𝕜 := 𝕜) (Xseq k - Xseq N) (Xseq N)
    calc
      ‖Xseq k‖ ≤ ‖Xseq k - Xseq N‖ + ‖Xseq N‖ := htri
      _ ≤ 1 + ‖Xseq N‖ := by linarith
      _ ≤ M := by
        dsimp [M]
        linarith [h_initial_nonneg]



theorem prob_12_2_b_of_cauchySeq {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {Xseq : ℕ → E}
    (hX : CauchySeq Xseq) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, ‖Xseq k‖ ≤ M :=
  prob_12_2_b (𝕜 := 𝕜) (textbookCauchySequence_of_cauchySeq hX)



theorem prob_12_2_c {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {Xseq : ℕ → E} {X : E}
    (hCauchy : TextbookCauchySequence Xseq)
    (hConv : Tendsto (fun k => ‖Xseq k - X‖) atTop (𝓝 0)) :
    ∃ M : ℝ, 0 ≤ M ∧ ‖X‖ ≤ M := by
  rcases prob_12_2_b (𝕜 := 𝕜) hCauchy with ⟨M, hM_nonneg, hM⟩
  have hnorm : Tendsto (fun k => ‖Xseq k‖) atTop (𝓝 ‖X‖) :=
    prob_12_2_a (𝕜 := 𝕜) hConv
  refine ⟨M, hM_nonneg, ?_⟩
  exact le_of_tendsto_of_tendsto' hnorm tendsto_const_nhds hM

 
theorem prob_12_2 {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (Xseq : ℕ → E) (X : E) :
    (Tendsto (fun k => ‖Xseq k - X‖) atTop (𝓝 0) →
      Tendsto (fun k => ‖Xseq k‖) atTop (𝓝 ‖X‖)) ∧
    (TextbookCauchySequence Xseq →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, ‖Xseq k‖ ≤ M) ∧
    (TextbookCauchySequence Xseq →
      Tendsto (fun k => ‖Xseq k - X‖) atTop (𝓝 0) →
        ∃ M : ℝ, 0 ≤ M ∧ ‖X‖ ≤ M) := by
  exact ⟨fun h => prob_12_2_a (𝕜 := 𝕜) h,
    ⟨fun h => prob_12_2_b (𝕜 := 𝕜) h,
      fun hC hT => prob_12_2_c (𝕜 := 𝕜) hC hT⟩⟩

 
theorem prob_12_2_l2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Xseq : ℕ → Ω →₂[P] ℝ) (X : Ω →₂[P] ℝ) :
    (Tendsto (fun k => ‖Xseq k - X‖) atTop (𝓝 0) →
      Tendsto (fun k => ‖Xseq k‖) atTop (𝓝 ‖X‖)) ∧
    (TextbookCauchySequence Xseq →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, ‖Xseq k‖ ≤ M) ∧
    (TextbookCauchySequence Xseq →
      Tendsto (fun k => ‖Xseq k - X‖) atTop (𝓝 0) →
        ∃ M : ℝ, 0 ≤ M ∧ ‖X‖ ≤ M) :=
  prob_12_2 (𝕜 := ℝ) Xseq X
