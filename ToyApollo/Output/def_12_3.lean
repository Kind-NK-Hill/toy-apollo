/-
TASK ID: def_12_3
TYPE: Definition
SOURCE PLAN: chapter12-l2-norm-inner-product
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open Filter
open scoped Topology

def TextbookCauchySequence {E : Type*} [NormedAddCommGroup E] (u : ℕ → E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
    ∀ m n : ℕ, N ≤ m → N ≤ n → ‖u m - u n‖ ≤ ε

def TextbookConvergentSequence {E : Type*} [NormedAddCommGroup E] (u : ℕ → E) : Prop :=
  ∃ u0 : E, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n → ‖u n - u0‖ ≤ ε

theorem textbookCauchySequence_of_cauchySeq {E : Type*} [NormedAddCommGroup E]
    {u : ℕ → E} (hu : CauchySeq u) : TextbookCauchySequence u := by
  intro ε hε
  rcases (Metric.cauchySeq_iff.mp hu ε hε) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m n hm hn
  simpa [dist_eq_norm] using le_of_lt (hN m hm n hn)

theorem textbookConvergentSequence_of_tendsto {E : Type*} [NormedAddCommGroup E]
    {u : ℕ → E} {u0 : E} (hu : Tendsto u atTop (𝓝 u0)) :
    TextbookConvergentSequence u := by
  refine ⟨u0, ?_⟩
  intro ε hε
  rcases (Metric.tendsto_atTop.mp hu ε hε) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  simpa [dist_eq_norm] using le_of_lt (hN n hn)

theorem cauchySeq_of_textbookCauchySequence {E : Type*} [NormedAddCommGroup E]
    {u : ℕ → E} (hu : TextbookCauchySequence u) : CauchySeq u := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rcases hu (ε / 2) hε2 with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hle : ‖u m - u n‖ ≤ ε / 2 := hN m n hm hn
  simpa [dist_eq_norm] using (lt_of_le_of_lt hle (by linarith))

theorem every_textbookCauchySequence_converges_of_complete {E : Type*}
    [NormedAddCommGroup E] (hComplete : CompleteSpace E) :
    ∀ u : ℕ → E, TextbookCauchySequence u → TextbookConvergentSequence u := by
  let _ : CompleteSpace E := hComplete
  intro u hu
  have hCauchy : CauchySeq u := cauchySeq_of_textbookCauchySequence hu
  rcases cauchySeq_tendsto_of_complete hCauchy with ⟨u0, hlim⟩
  exact textbookConvergentSequence_of_tendsto hlim

class TextbookCompleteSpace (E : Type*) [NormedAddCommGroup E] : Prop where
  completeSpace : CompleteSpace E
  textbook_convergent :
    ∀ u : ℕ → E, TextbookCauchySequence u → TextbookConvergentSequence u

instance textbookCompleteSpace_of_complete {E : Type*} [NormedAddCommGroup E]
    [hComplete : CompleteSpace E] : TextbookCompleteSpace E where
  completeSpace := hComplete
  textbook_convergent :=
    every_textbookCauchySequence_converges_of_complete hComplete

theorem textbookCompleteSpace_iff_complete (E : Type*) [NormedAddCommGroup E] :
    TextbookCompleteSpace E ↔ CompleteSpace E := by
  constructor
  · intro h
    exact h.completeSpace
  · intro h
    exact
      { completeSpace := h
        textbook_convergent := every_textbookCauchySequence_converges_of_complete h }

def TextbookHilbertSpace (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] : Prop :=
  TextbookCompleteSpace E

theorem textbookHilbertSpace_iff_complete (𝕜 E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] :
    TextbookHilbertSpace 𝕜 E ↔ CompleteSpace E :=
  textbookCompleteSpace_iff_complete E

def def_12_3 (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] : Prop :=
  TextbookHilbertSpace 𝕜 E
