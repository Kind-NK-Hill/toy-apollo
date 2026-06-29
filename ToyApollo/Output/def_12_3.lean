import Mathlib

/-
TASK ID: def_12_3
TYPE: Definition
SOURCE PLAN: chapter12-l2-norm-inner-product
TASK CONTENT:
\begin{defbox}{12.3}
\end{defbox}

A sequence of vectors (un)\infty

n=1 in a vector space V with a norm function \cdot is

called a Cauchy sequence if given any \epsilon> 0, there exists an integer N such that

um - un\leq \epsilon for all m, n \geq N. We say that a sequence of vectors (un)\infty

n=1 is

convergent if there exists a vector u0 \in V such that for any given \epsilon> 0, there is

an integer N such that un - u0\leq \epsilonfor all n \geq N .

A normed vector space V is said to be complete if every Cauchy sequence in V is

convergent. A Hilbert space is a (real or complex) vector space that is complete

with respect to the norm induced by the inner product.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter
open scoped Topology

/-- Textbook epsilon definition of a Cauchy sequence in a normed vector space. -/
def TextbookCauchySequence {E : Type*} [NormedAddCommGroup E] (u : ℕ → E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
    ∀ m n : ℕ, N ≤ m → N ≤ n → ‖u m - u n‖ ≤ ε

/-- Textbook epsilon definition of convergence in a normed vector space. -/
def TextbookConvergentSequence {E : Type*} [NormedAddCommGroup E] (u : ℕ → E) : Prop :=
  ∃ u0 : E, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n → ‖u n - u0‖ ≤ ε

/-- Mathlib Cauchy sequences imply the textbook epsilon-Cauchy condition. -/
theorem textbookCauchySequence_of_cauchySeq {E : Type*} [NormedAddCommGroup E]
    {u : ℕ → E} (hu : CauchySeq u) : TextbookCauchySequence u := by
  intro ε hε
  rcases (Metric.cauchySeq_iff.mp hu ε hε) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m n hm hn
  simpa [dist_eq_norm] using le_of_lt (hN m hm n hn)

/-- Mathlib convergence implies the textbook epsilon convergence condition. -/
theorem textbookConvergentSequence_of_tendsto {E : Type*} [NormedAddCommGroup E]
    {u : ℕ → E} {u0 : E} (hu : Tendsto u atTop (𝓝 u0)) :
    TextbookConvergentSequence u := by
  refine ⟨u0, ?_⟩
  intro ε hε
  rcases (Metric.tendsto_atTop.mp hu ε hε) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  simpa [dist_eq_norm] using le_of_lt (hN n hn)

/-- Textbook epsilon-Cauchy sequences are Mathlib Cauchy sequences. -/
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

/-- Mathlib completeness supplies the textbook statement that every textbook
Cauchy sequence converges in the textbook epsilon sense. -/
theorem every_textbookCauchySequence_converges_of_complete {E : Type*}
    [NormedAddCommGroup E] (hComplete : CompleteSpace E) :
    ∀ u : ℕ → E, TextbookCauchySequence u → TextbookConvergentSequence u := by
  let _ : CompleteSpace E := hComplete
  intro u hu
  have hCauchy : CauchySeq u := cauchySeq_of_textbookCauchySequence hu
  rcases cauchySeq_tendsto_of_complete hCauchy with ⟨u0, hlim⟩
  exact textbookConvergentSequence_of_tendsto hlim

/-- Textbook completeness for normed spaces: the Mathlib complete-space
structure together with its reusable epsilon-sequence reading.  This is a class
so older downstream theorem statements that used `infer_instance` remain
compatible while the textbook sequence clause stays public. -/
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

/-- A textbook Hilbert space is an inner product space complete in its induced
norm. -/
def TextbookHilbertSpace (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] : Prop :=
  TextbookCompleteSpace E

theorem textbookHilbertSpace_iff_complete (𝕜 E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] :
    TextbookHilbertSpace 𝕜 E ↔ CompleteSpace E :=
  textbookCompleteSpace_iff_complete E

/-- Exported definition for Definition 12.3: the Hilbert-space condition. -/
def def_12_3 (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] : Prop :=
  TextbookHilbertSpace 𝕜 E
