import Mathlib
import ToyApollo.Output.def_12_2
import ToyApollo.Output.def_12_3
import ToyApollo.Output.thm_12_1
import ToyApollo.Output.thm_12_2

/-
TASK ID: prob_12_2
TYPE: Problem
SOURCE PLAN: chapter12-problems
TASK CONTENT:
\textbf{12.2.} Consider an inner product space with induced L 2 norm denoted by\cdot 2.

(a) Prove the continuity of the L 2 norm, that is, if (X k)k\geq 1 is a sequence in the

inner product space such that Xk - X2 \to 0f o r s o m e X as n \to\infty , then

limn\to\infty Xk2 = X2.

(b) Let (X k)k\geq 1 be a Cauchy sequence. Show that the L 2 norms of the sequence are

bounded, ie., there exists a real number M such thatXk2 \leqM for all k .

(c) Suppose the Cauchy (X k)k\geq 1 in part (b) converges to X in L 2 norm. Prove that

X2 is finite.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology InnerProductSpace

/-- The reverse triangle inequality is the estimate behind norm continuity:
changing a vector by a small amount changes its norm by at most that amount. -/
theorem prob_12_2_norm_difference_bound {E : Type*} [NormedAddCommGroup E]
    (X Y : E) :
    |‖X‖ - ‖Y‖| ≤ ‖X - Y‖ :=
  abs_norm_sub_norm_le X Y

/-- Problem 12.2(a): convergence in the induced `L²` norm implies convergence
of the corresponding norm values. -/
theorem prob_12_2_a {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {Xseq : ℕ → E} {X : E}
    (hX : Tendsto (fun k => ‖Xseq k - X‖) atTop (𝓝 0)) :
    Tendsto (fun k => ‖Xseq k‖) atTop (𝓝 ‖X‖) := by
  have hXseq : Tendsto Xseq atTop (𝓝 X) :=
    tendsto_iff_norm_sub_tendsto_zero.2 hX
  exact tendsto_norm.comp hXseq

/-- The same continuity statement, using the textbook epsilon convergence
definition from Definition 12.3. -/
theorem prob_12_2_a_textbook {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {Xseq : ℕ → E} {X : E}
    (hX : Tendsto (fun k => ‖Xseq k - X‖) atTop (𝓝 0)) :
    TextbookConvergentSequence (fun k => (‖Xseq k‖ : ℝ)) :=
  textbookConvergentSequence_of_tendsto (prob_12_2_a (𝕜 := 𝕜) hX)

/-- Problem 12.2(b): a textbook Cauchy sequence has bounded `L²` norms.  The
tail is controlled by Minkowski, and the finite initial segment is controlled by
a finite sum of norms. -/
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

/-- Mathlib Cauchy sequences satisfy the same bounded-norm conclusion, via the
local textbook Cauchy interface from Definition 12.3. -/
theorem prob_12_2_b_of_cauchySeq {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {Xseq : ℕ → E}
    (hX : CauchySeq Xseq) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, ‖Xseq k‖ ≤ M :=
  prob_12_2_b (𝕜 := 𝕜) (textbookCauchySequence_of_cauchySeq hX)

/-- Problem 12.2(c): if the Cauchy sequence converges in `L²` norm to `X`, then
the limiting `L²` norm is bounded by the same kind of finite real bound. -/
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

/-- The combined statement of Problem 12.2. -/
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

/-- Problem 12.2 specialized to the real `L²(P)` quotient of random variables. -/
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
