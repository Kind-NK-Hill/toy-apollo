import Mathlib
import ToyApollo.Output.ex_12_1_2

/-
TASK ID: ex_12_2_1
TYPE: Example_Proof
SOURCE PLAN: chapter12-closed-subspace-projection
TASK CONTENT:
\textbf{Example 12.2.1 (An Example of Subspace that Is Not Closed)} \\

In Example 12.1.2,w el e t W denote the subset of infinite sequences .(x1,x 2,x 3,... ) in which only

finitely many components are nonzero. This is a vector space because it is closed under addition

and scalar multiplication.

However, this subspace is not closed because

Xk \coloneqq(1, 1, 1,..., 1,

k ones

0, 0, 0,...,)

converges to an infinite sequence that contains infinitely many 1's, as k \to\infty , which is not in the

subspace.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory
open Filter

open scoped BigOperators Topology

noncomputable section

/-- The subspace `W` from Example 12.2.1: complex sequences with finite
support. -/
def ex_12_2_1_W : Set (ex_12_1_2_space → ℂ) :=
  {X | (Function.support X).Finite}

/-- `W` contains the zero sequence. -/
theorem ex_12_2_1_zero_mem :
    (fun _ : ex_12_1_2_space => (0 : ℂ)) ∈ ex_12_2_1_W := by
  simp [ex_12_2_1_W]

/-- Finite-support sequences are closed under complex linear combinations. -/
theorem ex_12_2_1_linear_combination
    {X Y : ex_12_1_2_space → ℂ}
    (hX : X ∈ ex_12_2_1_W) (hY : Y ∈ ex_12_2_1_W)
    (α β : ℂ) :
    (fun n => α * X n + β * Y n) ∈ ex_12_2_1_W := by
  rcases hX with hX
  rcases hY with hY
  refine (hX.union hY).subset ?_
  intro n hn
  by_contra hnmem
  have hnXnot : n ∉ Function.support X := fun hx => hnmem (Or.inl hx)
  have hnYnot : n ∉ Function.support Y := fun hy => hnmem (Or.inr hy)
  have hnX : X n = 0 := by
    simpa [Function.mem_support] using
      hnXnot
  have hnY : Y n = 0 := by
    simpa [Function.mem_support] using
      hnYnot
  simp [Function.mem_support, hnX, hnY] at hn

/-- The textbook sequence with `k` initial ones and then zeros. -/
def ex_12_2_1_partialOnes (k : ℕ) : ex_12_1_2_space → ℂ :=
  fun n => if n < k then 1 else 0

/-- The infinite sequence containing only ones. -/
def ex_12_2_1_allOnes : ex_12_1_2_space → ℂ :=
  fun _ => 1

theorem ex_12_2_1_partialOnes_mem (k : ℕ) :
    ex_12_2_1_partialOnes k ∈ ex_12_2_1_W := by
  refine (Finset.range k).finite_toSet.subset ?_
  intro n hn
  by_cases hnk : n < k
  · exact Finset.mem_range.mpr hnk
  · simp [ex_12_2_1_partialOnes, Function.mem_support, hnk] at hn

/-- The all-ones sequence has infinite support, hence is not in `W`. -/
theorem ex_12_2_1_allOnes_not_mem :
    ex_12_2_1_allOnes ∉ ex_12_2_1_W := by
  intro h
  have hsupport : (Function.support ex_12_2_1_allOnes).Finite := by
    simpa [ex_12_2_1_W] using h
  have hfinite_univ : (Set.univ : Set ex_12_1_2_space).Finite := by
    simpa [ex_12_2_1_allOnes, Function.support] using hsupport
  exact Set.infinite_univ hfinite_univ

/-- The all-ones sequence is still an `L²(P)` sequence in Example 12.1.2,
because the geometric weights are summable. -/
theorem ex_12_2_1_allOnes_L2Series :
    ex_12_1_2_L2Series ex_12_2_1_allOnes := by
  unfold ex_12_1_2_L2Series
  exact (summable_geometric_two' (1 : ℝ)).congr fun n => by
    rw [ex_12_1_2_realWeight_eq]
    simp [ex_12_2_1_allOnes, pow_succ, div_eq_mul_inv]

/-- The squared `L²` tail error of the `k`-th truncation is the geometric tail
`2^{-k}`. This tends to zero, which is the convergence mechanism in the source
example. -/
def ex_12_2_1_tailError (k : ℕ) : ℝ :=
  ((2 : ℝ) ^ k)⁻¹

/-- The squared `L²(P)` error between the `k`-th truncation and the all-ones
sequence, written as the weighted square series from Example 12.1.2. -/
def ex_12_2_1_L2Error (k : ℕ) : ℝ :=
  ∑' n : ex_12_1_2_space,
    ex_12_1_2_realWeight n *
      ‖ex_12_2_1_partialOnes k n - ex_12_2_1_allOnes n‖ ^ 2

/-- The textbook geometric-tail computation:
`‖X_k - 1‖²₂ = Σ_{n ≥ k} 2^{-(n+1)} = 2^{-k}`. -/
theorem ex_12_2_1_L2Error_eq_tailError (k : ℕ) :
    ex_12_2_1_L2Error k = ex_12_2_1_tailError k := by
  unfold ex_12_2_1_L2Error
  calc
    (∑' n : ex_12_1_2_space,
        ex_12_1_2_realWeight n *
          ‖ex_12_2_1_partialOnes k n - ex_12_2_1_allOnes n‖ ^ 2)
        = ∑' n : ℕ, if k ≤ n then ((2 : ℝ)⁻¹) ^ (n + 1) else 0 := by
          apply tsum_congr
          intro n
          by_cases hn : n < k
          · have hnot : ¬ k ≤ n := not_le.mpr hn
            rw [if_neg hnot]
            have hpn : ex_12_2_1_partialOnes k n = 1 := by
              simp [ex_12_2_1_partialOnes, hn]
            simp [ex_12_1_2_realWeight_eq, ex_12_2_1_allOnes, hpn]
          · have hle : k ≤ n := le_of_not_gt hn
            rw [if_pos hle]
            have hpn : ex_12_2_1_partialOnes k n = 0 := by
              simp [ex_12_2_1_partialOnes, hn]
            rw [ex_12_1_2_realWeight_eq]
            simp [ex_12_2_1_allOnes, hpn, one_div, inv_pow]
    _ = ∑' n : ℕ, (2 : ℝ)⁻¹ *
          (if k ≤ n then ((2 : ℝ)⁻¹) ^ n else 0) := by
          apply tsum_congr
          intro n
          by_cases h : k ≤ n
          · simp [h, pow_succ, mul_comm]
          · simp [h]
    _ = (2 : ℝ)⁻¹ *
          (∑' n : ℕ, if k ≤ n then ((2 : ℝ)⁻¹) ^ n else 0) := by
          rw [tsum_mul_left]
    _ = (2 : ℝ)⁻¹ * (2 * (2 : ℝ)⁻¹ ^ k) := by
          rw [tsum_geometric_inv_two_ge]
    _ = ex_12_2_1_tailError k := by
          simp [ex_12_2_1_tailError, inv_pow]

theorem ex_12_2_1_tailError_tendsto_zero :
    Tendsto ex_12_2_1_tailError atTop (nhds 0) := by
  simpa [ex_12_2_1_tailError] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by positivity : 0 ≤ (2 : ℝ)⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1))

theorem ex_12_2_1_L2Error_tendsto_zero :
    Tendsto ex_12_2_1_L2Error atTop (nhds 0) := by
  have hfun : ex_12_2_1_L2Error = ex_12_2_1_tailError := by
    funext k
    exact ex_12_2_1_L2Error_eq_tailError k
  rw [hfun]
  exact ex_12_2_1_tailError_tendsto_zero

/-- A point is in the sequential `L²` closure of a set of sequences when it is
the weighted-`L²` limit of a sequence from that set. -/
def ex_12_2_1_L2SequentialClosure
    (S : Set (ex_12_1_2_space → ℂ)) (X : ex_12_1_2_space → ℂ) : Prop :=
  ∃ A : ℕ → ex_12_1_2_space → ℂ,
    (∀ k, A k ∈ S) ∧
      Tendsto
        (fun k =>
          ∑' n : ex_12_1_2_space,
            ex_12_1_2_realWeight n * ‖A k n - X n‖ ^ 2)
        atTop (nhds 0)

/-- Sequential closedness for the weighted-`L²` convergence criterion used in
Example 12.2.1. -/
def ex_12_2_1_L2SequentiallyClosed
    (S : Set (ex_12_1_2_space → ℂ)) : Prop :=
  ∀ X, ex_12_2_1_L2SequentialClosure S X → X ∈ S

/-- The all-ones sequence lies in the `L²` sequential closure of the
finite-support subspace, witnessed by the truncations `Xₖ`. -/
theorem ex_12_2_1_allOnes_mem_L2SequentialClosure :
    ex_12_2_1_L2SequentialClosure ex_12_2_1_W ex_12_2_1_allOnes := by
  refine ⟨ex_12_2_1_partialOnes, ex_12_2_1_partialOnes_mem, ?_⟩
  exact ex_12_2_1_L2Error_tendsto_zero

/-- Therefore the finite-support subspace is not closed for the source
weighted-`L²` convergence criterion. -/
theorem ex_12_2_1_W_not_L2SequentiallyClosed :
    ¬ ex_12_2_1_L2SequentiallyClosed ex_12_2_1_W := by
  intro hclosed
  exact ex_12_2_1_allOnes_not_mem
    (hclosed ex_12_2_1_allOnes ex_12_2_1_allOnes_mem_L2SequentialClosure)

/-- Example 12.2.1: finite-support sequences form a vector subspace, but this
subspace is not closed in the `L²` sequence space from Example 12.1.2. -/
theorem ex_12_2_1 :
    (fun _ : ex_12_1_2_space => (0 : ℂ)) ∈ ex_12_2_1_W ∧
      (∀ X Y, X ∈ ex_12_2_1_W → Y ∈ ex_12_2_1_W → ∀ α β : ℂ,
        (fun n => α * X n + β * Y n) ∈ ex_12_2_1_W) ∧
      (∀ k, ex_12_2_1_partialOnes k ∈ ex_12_2_1_W) ∧
      ex_12_1_2_L2Series ex_12_2_1_allOnes ∧
      ex_12_2_1_allOnes ∉ ex_12_2_1_W ∧
      (∀ k, ex_12_2_1_L2Error k = ex_12_2_1_tailError k) ∧
      Tendsto ex_12_2_1_L2Error atTop (nhds 0) ∧
      ¬ ex_12_2_1_L2SequentiallyClosed ex_12_2_1_W := by
  exact ⟨ex_12_2_1_zero_mem,
    (fun X Y hX hY α β => ex_12_2_1_linear_combination hX hY α β),
    ex_12_2_1_partialOnes_mem,
    ex_12_2_1_allOnes_L2Series,
    ex_12_2_1_allOnes_not_mem,
    ex_12_2_1_L2Error_eq_tailError,
    ex_12_2_1_L2Error_tendsto_zero,
    ex_12_2_1_W_not_L2SequentiallyClosed⟩
