/-
TASK ID: ex_12_2_1
TYPE: Example_Proof
SOURCE PLAN: chapter12-closed-subspace-projection
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.ex_12_1_2

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory
open Filter

open scoped BigOperators Topology

noncomputable section

def ex_12_2_1_W : Set (ex_12_1_2_space → ℂ) :=
  {X | (Function.support X).Finite}

theorem ex_12_2_1_zero_mem :
    (fun _ : ex_12_1_2_space => (0 : ℂ)) ∈ ex_12_2_1_W := by
  simp [ex_12_2_1_W]

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

def ex_12_2_1_partialOnes (k : ℕ) : ex_12_1_2_space → ℂ :=
  fun n => if n < k then 1 else 0

def ex_12_2_1_allOnes : ex_12_1_2_space → ℂ :=
  fun _ => 1

theorem ex_12_2_1_partialOnes_mem (k : ℕ) :
    ex_12_2_1_partialOnes k ∈ ex_12_2_1_W := by
  refine (Finset.range k).finite_toSet.subset ?_
  intro n hn
  by_cases hnk : n < k
  · exact Finset.mem_range.mpr hnk
  · simp [ex_12_2_1_partialOnes, Function.mem_support, hnk] at hn

theorem ex_12_2_1_allOnes_not_mem :
    ex_12_2_1_allOnes ∉ ex_12_2_1_W := by
  intro h
  have hsupport : (Function.support ex_12_2_1_allOnes).Finite := by
    simpa [ex_12_2_1_W] using h
  have hfinite_univ : (Set.univ : Set ex_12_1_2_space).Finite := by
    simpa [ex_12_2_1_allOnes, Function.support] using hsupport
  exact Set.infinite_univ hfinite_univ

theorem ex_12_2_1_allOnes_L2Series :
    ex_12_1_2_L2Series ex_12_2_1_allOnes := by
  unfold ex_12_1_2_L2Series
  exact (summable_geometric_two' (1 : ℝ)).congr fun n => by
    rw [ex_12_1_2_realWeight_eq]
    simp [ex_12_2_1_allOnes, pow_succ, div_eq_mul_inv]

def ex_12_2_1_tailError (k : ℕ) : ℝ :=
  ((2 : ℝ) ^ k)⁻¹

def ex_12_2_1_L2Error (k : ℕ) : ℝ :=
  ∑' n : ex_12_1_2_space,
    ex_12_1_2_realWeight n *
      ‖ex_12_2_1_partialOnes k n - ex_12_2_1_allOnes n‖ ^ 2

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

def ex_12_2_1_L2SequentialClosure
    (S : Set (ex_12_1_2_space → ℂ)) (X : ex_12_1_2_space → ℂ) : Prop :=
  ∃ A : ℕ → ex_12_1_2_space → ℂ,
    (∀ k, A k ∈ S) ∧
      Tendsto
        (fun k =>
          ∑' n : ex_12_1_2_space,
            ex_12_1_2_realWeight n * ‖A k n - X n‖ ^ 2)
        atTop (nhds 0)

def ex_12_2_1_L2SequentiallyClosed
    (S : Set (ex_12_1_2_space → ℂ)) : Prop :=
  ∀ X, ex_12_2_1_L2SequentialClosure S X → X ∈ S

theorem ex_12_2_1_allOnes_mem_L2SequentialClosure :
    ex_12_2_1_L2SequentialClosure ex_12_2_1_W ex_12_2_1_allOnes := by
  refine ⟨ex_12_2_1_partialOnes, ex_12_2_1_partialOnes_mem, ?_⟩
  exact ex_12_2_1_L2Error_tendsto_zero

theorem ex_12_2_1_W_not_L2SequentiallyClosed :
    ¬ ex_12_2_1_L2SequentiallyClosed ex_12_2_1_W := by
  intro hclosed
  exact ex_12_2_1_allOnes_not_mem
    (hclosed ex_12_2_1_allOnes ex_12_2_1_allOnes_mem_L2SequentialClosure)

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
