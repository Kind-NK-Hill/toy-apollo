/-
TASK ID: prob_6_1
TYPE: Problem
SOURCE PLAN: 24_chap6_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory BigOperators Finset

lemma binom_weight_nonneg (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (k : Fin (n + 1)) :
    0 ≤ (Nat.choose n k.val : ℝ) * p ^ k.val * (1 - p) ^ (n - k.val) := by
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _))
    (pow_nonneg (sub_nonneg.mpr hp') _)

lemma integral_weighted_dirac_fin {n : ℕ} (f : Fin (n + 1) → ℝ)
    (w : Fin (n + 1) → ℝ) (hw : ∀ k, 0 ≤ w k) :
    ∫ x, f x ∂(∑ k : Fin (n + 1), (ENNReal.ofReal (w k)) • Measure.dirac k) =
      ∑ k : Fin (n + 1), w k * f k := by
  rw [MeasureTheory.integral_finset_sum_measure]
  · simp +decide [MeasureTheory.integral_smul_measure, hw]
  · simp +decide [MeasureTheory.Integrable]
    intro k
    simp +decide [HasFiniteIntegral]
    exact ⟨Measurable.aestronglyMeasurable (by measurability),
      ENNReal.mul_lt_top (by aesop) (by aesop)⟩

lemma binomial_expectation_identity (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    ∑ k : Fin (n + 1),
      (Nat.choose n k.val : ℝ) * p ^ k.val * (1 - p) ^ (n - k.val) * k.val = n * p := by
  have h_sum : ∑ k : Fin (n + 1),
      (Nat.choose n k.val : ℝ) * p ^ k.val * (1 - p) ^ (n - k.val) * k.val =
        n * p * ∑ k : Fin n,
          (Nat.choose (n - 1) k.val : ℝ) * p ^ k.val * (1 - p) ^ (n - 1 - k.val) := by
    rcases n <;> simp_all +decide [Fin.sum_univ_succ, Nat.add_one_mul_choose_eq]
    simp +decide [mul_add, Finset.mul_sum _ _ _, Nat.choose_succ_succ, mul_assoc,
      mul_comm, mul_left_comm, pow_succ', tsub_tsub]
    refine' Finset.sum_congr rfl fun x hx => _
    have := Nat.add_one_mul_choose_eq (‹_› : ℕ) (x + 1)
    have := Nat.add_one_mul_choose_eq (‹_› : ℕ) (x + 2)
    norm_num [Nat.choose_succ_succ] at *
    ring_nf at *
    simp_all +decide [← mul_assoc, ← pow_succ']
    push_cast [← @Nat.cast_inj ℝ ..] at *
    nlinarith [show
      0 ≤ p ^ 2 * p ^ (x : ℕ) * (1 - p) ^ (‹_› - (1 + x : ℕ)) by
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hp _))
          (pow_nonneg (sub_nonneg.mpr hp') _)]
  rcases n <;> simp_all +decide [Fin.sum_univ_castSucc]
  have h_binom :
      ∑ x : Fin (Nat.succ ‹_›),
        (Nat.choose ‹_› x.val : ℝ) * p ^ x.val * (1 - p) ^ (‹_› - x.val) =
          (p + (1 - p)) ^ ‹_› := by
    rw [add_pow]
    simp +decide [mul_assoc, mul_comm, mul_left_comm, Finset.sum_range]
  simp_all +decide [Finset.sum_range, Fin.sum_univ_castSucc]

lemma binomial_alternating_identity (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    ∑ k : Fin (n + 1),
      (Nat.choose n k.val : ℝ) * p ^ k.val * (1 - p) ^ (n - k.val) *
        (if k.val % 2 = 0 then (1 : ℝ) else -1) = (1 - 2 * p) ^ n := by
  convert (add_pow (-p : ℝ) (1 - p) n) using 1 <;> ring
  · rw [show (1 - p * 2 : ℝ) = (-p) + (1 - p) by ring, add_pow]
    rw [Finset.sum_range]
    refine' Finset.sum_congr rfl fun x hx => _
    split_ifs <;> ring
    · norm_num [Nat.even_iff, ‹_›]
    · rw [neg_one_pow_eq_pow_mod_two]
      aesop
  · convert (add_pow (-p : ℝ) (1 - p) n) using 1 <;> ring

theorem prob_6_1 (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    let P : Measure (Fin (n + 1)) :=
      ∑ k : Fin (n + 1),
        (ENNReal.ofReal (Nat.choose n k.val * p ^ k.val * (1 - p) ^ (n - k.val))) •
          Measure.dirac k
    let X : Fin (n + 1) → ℝ := fun k => k.val
    let Y : Fin (n + 1) → ℝ := fun k => if k.val % 2 = 0 then 1 else -1
    ∫ x, X x ∂P = n * p ∧ ∫ x, Y x ∂P = (1 - 2 * p) ^ n := by
  intro P X Y
  constructor
  · show ∫ x, (x.val : ℝ) ∂P = ↑n * p
    rw [integral_weighted_dirac_fin _ _ (binom_weight_nonneg n p hp hp')]
    exact binomial_expectation_identity n p hp hp'
  · show ∫ x, Y x ∂P = (1 - 2 * p) ^ n
    rw [integral_weighted_dirac_fin _ _ (binom_weight_nonneg n p hp hp')]
    exact binomial_alternating_identity n p hp hp'
