/-
TASK ID: prob_6_9
TYPE: Problem
SOURCE PLAN: 24_chap6_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Filter

namespace Prob69Support

instance : MeasurableSpace ℕ+ := ⊤

noncomputable abbrev countingMeasure : Measure ℕ+ := Measure.count

def rowFunction (a : ℕ+ → ℕ+ → NNReal) (i : ℕ+) : ℕ+ → ENNReal :=
  fun j => (a i j : ENNReal)

def partialRowSum (a : ℕ+ → ℕ+ → NNReal) (n : ℕ) : ℕ+ → ENNReal :=
  fun j => Finset.sum (Finset.range n) fun m => rowFunction a (Nat.succPNat m) j

noncomputable def limitRowSum (a : ℕ+ → ℕ+ → NNReal) : ℕ+ → ENNReal :=
  fun j => ∑' i : ℕ+, rowFunction a i j

lemma rowFunction_measurable (a : ℕ+ → ℕ+ → NNReal) (i : ℕ+) :
    Measurable (rowFunction a i) :=
  measurable_of_countable _

lemma rowFunction_lintegral_eq_tsum (a : ℕ+ → ℕ+ → NNReal) (i : ℕ+) :
    ∫⁻ j, rowFunction a i j ∂countingMeasure = ∑' j : ℕ+, rowFunction a i j := by
  simpa [countingMeasure] using MeasureTheory.lintegral_count (rowFunction a i)

lemma partialRowSum_monotone (a : ℕ+ → ℕ+ → NNReal) :
    Monotone (partialRowSum a) := by
  intro m n hmn j
  have hmono : Monotone (fun n => partialRowSum a n j) := by
    exact monotone_nat_of_le_succ (fun n => by
      calc
        partialRowSum a n j ≤ partialRowSum a n j + rowFunction a (Nat.succPNat n) j := by
          exact le_add_of_nonneg_right bot_le
        _ = partialRowSum a (n + 1) j := by
          rw [partialRowSum, partialRowSum, Finset.sum_range_succ])
  exact hmono hmn

lemma partialRowSum_iSup_eq_limitRowSum (a : ℕ+ → ℕ+ → NNReal) (j : ℕ+) :
    (⨆ n : ℕ, partialRowSum a n j) = limitRowSum a j := by
  have htsum :
      (∑' i : ℕ+, rowFunction a i j) =
        ∑' n : ℕ, rowFunction a (Nat.succPNat n) j := by
    simpa [rowFunction] using
      (Equiv.pnatEquivNat.tsum_eq (fun n : ℕ => rowFunction a (Nat.succPNat n) j))
  rw [limitRowSum, htsum]
  symm
  exact ENNReal.tsum_eq_iSup_nat

lemma partialRowSum_lintegral_eq_finset (a : ℕ+ → ℕ+ → NNReal) (n : ℕ) :
    ∫⁻ j, partialRowSum a n j ∂countingMeasure =
      Finset.sum (Finset.range n) fun m => ∫⁻ j, rowFunction a (Nat.succPNat m) j ∂countingMeasure := by
  simpa [partialRowSum, countingMeasure] using
    (MeasureTheory.lintegral_finset_sum
      (μ := countingMeasure) (s := Finset.range n)
      (f := fun m : ℕ => rowFunction a (Nat.succPNat m))
      (fun m hm => rowFunction_measurable a (Nat.succPNat m)))

lemma limitRowSum_lintegral_eq_iSup (a : ℕ+ → ℕ+ → NNReal) :
    ∫⁻ j, limitRowSum a j ∂countingMeasure =
      ⨆ n : ℕ, ∫⁻ j, partialRowSum a n j ∂countingMeasure := by
  rw [← MeasureTheory.lintegral_iSup
    (μ := countingMeasure)
    (f := partialRowSum a)
    (fun n => measurable_of_countable (partialRowSum a n))
    (partialRowSum_monotone a)]
  exact MeasureTheory.lintegral_congr_ae <|
    Filter.Eventually.of_forall fun j => (partialRowSum_iSup_eq_limitRowSum a j).symm

lemma left_iterated_lintegral_eq_limit (a : ℕ+ → ℕ+ → NNReal) :
    ∫⁻ i, ∫⁻ j, rowFunction a i j ∂countingMeasure ∂countingMeasure =
      ∫⁻ j, limitRowSum a j ∂countingMeasure := by
  calc
    ∫⁻ i, ∫⁻ j, rowFunction a i j ∂countingMeasure ∂countingMeasure
        = ∑' i : ℕ+, ∫⁻ j, rowFunction a i j ∂countingMeasure := by
            simpa [countingMeasure] using
              (MeasureTheory.lintegral_count
                (fun i : ℕ+ => ∫⁻ j, rowFunction a i j ∂countingMeasure))
    _ = ∑' n : ℕ, ∫⁻ j, rowFunction a (Nat.succPNat n) j ∂countingMeasure := by
          simpa using
            (Equiv.pnatEquivNat.tsum_eq
              (fun n : ℕ => ∫⁻ j, rowFunction a (Nat.succPNat n) j ∂countingMeasure))
    _ = ⨆ n : ℕ, Finset.sum (Finset.range n)
          (fun m => ∫⁻ j, rowFunction a (Nat.succPNat m) j ∂countingMeasure) := by
          rw [ENNReal.tsum_eq_iSup_nat]
    _ = ⨆ n : ℕ, ∫⁻ j, partialRowSum a n j ∂countingMeasure := by
          simp_rw [partialRowSum_lintegral_eq_finset]
    _ = ∫⁻ j, limitRowSum a j ∂countingMeasure := by
          exact (limitRowSum_lintegral_eq_iSup a).symm

lemma right_iterated_lintegral_eq_limit (a : ℕ+ → ℕ+ → NNReal) :
    ∫⁻ j, ∫⁻ i, rowFunction a i j ∂countingMeasure ∂countingMeasure =
      ∫⁻ j, limitRowSum a j ∂countingMeasure := by
  refine MeasureTheory.lintegral_congr_ae <| Filter.Eventually.of_forall ?_
  intro j
  calc
    ∫⁻ i, rowFunction a i j ∂countingMeasure = ∑' i : ℕ+, rowFunction a i j := by
      simpa [countingMeasure] using MeasureTheory.lintegral_count (fun i : ℕ+ => rowFunction a i j)
    _ = limitRowSum a j := by
      simp [limitRowSum]

end Prob69Support

open Prob69Support

theorem prob_6_9 (a : ℕ+ → ℕ+ → NNReal) :
    let μ : MeasureTheory.Measure ℕ+ := MeasureTheory.Measure.count
    ∫⁻ i, ∫⁻ j, (a i j : ENNReal) ∂μ ∂μ = ∫⁻ j, ∫⁻ i, (a i j : ENNReal) ∂μ ∂μ := by
  intro μ
  change ∫⁻ i, ∫⁻ j, rowFunction a i j ∂countingMeasure ∂countingMeasure =
    ∫⁻ j, ∫⁻ i, rowFunction a i j ∂countingMeasure ∂countingMeasure
  calc
    ∫⁻ i, ∫⁻ j, rowFunction a i j ∂countingMeasure ∂countingMeasure
        = ∫⁻ j, limitRowSum a j ∂countingMeasure := left_iterated_lintegral_eq_limit a
    _ = ∫⁻ j, ∫⁻ i, rowFunction a i j ∂countingMeasure ∂countingMeasure := by
          exact (right_iterated_lintegral_eq_limit a).symm
