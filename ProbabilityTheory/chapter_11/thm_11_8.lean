/-
TASK ID: thm_11_8
TYPE: Theorem_Statement
SOURCE PLAN: chapter11-strong-law-large-numbers
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_10.def_10_1
import ProbabilityTheory.chapter_11.thm_11_5
import ProbabilityTheory.common_support.etemadi_pairwise_iid_slln




-- WRITE FINAL LEAN CODE BELOW

open Filter
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators
open scoped Topology

theorem thm_11_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m : ℝ)
    (hInt : Integrable (X 0) P)
    (hpairwise : Pairwise fun i j => X i ⟂ᵢ[P] X j)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hmean : P[X 0] = m) :
    ConvergesAlmostSurely P (fun n => thm_11_5_sampleMean X n) (fun _ => m) := by
  have hInt_all : ∀ i, Integrable (X i) P := fun i =>
    (hident i).integrable_iff.2 hInt
  have hAvg_meas : ∀ n, AEStronglyMeasurable (thm_11_5_sampleMean X n) P := by
    intro n
    change AEStronglyMeasurable
      (fun ω => (1 / ((n : ℝ) + 1)) * (∑ i : Fin (n + 1), X i.1 ω)) P
    simpa using
      (MeasureTheory.AEStronglyMeasurable.const_mul
        (Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin (n + 1)))
          (fun i _hi => (hInt_all i.1).aestronglyMeasurable))
        (1 / ((n : ℝ) + 1)))
  have hStrong :
      ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, X i ω))
          atTop (nhds P[X 0]) :=
    etemadi_pairwise_iid_strong_law_ae P X hInt hpairwise hident
  have hAS_mean :
      ConvergesAlmostSurely P (fun n => thm_11_5_sampleMean X n) (fun _ => P[X 0]) := by
    refine ⟨hAvg_meas, aestronglyMeasurable_const, ?_⟩
    filter_upwards [hStrong] with ω hω
    have hcomp :=
      hω.comp (Filter.tendsto_add_atTop_nat 1)
    convert hcomp using 1
    ext n
    have hsum :
        (∑ i : Fin (n + 1), X i.1 ω) =
          ∑ i ∈ Finset.range (n + 1), X i ω := by
      simpa using (Fin.sum_univ_eq_sum_range (fun i => X i ω) (n + 1))
    simp [Function.comp_apply, thm_11_5_sampleMean, one_div, smul_eq_mul, hsum,
      Nat.cast_add, Nat.cast_one]
  refine ⟨hAS_mean.1, aestronglyMeasurable_const, ?_⟩
  filter_upwards [hAS_mean.2.2] with ω hω
  simpa [hmean] using hω
