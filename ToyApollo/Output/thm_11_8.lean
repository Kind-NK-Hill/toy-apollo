import Mathlib
import ToyApollo.Output.def_10_1
import ToyApollo.Output.thm_11_5

/-
TASK ID: thm_11_8
TYPE: Theorem_Statement
SOURCE PLAN: chapter11-strong-law-large-numbers
TASK CONTENT:
\begin{thmbox}{11.8}
\end{thmbox}

Suppose Xi ,f o r i\geq 1 , are pairwise independent and identically distributed

random variables with finite mean \mu. ThenSn/n

as.

\to \mu asn\to\infty .

A proof of this theorem by Etemadi can be found in [ 4, Thm 2.4.1].
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators
open scoped Topology

-- Local source-step for `thm_11_8`: pairwise-independent iid real-valued
-- Etemadi step, from a.e. convergence of `∑ X_i/n` to `P[X 0]`.
theorem etemadi_pairwise_iid_strong_law_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ)
    (hInt : Integrable (X 0) P)
  (hpairwise : Pairwise fun i j => X i ⟂ᵢ[P] X j)
  (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, X i ω))
        atTop (nhds P[X 0]) := by
  letI : MeasureSpace Ω := ⟨P⟩
  by_cases h : ∀ᵐ ω, X 0 ω = 0
  · have I : ∀ᵐ ω, ∀ i, X i ω = 0 := by
      rw [ae_all_iff]
      intro i
      exact (hident i).symm.ae_snd (p := fun x ↦ x = 0) measurableSet_eq h
    filter_upwards [I] with ω hω
    simpa [hω] using (integral_eq_zero_of_ae h).symm
  · haveI : IsProbabilityMeasure P :=
      hInt.isProbabilityMeasure_of_indepFun (X 0) (X 1) h (hpairwise Nat.zero_ne_one)
    let pos : ℝ → ℝ := fun x => max x 0
    let neg : ℝ → ℝ := fun x => max (-x) 0
    have posm : Measurable pos := measurable_id'.max measurable_const
    have negm : Measurable neg := measurable_id'.neg.max measurable_const
    have hpos : ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, (pos ∘ X i) ω) / n) atTop
          (nhds (𝔼[pos ∘ X 0])) :=
      ProbabilityTheory.strong_law_aux7 (X := fun i ω ↦ pos (X i ω)) hInt.pos_part
        (fun i j hij => (hpairwise hij).comp posm posm)
        (fun i => (hident i).comp posm) (fun i ω => le_max_right _ _)
    have hneg : ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, (neg ∘ X i) ω) / n) atTop
          (nhds (𝔼[neg ∘ X 0])) :=
      ProbabilityTheory.strong_law_aux7 (X := fun i ω ↦ neg (X i ω)) hInt.neg_part
        (fun i j hij => (hpairwise hij).comp negm negm)
        (fun i => (hident i).comp negm) (fun i ω => le_max_right _ _)
    filter_upwards [hpos, hneg] with ω hωpos hωneg
    have hpoint : ∀ i, pos (X i ω) + -neg (X i ω) = X i ω := by
      intro i
      simpa [sub_eq_add_neg, pos, neg] using (max_zero_sub_max_neg_zero_eq_self (X i ω))
    have hsub : Tendsto (fun n : ℕ => (↑n)⁻¹ * ∑ x ∈ Finset.range n, (pos (X x ω) + -neg (X x ω)))
        atTop (nhds ((∫ x, (pos ∘ X 0) x ∂P) - ∫ x, (neg ∘ X 0) x ∂P)) := by
      simpa [div_eq_mul_inv, sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib, add_comm,
        add_left_comm, add_assoc, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using hωpos.sub hωneg
    have hsumEq : ∀ n, ∑ i ∈ Finset.range n, X i ω = ∑ x ∈ Finset.range n, (pos (X x ω) + -neg (X x ω)) := by
      intro n
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa [hpoint i]
    have hsub' : Tendsto (fun n : ℕ => (↑n)⁻¹ * ∑ i ∈ Finset.range n, X i ω)
        atTop (nhds ((∫ x, (pos ∘ X 0) x ∂P) - ∫ x, (neg ∘ X 0) x ∂P)) := by
      simpa [hsumEq] using hsub
    have hmean : (∫ x, X 0 x ∂P) = (∫ x, (pos ∘ X 0) x ∂P) - ∫ x, (neg ∘ X 0) x ∂P := by
      have hpoint : (fun x ↦ X 0 x) = fun x ↦ pos (X 0 x) - neg (X 0 x) := by
        funext x
        simpa [pos, neg] using (max_zero_sub_max_neg_zero_eq_self (X 0 x)).symm
      calc
        ∫ x, X 0 x ∂P = ∫ x, (pos (X 0 x) - neg (X 0 x)) ∂P := by
          simpa using congrArg (fun f => ∫ x, f x ∂P) hpoint
        _ = (∫ x, pos (X 0 x) ∂P) - ∫ x, neg (X 0 x) ∂P := by
          simpa [pos, neg] using integral_sub hInt.pos_part hInt.neg_part
    simpa [hmean, div_eq_mul_inv, smul_eq_mul, sub_eq_add_neg] using hsub'

theorem thm_11_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (m : ℝ)
    (hInt : Integrable (X 0) P)
    (hpairwise : Pairwise fun i j => X i ⟂ᵢ[P] X j)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hmean : P[X 0] = m) :
    ConvergesAlmostSurely P (fun n => thm_11_5_sampleMean X n) (fun _ => m) := by
  have hStrong :
      ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, X i ω))
          atTop (nhds P[X 0]) :=
    etemadi_pairwise_iid_strong_law_ae P X hInt hpairwise hident
  have hAS_mean :
      ConvergesAlmostSurely P (fun n => thm_11_5_sampleMean X n) (fun _ => P[X 0]) := by
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
  filter_upwards [hAS_mean] with ω hω
  simpa [hmean] using hω
