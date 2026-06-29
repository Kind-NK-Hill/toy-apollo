import Mathlib

open Filter
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators
open scoped Topology
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
        Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, (pos ∘ X i) ω) / n) atTop (nhds (𝔼[pos ∘ X 0])) :=
      ProbabilityTheory.strong_law_aux7 (X := fun i ω ↦ pos (X i ω)) hInt.pos_part
        (fun i j hij => (hpairwise hij).comp posm posm)
        (fun i => (hident i).comp posm) (fun i ω => le_max_right _ _)
    have hneg : ∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, (neg ∘ X i) ω) / n) atTop (nhds (𝔼[neg ∘ X 0])) :=
      ProbabilityTheory.strong_law_aux7 (X := fun i ω ↦ neg (X i ω)) hInt.neg_part
        (fun i j hij => (hpairwise hij).comp negm negm)
        (fun i => (hident i).comp negm) (fun i ω => le_max_right _ _)
    filter_upwards [hpos, hneg] with ω hωpos hωneg
    have hsub : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, X i ω))
        atTop (nhds ((∫ x, (pos ∘ X 0) x ∂P) - ∫ x, (neg ∘ X 0) x ∂P)) := by
      simpa [pos, neg, sub_eq_add_neg, div_eq_mul_inv, Finset.sum_sub_distrib, sub_div,
        Function.comp_apply, max_zero_sub_max_neg_zero_eq_self] using hωpos.sub hωneg
    have hmean : (∫ x, X 0 x ∂P) = (∫ x, (pos ∘ X 0) x ∂P) - ∫ x, (neg ∘ X 0) x ∂P := by
      rw [← integral_sub hInt.pos_part hInt.neg_part]
      congr
      ext x
      simp [pos, neg, max_zero_sub_max_neg_zero_eq_self, Function.comp_apply]
    simpa [hmean, div_eq_mul_inv] using hsub
