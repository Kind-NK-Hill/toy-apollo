/-
TASK ID: DirichletGammaProductDensity
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_01.DirichletGamma

open MeasureTheory ProbabilityTheory Real BigOperators Finset
open scoped ENNReal BigOperators

noncomputable section

 
theorem gammaScaleLaw_eq_withDensity_gammaPDF (alpha beta : ℝ) :
    gammaScaleLaw alpha beta =
      (volume : Measure ℝ).withDensity
        (ProbabilityTheory.gammaPDF alpha beta⁻¹) := by
  rfl



theorem gammaProductLaw_eq_pi_withDensity_gammaPDF
    {n : ℕ} (alpha : Fin n → ℝ) (beta : ℝ) :
    gammaProductLaw alpha beta =
      Measure.pi fun i =>
        (volume : Measure ℝ).withDensity
          (ProbabilityTheory.gammaPDF (alpha i) beta⁻¹) := by
  rfl

theorem gammaProductLaw_eq_pi_withDensity_gammaPDFReal
    {n : ℕ} (alpha : Fin n → ℝ) (beta : ℝ) :
    gammaProductLaw alpha beta =
      Measure.pi fun i =>
        (volume : Measure ℝ).withDensity
          (fun x => ENNReal.ofReal
            (ProbabilityTheory.gammaPDFReal (alpha i) beta⁻¹ x)) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem lintegral_fin_nat_prod_eq_prod_ennreal
    {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂Measure.pi μ =
      ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hprodmeas :
          Measurable
            (fun y : (i : Fin n) → E (Fin.succ i) =>
              ∏ i : Fin n, f (Fin.succ i) (y i)) := by
        fun_prop
      calc
        ∫⁻ x : (i : Fin (n + 1)) → E i, ∏ i, f i (x i) ∂Measure.pi μ =
            ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
              f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
              ∂(μ 0).prod (Measure.pi fun i => μ i.succ) := by
          rw [((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_map_equiv]
          apply lintegral_congr
          intro a
          rw [Fin.prod_univ_succ]
          have h0 :
              f 0 ((MeasurableEquiv.piFinSuccAbove E 0).symm a 0) = f 0 a.1 := by
            rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
            change
              f 0 (Fin.insertNth (0 : Fin (n + 1)) a.1 (fun j => a.2 j) 0) =
                f 0 a.1
            rw [Fin.insertNth_apply_same]
          have htail : ∀ j : Fin n,
              f (Fin.succ j)
                  ((MeasurableEquiv.piFinSuccAbove E 0).symm a (Fin.succ j)) =
                f (Fin.succ j) (a.2 j) := by
            intro j
            rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
            change
              f ((0 : Fin (n + 1)).succAbove j)
                  (Fin.insertNth (0 : Fin (n + 1)) a.1 (fun j => a.2 j)
                    ((0 : Fin (n + 1)).succAbove j)) =
                f ((0 : Fin (n + 1)).succAbove j) (a.2 j)
            rw [Fin.insertNth_apply_succAbove]
          rw [h0]
          exact congrArg (fun z => f 0 a.1 * z)
            (Finset.prod_congr rfl fun j _ => htail j)
        _ =
            (∫⁻ x, f 0 x ∂μ 0) *
              ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂μ i.succ := by
          rw [MeasureTheory.lintegral_prod]
          · simp_rw [MeasureTheory.lintegral_const_mul _ hprodmeas]
            rw [ih (fun i => f (Fin.succ i)) (fun i => hf _)]
            rw [MeasureTheory.lintegral_mul_const _ (hf 0)]
          · fun_prop
        _ = ∏ i, ∫⁻ x, f i x ∂μ i := by
          rw [Fin.prod_univ_succ]

theorem pi_withDensity_fin
    {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ℝ≥0∞)
    [∀ i, SigmaFinite ((μ i).withDensity (f i))]
    (hf : ∀ i, Measurable (f i)) :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  refine Measure.pi_eq (μ := fun i => (μ i).withDensity (f i)) ?_
  intro s hs
  rw [withDensity_apply]
  · rw [← lintegral_indicator
      (MeasurableSet.pi Set.finite_univ.countable fun i _ => hs i)]
    calc
      ∫⁻ x : (i : Fin n) → E i,
          Set.indicator (Set.pi Set.univ s) (fun x => ∏ i, f i (x i)) x
          ∂Measure.pi μ =
        ∫⁻ x : (i : Fin n) → E i,
          ∏ i, Set.indicator (s i) (f i) (x i) ∂Measure.pi μ := by
          apply lintegral_congr
          intro x
          classical
          by_cases hx : x ∈ Set.pi Set.univ s
          · have hxi : ∀ i : Fin n, x i ∈ s i := by
              intro i
              exact hx i (Set.mem_univ i)
            rw [Set.indicator_of_mem hx]
            refine Finset.prod_congr rfl ?_
            intro i _
            rw [Set.indicator_of_mem (hxi i)]
          · have hnot : ∃ i : Fin n, x i ∉ s i := by
              by_contra hnone
              rw [not_exists] at hnone
              exact hx (by simpa [Set.mem_pi] using hnone)
            rcases hnot with ⟨i, hi⟩
            have hprod :
                (∏ j : Fin n, Set.indicator (s j) (f j) (x j)) = 0 := by
              exact Finset.prod_eq_zero (Finset.mem_univ i)
                (by rw [Set.indicator_of_notMem hi])
            rw [Set.indicator_of_notMem hx, hprod]
      _ = ∏ i, ∫⁻ x in s i, f i x ∂μ i := by
        rw [lintegral_fin_nat_prod_eq_prod_ennreal
          (fun i x => Set.indicator (s i) (f i) x)
          (fun i => (hf i).indicator (hs i))]
        refine Finset.prod_congr rfl ?_
        intro i _
        rw [lintegral_indicator (hs i)]
      _ = ∏ i, ((μ i).withDensity (f i)) (s i) := by
        refine Finset.prod_congr rfl ?_
        intro i _
        rw [withDensity_apply _ (hs i)]
  · exact MeasurableSet.pi Set.finite_univ.countable fun i _ => hs i
