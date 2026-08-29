/-
TASK ID: prob_6_3
TYPE: Problem
SOURCE PLAN: 24_chap6_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace Def67Support

noncomputable def posPart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → EReal) : Ω → ENNReal :=
  fun ω => (X ω).toENNReal

noncomputable def negPart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → EReal) : Ω → ENNReal :=
  fun ω => (-X ω).toENNReal

noncomputable def posLIntegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → EReal) : ENNReal :=
  ∫⁻ ω, posPart X ω ∂P

noncomputable def negLIntegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → EReal) : ENNReal :=
  ∫⁻ ω, negPart X ω ∂P

noncomputable def textbookIntegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → EReal) : Option EReal :=
  if posLIntegral P X = ⊤ ∧ negLIntegral P X = ⊤ then
    none
  else
    some ((posLIntegral P X : EReal) - (negLIntegral P X : EReal))

end Def67Support

noncomputable def expectation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → EReal) : Option EReal :=
  Def67Support.textbookIntegral P X

namespace Prob63Support

abbrev CouponStageΩ (k : ℕ) := Fin k → ℕ

noncomputable def stageSuccessProb (n : ℕ) {k : ℕ} (i : Fin k) : ℝ :=
  ((n - i.1 : ℕ) : ℝ) / n

lemma sampleCount_pos {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : 0 < n := by
  exact lt_of_lt_of_le (Nat.succ_le_iff.mp hk) hkn

lemma stageSuccessProb_pos {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    0 < stageSuccessProb n i := by
  have hi : i.1 < n := lt_of_lt_of_le i.2 hkn
  have hn : (0 : ℝ) < n := by
    exact_mod_cast sampleCount_pos hk hkn
  unfold stageSuccessProb
  exact div_pos (by exact_mod_cast Nat.sub_pos_of_lt hi) hn

lemma stageSuccessProb_le_one {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    stageSuccessProb n i ≤ 1 := by
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (sampleCount_pos hk hkn))
  unfold stageSuccessProb
  field_simp [hn]
  exact_mod_cast Nat.sub_le n i.1

lemma stageFailureProb_abs_lt_one {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    ‖1 - stageSuccessProb n i‖ < 1 := by
  have hp_pos := stageSuccessProb_pos hk hkn i
  have hp_le := stageSuccessProb_le_one hk hkn i
  have hnonneg : 0 ≤ 1 - stageSuccessProb n i := sub_nonneg.mpr hp_le
  have hlt : 1 - stageSuccessProb n i < 1 := by linarith
  simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hlt

noncomputable def stagePMF (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) : PMF ℕ :=
  ProbabilityTheory.geometricPMF
    (p := stageSuccessProb n i)
    (stageSuccessProb_pos hk hkn i)
    (stageSuccessProb_le_one hk hkn i)

noncomputable def stageMeasure (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    Measure ℕ :=
  (stagePMF n k hk hkn i).toMeasure

noncomputable def couponLaw (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    Measure (CouponStageΩ k) :=
  Measure.pi (stageMeasure n k hk hkn)

noncomputable def scalarStageWait (m : ℕ) : ℝ := (m : ℝ) + 1

noncomputable def stageWaitReal {k : ℕ} (i : Fin k) : CouponStageΩ k → ℝ :=
  fun ω => scalarStageWait (ω i)

noncomputable def couponCollectionTimeReal (_n k : ℕ) : CouponStageΩ k → ℝ :=
  fun ω => ∑ i : Fin k, stageWaitReal i ω

noncomputable def couponCollectionTime (n k : ℕ) : CouponStageΩ k → EReal :=
  fun ω => (couponCollectionTimeReal n k ω : EReal)

noncomputable def couponCollectorValueReal (n k : ℕ) : ℝ :=
  ∑ i : Fin k, (n : ℝ) / (n - i.1 : ℕ)

noncomputable def couponCollectorValue (n k : ℕ) : EReal :=
  (couponCollectorValueReal n k : ℝ)

lemma stageMeasure_apply_singleton {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (i : Fin k) (m : ℕ) :
    stageMeasure n k hk hkn i {m} =
      ENNReal.ofReal (ProbabilityTheory.geometricPMFReal (stageSuccessProb n i) m) := by
  rw [stageMeasure]
  rw [PMF.toMeasure_apply_singleton (stagePMF n k hk hkn i) m (measurableSet_singleton m)]
  rfl

lemma stageMeasure_apply_singleton_toReal {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (i : Fin k) (m : ℕ) :
    (stageMeasure n k hk hkn i {m}).toReal =
      ProbabilityTheory.geometricPMFReal (stageSuccessProb n i) m := by
  rw [stageMeasure_apply_singleton hk hkn i m]
  rw [ENNReal.toReal_ofReal]
  exact ProbabilityTheory.geometricPMFReal_nonneg
    (stageSuccessProb_pos hk hkn i)
    (stageSuccessProb_le_one hk hkn i)

lemma stageWaitSeries_hasSum {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    HasSum
      (fun m : ℕ =>
        scalarStageWait m * ProbabilityTheory.geometricPMFReal (stageSuccessProb n i) m)
      ((n : ℝ) / (n - i.1 : ℕ)) := by
  let p : ℝ := stageSuccessProb n i
  let r : ℝ := 1 - p
  have hr : ‖r‖ < 1 := by
    simpa [r, p] using stageFailureProb_abs_lt_one hk hkn i
  have hsum :
      HasSum (fun m : ℕ => ((m + 1 : ℕ) : ℝ) * r ^ m)
        (1 / (1 - r) ^ (1 + 1 : ℕ)) := by
    simpa [Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
      using hasSum_choose_mul_geometric_of_norm_lt_one 1 hr
  have hsum' :
      HasSum (fun m : ℕ => scalarStageWait m * r ^ m)
        (1 / (1 - r) ^ (1 + 1 : ℕ)) := by
    simpa [scalarStageWait] using hsum
  have hscaled :
      HasSum
        (fun m : ℕ => p * (scalarStageWait m * r ^ m))
        (p * (1 / (1 - r) ^ (1 + 1 : ℕ))) := hsum'.mul_left p
  have htarget : p * (1 / (1 - r) ^ (1 + 1 : ℕ)) = (n : ℝ) / (n - i.1 : ℕ) := by
    have hn : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (sampleCount_pos hk hkn))
    have hni : ((n - i.1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.sub_pos_of_lt (lt_of_lt_of_le i.2 hkn)).ne'
    have hp_ne : p ≠ 0 := (stageSuccessProb_pos hk hkn i).ne'
    calc
      p * (1 / (1 - r) ^ (1 + 1 : ℕ)) = p * (1 / p ^ (1 + 1 : ℕ)) := by
        simp [r]
      _ = 1 / p := by
        field_simp [hp_ne]
      _ = (n : ℝ) / (n - i.1 : ℕ) := by
        unfold p stageSuccessProb
        field_simp [hn, hni]
  convert hscaled using 1
  · ext m
    simp [scalarStageWait, ProbabilityTheory.geometricPMFReal, r, p, mul_left_comm, mul_comm]
  · exact htarget.symm

lemma stageWaitSummableNorm {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    Summable
      (fun m : ℕ =>
        (stageMeasure n k hk hkn i {m}).toReal * ‖scalarStageWait m‖) := by
  have hsum := (stageWaitSeries_hasSum hk hkn i).summable
  refine hsum.congr ?_
  intro m
  rw [stageMeasure_apply_singleton_toReal hk hkn i m]
  rw [Real.norm_of_nonneg (by unfold scalarStageWait; positivity)]
  simp [scalarStageWait, mul_comm]

lemma stageWaitIntegrable {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    Integrable scalarStageWait (stageMeasure n k hk hkn i) := by
  rw [← Measure.sum_smul_dirac (stageMeasure n k hk hkn i)]
  apply MeasureTheory.integrable_sum_dirac
  · intro m
    haveI : IsProbabilityMeasure (stageMeasure n k hk hkn i) := by
      unfold stageMeasure
      infer_instance
    have hle :
        stageMeasure n k hk hkn i {m} ≤ stageMeasure n k hk hkn i Set.univ := by
      exact measure_mono (by intro x hx; trivial)
    exact ne_of_lt (lt_of_le_of_lt (by simpa using hle) (by simp))
  · exact stageWaitSummableNorm hk hkn i

lemma stageWaitIntegral_eq {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (i : Fin k) :
    ∫ m, scalarStageWait m ∂(stageMeasure n k hk hkn i) =
      (n : ℝ) / (n - i.1 : ℕ) := by
  unfold stageMeasure
  rw [PMF.integral_eq_tsum]
  · change (∑' a : ℕ, ((stagePMF n k hk hkn i a).toReal) * scalarStageWait a) =
      (n : ℝ) / (n - i.1 : ℕ)
    have hmass :
        ∀ a : ℕ,
          ((stagePMF n k hk hkn i a).toReal) =
            ProbabilityTheory.geometricPMFReal (stageSuccessProb n i) a := by
      intro a
      unfold stagePMF ProbabilityTheory.geometricPMF
      change (ENNReal.ofReal
          (ProbabilityTheory.geometricPMFReal (stageSuccessProb n i) a)).toReal =
        ProbabilityTheory.geometricPMFReal (stageSuccessProb n i) a
      rw [ENNReal.toReal_ofReal]
      exact ProbabilityTheory.geometricPMFReal_nonneg
        (stageSuccessProb_pos hk hkn i)
        (stageSuccessProb_le_one hk hkn i)
    calc
      ∑' a : ℕ, ((stagePMF n k hk hkn i a).toReal) * scalarStageWait a
          = ∑' a : ℕ,
              scalarStageWait a * ProbabilityTheory.geometricPMFReal (stageSuccessProb n i) a := by
              apply tsum_congr
              intro a
              rw [hmass a]
              ring
      _ = (n : ℝ) / (n - i.1 : ℕ) := (stageWaitSeries_hasSum hk hkn i).tsum_eq
  · exact stageWaitIntegrable hk hkn i

lemma couponCollectionTimeReal_nonneg {n k : ℕ} (ω : CouponStageΩ k) :
    0 ≤ couponCollectionTimeReal n k ω := by
  unfold couponCollectionTimeReal
  exact Finset.sum_nonneg (fun i _ => by
    unfold stageWaitReal scalarStageWait
    positivity)

lemma couponCollectionTimeReal_integrable {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    Integrable (couponCollectionTimeReal n k) (couponLaw n k hk hkn) := by
  classical
  unfold couponCollectionTimeReal couponLaw
  refine integrable_finset_sum Finset.univ (fun i _ => ?_)
  haveI : ∀ j : Fin k, IsProbabilityMeasure (stageMeasure n k hk hkn j) := fun j => by
    unfold stageMeasure
    infer_instance
  exact MeasureTheory.integrable_comp_eval (μ := stageMeasure n k hk hkn)
    (i := i) (stageWaitIntegrable hk hkn i)

lemma couponCollectionTimeReal_integral_eq {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∫ ω, couponCollectionTimeReal n k ω ∂(couponLaw n k hk hkn) =
      couponCollectorValueReal n k := by
  classical
  haveI : ∀ j : Fin k, IsProbabilityMeasure (stageMeasure n k hk hkn j) := fun j => by
    unfold stageMeasure
    infer_instance
  unfold couponCollectionTimeReal couponCollectorValueReal couponLaw
  rw [MeasureTheory.integral_finset_sum]
  · refine Finset.sum_congr rfl ?_
    intro i hi
    have hsm :
        AEStronglyMeasurable scalarStageWait (stageMeasure n k hk hkn i) :=
      (measurable_of_countable scalarStageWait).aestronglyMeasurable
    simpa [stageWaitReal, scalarStageWait] using
      (MeasureTheory.integral_comp_eval (μ := stageMeasure n k hk hkn) (i := i) hsm).trans
        (stageWaitIntegral_eq hk hkn i)
  · intro i hi
    exact MeasureTheory.integrable_comp_eval (μ := stageMeasure n k hk hkn)
      (i := i) (stageWaitIntegrable hk hkn i)

lemma expectation_of_nonneg_real_eq_some_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : Integrable f μ) (h_nonneg : ∀ ω, 0 ≤ f ω) :
    expectation μ (fun ω => (f ω : EReal)) = some (((∫ ω, f ω ∂μ : ℝ)) : EReal) := by
  have hpos :
      Def67Support.posLIntegral μ (fun ω => (f ω : EReal)) =
        ENNReal.ofReal (∫ ω, f ω ∂μ) := by
    unfold Def67Support.posLIntegral Def67Support.posPart
    simp only [EReal.real_coe_toENNReal]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf]
    · exact Filter.Eventually.of_forall h_nonneg
  have hneg :
      Def67Support.negLIntegral μ (fun ω => (f ω : EReal)) = 0 := by
    unfold Def67Support.negLIntegral Def67Support.negPart
    calc
      ∫⁻ ω, (-((f ω : ℝ) : EReal)).toENNReal ∂μ = ∫⁻ ω, 0 ∂μ := by
        refine lintegral_congr_ae <| Filter.Eventually.of_forall (fun ω => ?_)
        simp [h_nonneg ω]
      _ = 0 := by simp
  unfold expectation Def67Support.textbookIntegral
  have hnot :
      ¬ (Def67Support.posLIntegral μ (fun ω => (f ω : EReal)) = ⊤ ∧
          Def67Support.negLIntegral μ (fun ω => (f ω : EReal)) = ⊤) := by
    intro h
    simpa [hneg] using h.2
  have hint_nonneg : 0 ≤ ∫ ω, f ω ∂μ := MeasureTheory.integral_nonneg h_nonneg
  rw [if_neg hnot, hpos, hneg]
  simp [hint_nonneg]

end Prob63Support

open Prob63Support

theorem prob_6_3 (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    expectation (couponLaw n k hk hkn) (couponCollectionTime n k) =
      some (couponCollectorValue n k) := by
  have hInt : Integrable (couponCollectionTimeReal n k) (couponLaw n k hk hkn) :=
    couponCollectionTimeReal_integrable hk hkn
  have hExp :=
    expectation_of_nonneg_real_eq_some_integral
      (couponLaw n k hk hkn) (couponCollectionTimeReal n k) hInt
      (couponCollectionTimeReal_nonneg (n := n) (k := k))
  rw [show couponCollectionTime n k = fun ω => (couponCollectionTimeReal n k ω : EReal) by rfl]
  rw [hExp, couponCollectionTimeReal_integral_eq hk hkn]
  rfl
