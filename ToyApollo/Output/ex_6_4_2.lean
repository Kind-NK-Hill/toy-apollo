/-
TASK ID: ex_6_4_2
TYPE: Example_Proof
SOURCE PLAN: 22_chap6_expectation
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.ex_6_4_1

open MeasureTheory
open scoped BigOperators

namespace Ex642Support

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def positiveTruncation (X : Ω → ℤ) (k : ℕ) : Ω → ENNReal :=
  fun ω => if 0 ≤ X ω ∧ X ω ≤ k then ((X ω).toNat : ENNReal) else 0

noncomputable def negativeTruncation (X : Ω → ℤ) (k : ℕ) : Ω → ENNReal :=
  positiveTruncation (fun ω => -X ω) k

noncomputable def positiveSeries (P : Measure Ω) (X : Ω → ℤ) : ENNReal :=
  ∑' i : ℕ, (i : ENNReal) * P (X ⁻¹' ({(i : ℤ)} : Set ℤ))

noncomputable def negativeSeries (P : Measure Ω) (X : Ω → ℤ) : ENNReal :=
  ∑' i : ℕ, (i : ENNReal) * P (X ⁻¹' ({(-(i : ℤ))} : Set ℤ))

theorem neg_preimage_singleton (X : Ω → ℤ) (i : ℕ) :
    (fun ω => -X ω) ⁻¹' ({(i : ℤ)} : Set ℤ) =
      X ⁻¹' ({(-(i : ℤ))} : Set ℤ) := by
  ext ω
  constructor
  · intro h
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h ⊢
    linarith
  · intro h
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h ⊢
    linarith

theorem positiveTruncation_eq_sum (X : Ω → ℤ) (k : ℕ) :
    positiveTruncation X k =
      fun ω =>
        ∑ i ∈ Finset.range (k + 1),
          Set.indicator (X ⁻¹' ({(i : ℤ)} : Set ℤ)) (fun _ : Ω => (i : ENNReal)) ω := by
  funext ω
  classical
  by_cases hω : 0 ≤ X ω ∧ X ω ≤ k
  · have hmem : (X ω).toNat ∈ Finset.range (k + 1) := by
      rw [Finset.mem_range]
      exact Nat.lt_add_one_iff.mpr (Int.toNat_le.mpr hω.2)
    rw [positiveTruncation, if_pos hω, Finset.sum_eq_single_of_mem (X ω).toNat hmem]
    · have hEq : (((X ω).toNat : ℕ) : ℤ) = X ω := Int.toNat_of_nonneg hω.1
      simp [Set.indicator, hEq]
    · intro j hj hne
      have hne' : (j : ℤ) ≠ X ω := by
        intro hEq
        apply hne
        exact Int.ofNat.inj (hEq.trans (Int.toNat_of_nonneg hω.1).symm)
      have hnot : ω ∉ X ⁻¹' ({(j : ℤ)} : Set ℤ) := by
        intro hpre
        exact hne' (by simpa using hpre.symm)
      simp [Set.indicator, hnot]
  · rw [positiveTruncation, if_neg hω]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    have hnot : ω ∉ X ⁻¹' ({(j : ℤ)} : Set ℤ) := by
      intro hpre
      apply hω
      constructor
      · rw [show X ω = (j : ℤ) by simpa using hpre]
        exact_mod_cast Nat.zero_le j
      · rw [show X ω = (j : ℤ) by simpa using hpre]
        exact Int.ofNat_le.mpr (Nat.lt_add_one_iff.mp (Finset.mem_range.mp hj))
    simp [Set.indicator, hnot]

theorem positiveTruncation_measurable (X : Ω → ℤ) (hXm : Measurable X) (k : ℕ) :
    Measurable (positiveTruncation X k) := by
  rw [positiveTruncation_eq_sum]
  exact Finset.measurable_sum (Finset.range (k + 1)) fun i hi =>
    measurable_const.indicator (hXm (measurableSet_singleton (i : ℤ)))

theorem positiveTruncation_integral_formula (P : Measure Ω) (X : Ω → ℤ)
    (hXm : Measurable X) (k : ℕ) :
    ∫⁻ ω, positiveTruncation X k ω ∂P =
      ∑ i ∈ Finset.range (k + 1), (i : ENNReal) * P (X ⁻¹' ({(i : ℤ)} : Set ℤ)) := by
  rw [positiveTruncation_eq_sum]
  rw [MeasureTheory.lintegral_finset_sum]
  · refine Finset.sum_congr rfl ?_
    intro i hi
    simpa using
      (MeasureTheory.lintegral_indicator_const
        (μ := P)
        (s := X ⁻¹' ({(i : ℤ)} : Set ℤ))
        (hs := hXm (measurableSet_singleton (i : ℤ)))
        (c := (i : ENNReal)))
  · intro i hi
    exact measurable_const.indicator (hXm (measurableSet_singleton (i : ℤ)))

theorem positiveTruncation_mono (X : Ω → ℤ) :
    Monotone (positiveTruncation X) := by
  intro k l hkl ω
  by_cases h0 : 0 ≤ X ω
  · by_cases hk : X ω ≤ k
    · have hl : X ω ≤ l := le_trans hk (by exact_mod_cast hkl)
      simp [positiveTruncation, h0, hk, hl]
    · have hk' : ¬ (0 ≤ X ω ∧ X ω ≤ k) := by simp [h0, hk]
      have hleft : positiveTruncation X k ω = 0 := by simp [positiveTruncation, hk']
      by_cases hl : X ω ≤ l
      · have hright : positiveTruncation X l ω = ((X ω).toNat : ENNReal) := by
          simp [positiveTruncation, h0, hl]
        rw [hleft, hright]
        exact zero_le
      · simp [positiveTruncation, h0, hk, hl]
  · have hleft : positiveTruncation X k ω = 0 := by simp [positiveTruncation, h0]
    have hright : positiveTruncation X l ω = 0 := by simp [positiveTruncation, h0]
    rw [hleft, hright]

theorem iSup_positiveTruncation (X : Ω → ℤ) (ω : Ω) :
    (⨆ k : ℕ, positiveTruncation X k ω) = ((X ω).toNat : ENNReal) := by
  by_cases h0 : 0 ≤ X ω
  · have hEqInt : (((X ω).toNat : ℕ) : ℤ) = X ω := Int.toNat_of_nonneg h0
    apply le_antisymm
    · refine iSup_le ?_
      intro k
      by_cases hk : X ω ≤ k
      · simp [positiveTruncation, h0, hk]
      · simp [positiveTruncation, h0, hk]
    · have hk : X ω ≤ ((X ω).toNat : ℤ) := by simpa [hEqInt]
      have hself : positiveTruncation X (X ω).toNat ω = ((X ω).toNat : ENNReal) := by
        simp [positiveTruncation, h0, hk]
      calc
        ((X ω).toNat : ENNReal) = positiveTruncation X (X ω).toNat ω := hself.symm
        _ ≤ ⨆ k : ℕ, positiveTruncation X k ω := le_iSup (fun k => positiveTruncation X k ω) (X ω).toNat
  · have hnonpos : X ω ≤ 0 := le_of_not_ge h0
    have hzero : (X ω).toNat = 0 := Int.toNat_of_nonpos hnonpos
    rw [hzero]
    apply le_antisymm
    · refine iSup_le ?_
      intro k
      simp [positiveTruncation, h0]
    · exact show (((0 : ℕ) : ENNReal)) ≤ ⨆ k : ℕ, positiveTruncation X k ω by simp

theorem positiveSeries_eq_lintegral (P : Measure Ω) (X : Ω → ℤ)
    (hXm : Measurable X) :
    positiveSeries P X = ∫⁻ ω, ((X ω).toNat : ENNReal) ∂P := by
  have hlim :
      ∫⁻ ω, ((X ω).toNat : ENNReal) ∂P =
        ⨆ k : ℕ, ∫⁻ ω, positiveTruncation X k ω ∂P := by
    rw [← MeasureTheory.lintegral_iSup (fun k => positiveTruncation_measurable X hXm k)
      (positiveTruncation_mono X)]
    congr 1
    ext ω
    exact (iSup_positiveTruncation X ω).symm
  have hN : Filter.Tendsto (fun k : ℕ => k + 1) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.mpr ?_
    intro b
    rw [Filter.eventually_atTop]
    refine ⟨b, ?_⟩
    intro k hk
    exact le_trans hk (Nat.le_succ k)
  calc
    positiveSeries P X
        = ⨆ k : ℕ, ∑ i ∈ Finset.range ((fun n : ℕ => n + 1) k),
            (i : ENNReal) * P (X ⁻¹' ({(i : ℤ)} : Set ℤ)) := by
              simpa [positiveSeries] using
                (ENNReal.tsum_eq_iSup_nat'
                  (f := fun i : ℕ => (i : ENNReal) * P (X ⁻¹' ({(i : ℤ)} : Set ℤ)))
                  (N := fun k : ℕ => k + 1) hN)
    _ = ⨆ k : ℕ, ∫⁻ ω, positiveTruncation X k ω ∂P := by
          apply iSup_congr
          intro k
          symm
          exact positiveTruncation_integral_formula P X hXm k
    _ = ∫⁻ ω, ((X ω).toNat : ENNReal) ∂P := hlim.symm

theorem negativeTruncation_measurable (X : Ω → ℤ) (hXm : Measurable X) (k : ℕ) :
    Measurable (negativeTruncation X k) := by
  simpa [negativeTruncation] using positiveTruncation_measurable (X := fun ω => -X ω) hXm.neg k

theorem negativeTruncation_integral_formula (P : Measure Ω) (X : Ω → ℤ)
    (hXm : Measurable X) (k : ℕ) :
    ∫⁻ ω, negativeTruncation X k ω ∂P =
      ∑ i ∈ Finset.range (k + 1), (i : ENNReal) * P (X ⁻¹' ({(-(i : ℤ))} : Set ℤ)) := by
  have hbase :=
    positiveTruncation_integral_formula (P := P) (X := fun ω => -X ω) hXm.neg k
  simpa [negativeTruncation, neg_preimage_singleton] using hbase

theorem negativeTruncation_mono (X : Ω → ℤ) :
    Monotone (negativeTruncation X) := by
  change Monotone (positiveTruncation (fun ω => -X ω))
  exact positiveTruncation_mono (X := fun ω => -X ω)

theorem iSup_negativeTruncation (X : Ω → ℤ) (ω : Ω) :
    (⨆ k : ℕ, negativeTruncation X k ω) = ((-X ω).toNat : ENNReal) := by
  simpa [negativeTruncation] using iSup_positiveTruncation (X := fun ω => -X ω) ω

theorem negativeSeries_eq_lintegral (P : Measure Ω) (X : Ω → ℤ)
    (hXm : Measurable X) :
    negativeSeries P X = ∫⁻ ω, ((-X ω).toNat : ENNReal) ∂P := by
  have hbase := positiveSeries_eq_lintegral (P := P) (X := fun ω => -X ω) hXm.neg
  simpa [negativeSeries, positiveSeries, neg_preimage_singleton] using hbase

theorem posPart_eq_toNat (X : Ω → ℤ) :
    Def65Support.posPart (fun ω => ((((X ω : ℤ) : ℝ) : EReal))) =
      fun ω => ((X ω).toNat : ENNReal) := by
  funext ω
  by_cases h0 : 0 ≤ X ω
  · have hnatI : (((X ω).toNat : ℕ) : ℤ) = X ω := Int.toNat_of_nonneg h0
    have hnatR : (((X ω).toNat : ℕ) : ℝ) = (X ω : ℝ) := by exact_mod_cast hnatI
    calc
      Def65Support.posPart (fun ω => ((((X ω : ℤ) : ℝ) : EReal))) ω
          = ENNReal.ofReal (X ω : ℝ) := by rfl
      _ = ((X ω).toNat : ENNReal) := by
          rw [← hnatR]
          simp
  · have hnonpos : X ω ≤ 0 := le_of_not_ge h0
    have hzero : (X ω).toNat = 0 := Int.toNat_of_nonpos hnonpos
    simp [Def65Support.posPart, hzero, hnonpos]

theorem negPart_eq_toNat_neg (X : Ω → ℤ) :
    Def65Support.negPart (fun ω => ((((X ω : ℤ) : ℝ) : EReal))) =
      fun ω => ((-X ω).toNat : ENNReal) := by
  funext ω
  by_cases h0 : 0 ≤ -X ω
  · have hnatI : ((((-X ω).toNat : ℕ) : ℤ)) = -X ω := Int.toNat_of_nonneg h0
    have hnatR : ((((-X ω).toNat : ℕ) : ℝ)) = ((-X ω : ℤ) : ℝ) := by exact_mod_cast hnatI
    calc
      Def65Support.negPart (fun ω => ((((X ω : ℤ) : ℝ) : EReal))) ω
          = ENNReal.ofReal (((-X ω : ℤ) : ℝ)) := by simp [Def65Support.negPart]
      _ = ((-X ω).toNat : ENNReal) := by
          rw [← hnatR]
          simp
  · have hnonpos : -X ω ≤ 0 := le_of_not_ge h0
    have hzero : (-X ω).toNat = 0 := Int.toNat_of_nonpos hnonpos
    have hnonneg : 0 ≤ X ω := by linarith
    simp [Def65Support.negPart, hzero, hnonneg]

end Ex642Support

theorem ex_6_4_2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℤ) (hXm : Measurable X) :
    (∀ k : ℕ,
      ∫⁻ ω, Ex642Support.positiveTruncation X k ω ∂P =
        ∑ i ∈ Finset.range (k + 1), (i : ENNReal) * P (X ⁻¹' ({(i : ℤ)} : Set ℤ))) ∧
    Filter.Tendsto
      (fun k : ℕ => ∫⁻ ω, Ex642Support.positiveTruncation X k ω ∂P)
      Filter.atTop
      (nhds (Ex642Support.positiveSeries P X)) ∧
    (∀ k : ℕ,
      ∫⁻ ω, Ex642Support.negativeTruncation X k ω ∂P =
        ∑ i ∈ Finset.range (k + 1), (i : ENNReal) * P (X ⁻¹' ({(-(i : ℤ))} : Set ℤ))) ∧
    Filter.Tendsto
      (fun k : ℕ => ∫⁻ ω, Ex642Support.negativeTruncation X k ω ∂P)
      Filter.atTop
      (nhds (Ex642Support.negativeSeries P X)) ∧
    Def65Support.posLIntegral P (fun ω => ((((X ω : ℤ) : ℝ) : EReal))) =
      Ex642Support.positiveSeries P X ∧
    Def65Support.negLIntegral P (fun ω => ((((X ω : ℤ) : ℝ) : EReal))) =
      Ex642Support.negativeSeries P X ∧
    expectation P (fun ω => ((((X ω : ℤ) : ℝ) : EReal))) =
      if Ex642Support.positiveSeries P X = ⊤ ∧ Ex642Support.negativeSeries P X = ⊤ then
        none
      else
        some
          ((Ex642Support.positiveSeries P X : EReal) -
            (Ex642Support.negativeSeries P X : EReal)) := by
  have hPosFinite :
      ∀ k : ℕ,
        ∫⁻ ω, Ex642Support.positiveTruncation X k ω ∂P =
          ∑ i ∈ Finset.range (k + 1), (i : ENNReal) * P (X ⁻¹' ({(i : ℤ)} : Set ℤ)) := by
    intro k
    exact Ex642Support.positiveTruncation_integral_formula P X hXm k
  have hNegFinite :
      ∀ k : ℕ,
        ∫⁻ ω, Ex642Support.negativeTruncation X k ω ∂P =
          ∑ i ∈ Finset.range (k + 1), (i : ENNReal) * P (X ⁻¹' ({(-(i : ℤ))} : Set ℤ)) := by
    intro k
    exact Ex642Support.negativeTruncation_integral_formula P X hXm k
  let fpos : ℕ → ENNReal := fun i => (i : ENNReal) * P (X ⁻¹' ({(i : ℤ)} : Set ℤ))
  have hpos_hasSum : HasSum fpos (Ex642Support.positiveSeries P X) := by
    simpa [Ex642Support.positiveSeries, fpos] using (ENNReal.summable : Summable fpos).hasSum
  have hN : Filter.Tendsto (fun k : ℕ => k + 1) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.mpr ?_
    intro b
    rw [Filter.eventually_atTop]
    refine ⟨b, ?_⟩
    intro k hk
    exact le_trans hk (Nat.le_succ k)
  have hPosTendsto0 :
      Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, fpos i) Filter.atTop
        (nhds (Ex642Support.positiveSeries P X)) := by
    exact (ENNReal.hasSum_iff_tendsto_nat (r := Ex642Support.positiveSeries P X)).1 hpos_hasSum
  have hPosTendsto :
      Filter.Tendsto
        (fun k : ℕ => ∫⁻ ω, Ex642Support.positiveTruncation X k ω ∂P)
        Filter.atTop
        (nhds (Ex642Support.positiveSeries P X)) := by
    have htmp :
        Filter.Tendsto (fun k : ℕ => ∑ i ∈ Finset.range (k + 1), fpos i) Filter.atTop
          (nhds (Ex642Support.positiveSeries P X)) := by
      change Filter.Tendsto
        ((fun n : ℕ => ∑ i ∈ Finset.range n, fpos i) ∘
          fun k : ℕ => k + 1)
        Filter.atTop (nhds (Ex642Support.positiveSeries P X))
      exact hPosTendsto0.comp hN
    refine htmp.congr' ?_
    exact Filter.Eventually.of_forall fun k => (hPosFinite k).symm
  let fneg : ℕ → ENNReal := fun i => (i : ENNReal) * P (X ⁻¹' ({(-(i : ℤ))} : Set ℤ))
  have hneg_hasSum : HasSum fneg (Ex642Support.negativeSeries P X) := by
    simpa [Ex642Support.negativeSeries, fneg] using (ENNReal.summable : Summable fneg).hasSum
  have hNegTendsto0 :
      Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, fneg i) Filter.atTop
        (nhds (Ex642Support.negativeSeries P X)) := by
    exact (ENNReal.hasSum_iff_tendsto_nat (r := Ex642Support.negativeSeries P X)).1 hneg_hasSum
  have hNegTendsto :
      Filter.Tendsto
        (fun k : ℕ => ∫⁻ ω, Ex642Support.negativeTruncation X k ω ∂P)
        Filter.atTop
        (nhds (Ex642Support.negativeSeries P X)) := by
    have htmp :
        Filter.Tendsto (fun k : ℕ => ∑ i ∈ Finset.range (k + 1), fneg i) Filter.atTop
          (nhds (Ex642Support.negativeSeries P X)) := by
      change Filter.Tendsto
        ((fun n : ℕ => ∑ i ∈ Finset.range n, fneg i) ∘
          fun k : ℕ => k + 1)
        Filter.atTop (nhds (Ex642Support.negativeSeries P X))
      exact hNegTendsto0.comp hN
    refine htmp.congr' ?_
    exact Filter.Eventually.of_forall fun k => (hNegFinite k).symm
  have hPosL :
      Def65Support.posLIntegral P (fun ω => ((((X ω : ℤ) : ℝ) : EReal))) =
        Ex642Support.positiveSeries P X := by
    rw [Def65Support.posLIntegral, Ex642Support.posPart_eq_toNat,
      ← Ex642Support.positiveSeries_eq_lintegral P X hXm]
  have hNegL :
      Def65Support.negLIntegral P (fun ω => ((((X ω : ℤ) : ℝ) : EReal))) =
        Ex642Support.negativeSeries P X := by
    rw [Def65Support.negLIntegral, Ex642Support.negPart_eq_toNat_neg,
      ← Ex642Support.negativeSeries_eq_lintegral P X hXm]
  refine ⟨hPosFinite, hPosTendsto, hNegFinite, hNegTendsto, hPosL, hNegL, ?_⟩
  rw [expectation_eq_textbookIntegral]
  unfold textbookIntegral
  by_cases hBoth :
      Ex642Support.positiveSeries P X = ⊤ ∧ Ex642Support.negativeSeries P X = ⊤
  · simp [hPosL, hNegL, hBoth]
  · simp [hPosL, hNegL, hBoth]
