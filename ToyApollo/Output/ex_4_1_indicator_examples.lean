import Mathlib
import ToyApollo.Output.thm_2_9
import ToyApollo.Output.thm_4_1

open MeasureTheory Set
open scoped Pointwise ENNReal

noncomputable section

/- Source-fidelity repair: the third example below uses the exact `vitaliSet`
constructed in Sect. 2.5 through `thm_2_9`, not an arbitrary non-Borel witness. -/

/-- The set of rational numbers in `ℝ`. -/
def rationalSet : Set ℝ := ((↑) : ℚ → ℝ) '' univ

theorem rationalSet_countable : rationalSet.Countable := by
  simpa [rationalSet] using Set.Countable.image Set.countable_univ ((↑) : ℚ → ℝ)

theorem rationalSet_measurable : MeasurableSet rationalSet := by
  exact rationalSet_countable.measurableSet

theorem measurable_indicator_rationalSet :
    Measurable (Set.indicator rationalSet (fun _ => (1 : ℝ))) := by
  exact (thm_4_1 rationalSet).2 rationalSet_measurable

theorem measurable_indicator_cantorSet :
    Measurable (Set.indicator cantorSet (fun _ => (1 : ℝ))) := by
  exact (thm_4_1 cantorSet).2 isClosed_cantorSet.measurableSet

/-- Two points chosen by the Sect. 2.5 Vitali construction cannot differ by a rational
unless they are the same representative. -/
lemma eq_of_mem_vitaliSet_of_sub_rat {x y : ℝ}
    (hx : x ∈ vitaliSet) (hy : y ∈ vitaliSet)
    (hxy : ∃ q : ℚ, x - y = q) : x = y := by
  rcases rep_equiv_of_mem_vitaliSet hx with ⟨Qx, hQx⟩
  rcases rep_equiv_of_mem_vitaliSet hy with ⟨Qy, hQy⟩
  subst x
  subst y
  have hrel : vitaliRel (rep Qx) (rep Qy) := by
    change ∃ q : ℚ, (rep Qx).1 - (rep Qy).1 = (q : ℝ)
    exact hxy
  have hQ : Qx = Qy := by
    calc
      Qx = Quotient.mk _ (rep Qx) := (rep_eq Qx).symm
      _ = Quotient.mk _ (rep Qy) := Quotient.sound hrel
      _ = Qy := rep_eq Qy
  simp [hQ]

lemma vitaliSet_translate_disjoint {q₁ q₂ : ℚ} (hne : q₁ ≠ q₂) :
    Disjoint ({((q₁ : ℚ) : ℝ)} + vitaliSet) ({((q₂ : ℚ) : ℝ)} + vitaliSet) := by
  refine disjoint_left.2 ?_
  intro z hz₁ hz₂
  rcases hz₁ with ⟨a₁, ha₁, v₁, hv₁, hz₁⟩
  rcases hz₂ with ⟨a₂, ha₂, v₂, hv₂, hz₂⟩
  simp only [mem_singleton_iff] at ha₁ ha₂
  subst a₁
  subst a₂
  have hv_eq : v₁ = v₂ := by
    refine eq_of_mem_vitaliSet_of_sub_rat hv₁ hv₂ ?_
    refine ⟨q₂ - q₁, ?_⟩
    norm_num [sub_eq_add_neg] at hz₁ hz₂ ⊢
    linarith
  apply hne
  have hreal : ((q₁ : ℚ) : ℝ) = ((q₂ : ℚ) : ℝ) := by
    linarith
  exact_mod_cast hreal

lemma pairwise_disjoint_vitaliSet_nat_translates :
    Pairwise
      (fun m n : ℕ =>
        Disjoint ({(((natShift m : RatShift) : ℚ) : ℝ)} + vitaliSet)
          ({(((natShift n : RatShift) : ℚ) : ℝ)} + vitaliSet)) := by
  intro m n hmn
  apply vitaliSet_translate_disjoint
  intro hrat
  apply hmn
  exact natShift_injective (Subtype.ext hrat)

lemma natShift_range_bounded :
    Bornology.IsBounded (range fun n : ℕ => (((natShift n : RatShift) : ℚ) : ℝ)) := by
  refine (Metric.isBounded_Icc (0 : ℝ) 1).subset ?_
  rintro x ⟨n, rfl⟩
  constructor
  · change (0 : ℝ) ≤ (((natShift n : RatShift) : ℚ) : ℝ)
    exact_mod_cast (natShift n).2.1
  · change (((natShift n : RatShift) : ℚ) : ℝ) ≤ (1 : ℝ)
    exact le_of_lt (by
      change (((natShift n : RatShift) : ℚ) : ℝ) < (1 : ℝ)
      exact_mod_cast (natShift n).2.2)

lemma volume_vitaliSet_eq_zero_of_measurable (hV : MeasurableSet vitaliSet) :
    volume vitaliSet = 0 := by
  exact Measure.addHaar_eq_zero_of_disjoint_translates volume
    (fun n : ℕ => (((natShift n : RatShift) : ℚ) : ℝ))
    natShift_range_bounded pairwise_disjoint_vitaliSet_nat_translates hV

abbrev SmallRatShift := {q : ℚ // -1 < q ∧ q < 1}

lemma unitInterval_subset_iUnion_vitaliSet_rat_translates :
    UnitInterval ⊆ ⋃ q : SmallRatShift, {(((q : SmallRatShift) : ℚ) : ℝ)} + vitaliSet := by
  intro x hx
  let ux : UnitInterval := ⟨x, hx⟩
  let Q : VitaliQuot := Quotient.mk _ ux
  rcases mk_rel_rep ux with ⟨q, hq⟩
  have hq_as_real : ((q : ℚ) : ℝ) = x - (rep Q).1 := hq.symm
  have hq_gt_real : ((-1 : ℚ) : ℝ) < ((q : ℚ) : ℝ) := by
    rw [hq_as_real]
    have hx_nonneg : 0 ≤ x := hx.1
    have hrep_lt : (rep Q).1 < 1 := (rep Q).2.2
    norm_num
    linarith
  have hq_lt_real : ((q : ℚ) : ℝ) < ((1 : ℚ) : ℝ) := by
    rw [hq_as_real]
    have hx_lt : x < 1 := hx.2
    have hrep_nonneg : 0 ≤ (rep Q).1 := (rep Q).2.1
    norm_num
    linarith
  let qsmall : SmallRatShift := ⟨q, by
    constructor
    · exact_mod_cast hq_gt_real
    · exact_mod_cast hq_lt_real⟩
  refine mem_iUnion.2 ⟨qsmall, ?_⟩
  refine ⟨((q : ℚ) : ℝ), by simp [qsmall], (rep Q).1, mem_vitaliSet_rep Q, ?_⟩
  linarith

theorem vitaliSet_not_measurableSet : ¬ MeasurableSet vitaliSet := by
  intro hV
  have hzero : volume vitaliSet = 0 := volume_vitaliSet_eq_zero_of_measurable hV
  have htranslate_zero :
      ∀ q : SmallRatShift, volume ({(((q : SmallRatShift) : ℚ) : ℝ)} + vitaliSet) = 0 := by
    intro q
    calc
      volume ({(((q : SmallRatShift) : ℚ) : ℝ)} + vitaliSet) = volume vitaliSet := by
        simp only [image_add_left, measure_preimage_add, singleton_add]
      _ = 0 := hzero
  have hUnionZero :
      volume (⋃ q : SmallRatShift, {(((q : SmallRatShift) : ℚ) : ℝ)} + vitaliSet) = 0 := by
    apply le_antisymm
    · calc
        volume (⋃ q : SmallRatShift, {(((q : SmallRatShift) : ℚ) : ℝ)} + vitaliSet) ≤
            ∑' q : SmallRatShift, volume ({(((q : SmallRatShift) : ℚ) : ℝ)} + vitaliSet) :=
          measure_iUnion_le _
        _ = 0 := by
          rw [tsum_congr htranslate_zero]
          simp
    · exact zero_le
  have hUnitZero : volume UnitInterval = 0 :=
    le_antisymm
      ((measure_mono unitInterval_subset_iUnion_vitaliSet_rat_translates).trans_eq hUnionZero)
      zero_le
  have hUnitPositive : volume UnitInterval ≠ 0 := by
    rw [UnitInterval, Real.volume_Ico]
    norm_num
  exact hUnitPositive hUnitZero

theorem not_measurable_indicator_vitaliSet :
    ¬ Measurable (Set.indicator vitaliSet (fun _ => (1 : ℝ))) := by
  intro h
  exact vitaliSet_not_measurableSet ((thm_4_1 vitaliSet).1 h)

/--
Examples of indicator functions: the indicators of `ℚ` and of the Cantor set are Borel
measurable, while the indicator of the Sect. 2.5 Vitali set is not Borel measurable.
-/
theorem ex_4_1_indicator_examples :
    Measurable (Set.indicator rationalSet (fun _ => (1 : ℝ))) ∧
      Measurable (Set.indicator cantorSet (fun _ => (1 : ℝ))) ∧
      ¬ Measurable (Set.indicator vitaliSet (fun _ => (1 : ℝ))) := by
  exact ⟨measurable_indicator_rationalSet, measurable_indicator_cantorSet,
    not_measurable_indicator_vitaliSet⟩

end
