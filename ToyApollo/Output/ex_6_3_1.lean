import Mathlib
import ToyApollo.Output.def_6_5
import ToyApollo.Output.ex_6_3_1_harmonic

open MeasureTheory
open scoped BigOperators

noncomputable section

/-!
Example 6.3.1 formalizes the discrete Cauchy-type law on `ℤ` and proves that the
textbook real Lebesgue integral of `X(ω) = ω` is undefined because both positive
and negative parts are infinite.
-/

noncomputable def ex631BaseMass (z : ℤ) : ℝ :=
  (((Int.natAbs z : ℝ) ^ 2)⁻¹)

lemma ex631BaseMass_nonneg (z : ℤ) : 0 ≤ ex631BaseMass z := by
  exact inv_nonneg.mpr (sq_nonneg _)

lemma ex631BaseMass_summable : Summable ex631BaseMass := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa [ex631BaseMass, Int.natAbs_natCast] using
      (Real.summable_nat_pow_inv (p := 2)).2 (by norm_num)
  · simpa [ex631BaseMass, Int.natAbs_neg, Int.natAbs_natCast] using
      (Real.summable_nat_pow_inv (p := 2)).2 (by norm_num)

lemma ex631BaseMass_one_pos : 0 < ex631BaseMass 1 := by
  norm_num [ex631BaseMass]

noncomputable def ex631TotalMass : ℝ :=
  ∑' z : ℤ, ex631BaseMass z

lemma ex631TotalMass_pos : 0 < ex631TotalMass := by
  have hle : ex631BaseMass 1 ≤ ex631TotalMass := by
    simpa [ex631TotalMass] using
      (Summable.le_tsum ex631BaseMass_summable 1 (by
        intro j hj
        exact ex631BaseMass_nonneg j))
  exact lt_of_lt_of_le ex631BaseMass_one_pos hle

noncomputable def ex631NormConst : ℝ :=
  ex631TotalMass⁻¹

lemma ex631NormConst_pos : 0 < ex631NormConst := by
  exact inv_pos.mpr ex631TotalMass_pos

noncomputable def ex631WeightR (z : ℤ) : ℝ :=
  ex631NormConst * ex631BaseMass z

lemma ex631WeightR_nonneg (z : ℤ) : 0 ≤ ex631WeightR z := by
  exact mul_nonneg ex631NormConst_pos.le (ex631BaseMass_nonneg z)

noncomputable def ex631PMF : PMF ℤ :=
  ⟨fun z => ENNReal.ofReal (ex631WeightR z), by
    have hnonneg : ∀ z : ℤ, 0 ≤ ex631WeightR z := ex631WeightR_nonneg
    have hs : Summable ex631WeightR := by
      unfold ex631WeightR
      exact ex631BaseMass_summable.mul_left _
    have htsum : ∑' z : ℤ, ENNReal.ofReal (ex631WeightR z) = 1 := by
      calc
        ∑' z : ℤ, ENNReal.ofReal (ex631WeightR z)
            = ENNReal.ofReal (∑' z : ℤ, ex631WeightR z) := by
                symm
                exact ENNReal.ofReal_tsum_of_nonneg hnonneg hs
        _ = ENNReal.ofReal (ex631NormConst * ex631TotalMass) := by
              congr
              exact (ex631BaseMass_summable.hasSum.mul_left _).tsum_eq
        _ = 1 := by
              simpa [ex631NormConst, ex631TotalMass] using congrArg ENNReal.ofReal
                (inv_mul_cancel₀ ex631TotalMass_pos.ne')
    exact ((ENNReal.summable : Summable (fun z : ℤ => ENNReal.ofReal (ex631WeightR z)))).hasSum_iff.2
      htsum
  ⟩

noncomputable def ex631Measure : Measure ℤ :=
  ex631PMF.toMeasure

noncomputable def ex631RV : ℤ → EReal :=
  fun z => ((z : ℝ) : EReal)

lemma ex631Measure_apply_singleton (z : ℤ) :
    ex631Measure {z} = ENNReal.ofReal (ex631WeightR z) := by
  change ex631PMF.toMeasure {z} = ENNReal.ofReal (ex631WeightR z)
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton z)]
  rfl

lemma ex631PMF_tsum : (∑' z : ℤ, ex631PMF z) = 1 := by
  exact ex631PMF.tsum_coe

noncomputable def ex631PositiveHarmonic (z : ℤ) : NNReal :=
  if hz : 0 < z then
    ⟨ex631NormConst * (1 / (Int.natAbs z : ℝ)), by
      have hInv : 0 ≤ (1 / (Int.natAbs z : ℝ)) := by positivity
      exact mul_nonneg ex631NormConst_pos.le hInv⟩
  else
    0

noncomputable def ex631NegativeHarmonic (z : ℤ) : NNReal :=
  if hz : z < 0 then
    ⟨ex631NormConst * (1 / (Int.natAbs z : ℝ)), by
      have hInv : 0 ≤ (1 / (Int.natAbs z : ℝ)) := by positivity
      exact mul_nonneg ex631NormConst_pos.le hInv⟩
  else
    0

noncomputable def ex631HarmonicTerm (n : ℕ) : NNReal :=
  Ex631Harmonic.scaledTerm ex631NormConst n

lemma ex631HarmonicTerm_not_summable :
    ¬ Summable (fun n : ℕ => (ex631HarmonicTerm n : ℝ)) := by
  simpa [ex631HarmonicTerm] using Ex631Harmonic.scaledTerm_not_summable ex631NormConst_pos

lemma ex631HarmonicTerm_tsum_eq_top :
    (∑' n : ℕ, ((ex631HarmonicTerm n : NNReal) : ENNReal)) = ⊤ := by
  simpa [ex631HarmonicTerm] using
    Ex631Harmonic.scaledTerm_tsum_eq_top ex631NormConst_pos

lemma ex631PositiveHarmonic_nat_zero :
    (ex631PositiveHarmonic 0 : ℝ) = 0 := by
  simp [ex631PositiveHarmonic]

lemma ex631PositiveHarmonic_nat_succ (n : ℕ) :
    (ex631PositiveHarmonic (n + 1 : ℤ) : ℝ) =
      ex631NormConst * (1 / (n + 1 : ℝ)) := by
  have hz : (0 : ℤ) < (n + 1 : ℤ) := by
    exact_mod_cast Nat.succ_pos n
  rw [ex631PositiveHarmonic, dif_pos hz]
  change ex631NormConst * (1 / ((Int.natAbs ((n + 1 : ℤ)) : ℝ))) =
      ex631NormConst * (1 / (n + 1 : ℝ))
  have hnat : (((n + 1 : ℤ).natAbs : ℕ) : ℝ) = (n + 1 : ℝ) := by
    exact_mod_cast Int.natAbs_natCast (n + 1)
  rw [hnat]

lemma ex631PositiveHarmonic_neg (n : ℕ) :
    (ex631PositiveHarmonic (-((n : ℤ))) : ℝ) = 0 := by
  by_cases hn : n = 0
  · subst hn
    simp [ex631PositiveHarmonic]
  · have hle : ¬ 0 < (-((n : ℤ))) := by
      have hge : (-((n : ℤ))) ≤ 0 := by
        exact neg_nonpos.mpr (by exact_mod_cast Nat.zero_le n)
      exact not_lt_of_ge hge
    simp [ex631PositiveHarmonic, hle]

lemma ex631NegativeHarmonic_nat (n : ℕ) :
    (ex631NegativeHarmonic (n : ℤ) : ℝ) = 0 := by
  by_cases hn : n = 0
  · subst hn
    simp [ex631NegativeHarmonic]
  · have hlt : ¬ ((n : ℤ) < 0) := by
      exact not_lt_of_ge (by exact_mod_cast Nat.zero_le n)
    simp [ex631NegativeHarmonic, hlt]

lemma ex631NegativeHarmonic_neg_succ (n : ℕ) :
    (ex631NegativeHarmonic (-((n + 1 : ℕ) : ℤ)) : ℝ) =
      ex631NormConst * (1 / (n + 1 : ℝ)) := by
  have hz : (-((n + 1 : ℕ) : ℤ)) < 0 := by
    have hpos : (0 : ℤ) < (n + 1 : ℤ) := by
      exact_mod_cast Nat.succ_pos n
    exact neg_neg_iff_pos.mpr hpos
  rw [ex631NegativeHarmonic, dif_pos hz]
  change ex631NormConst * (1 / ((Int.natAbs (-((n + 1 : ℕ) : ℤ)) : ℝ))) =
      ex631NormConst * (1 / (n + 1 : ℝ))
  have hnat : (((-((n + 1 : ℕ) : ℤ)).natAbs : ℕ) : ℝ) = (n + 1 : ℝ) := by
    have hnatNat : (-((n + 1 : ℕ) : ℤ)).natAbs = n + 1 := by
      rw [Int.natAbs_neg, Int.natAbs_natCast]
    simpa [Nat.cast_add] using congrArg (fun m : ℕ => (m : ℝ)) hnatNat
  rw [hnat]

set_option maxHeartbeats 800000 in
lemma ex631PositiveHarmonic_not_summable :
    ¬ Summable (fun z : ℤ => (ex631PositiveHarmonic z : ℝ)) := by
  intro hs
  rcases (summable_int_iff_summable_nat_and_neg).1 hs with ⟨hNat, _⟩
  have hTail : Summable (fun n : ℕ => (ex631PositiveHarmonic (((n + 1 : ℕ) : ℤ)) : ℝ)) := by
    exact hNat.comp_injective Nat.succ_injective
  have hHarm : Summable (fun n : ℕ => ex631NormConst * (1 / (n + 1 : ℝ))) := by
    refine hTail.congr ?_
    intro n
    simpa using ex631PositiveHarmonic_nat_succ n
  exact Ex631Harmonic.scaledTerm_not_summable ex631NormConst_pos <| hHarm.congr
    (fun n => (Ex631Harmonic.scaledTerm_coe ex631NormConst_pos n).symm)

set_option maxHeartbeats 800000 in
lemma ex631NegativeHarmonic_not_summable :
    ¬ Summable (fun z : ℤ => (ex631NegativeHarmonic z : ℝ)) := by
  intro hs
  rcases (summable_int_iff_summable_nat_and_neg).1 hs with ⟨_, hNeg⟩
  have hTail : Summable (fun n : ℕ => (ex631NegativeHarmonic (-(((n + 1 : ℕ) : ℤ))) : ℝ)) := by
    exact hNeg.comp_injective Nat.succ_injective
  have hHarm : Summable (fun n : ℕ => ex631NormConst * (1 / (n + 1 : ℝ))) := by
    refine hTail.congr ?_
    intro n
    simpa using ex631NegativeHarmonic_neg_succ n
  exact Ex631Harmonic.scaledTerm_not_summable ex631NormConst_pos <| hHarm.congr
    (fun n => (Ex631Harmonic.scaledTerm_coe ex631NormConst_pos n).symm)

lemma ex631PositiveHarmonic_tsum_eq_top :
    (∑' z : ℤ, ((ex631PositiveHarmonic z : NNReal) : ENNReal)) = ⊤ := by
  exact (ENNReal.tsum_coe_eq_top_iff_not_summable_coe (f := ex631PositiveHarmonic)).2
    ex631PositiveHarmonic_not_summable

lemma ex631NegativeHarmonic_tsum_eq_top :
    (∑' z : ℤ, ((ex631NegativeHarmonic z : NNReal) : ENNReal)) = ⊤ := by
  exact (ENNReal.tsum_coe_eq_top_iff_not_summable_coe (f := ex631NegativeHarmonic)).2
    ex631NegativeHarmonic_not_summable

lemma ex631PositivePointwise (z : ℤ) :
    Def65Support.posPart ex631RV z * ex631Measure {z} =
      (ex631PositiveHarmonic z : ENNReal) := by
  by_cases hz : 0 < z
  · rw [ex631PositiveHarmonic, dif_pos hz, ENNReal.coe_nnreal_eq]
    rw [ex631Measure_apply_singleton]
    have hzreal : 0 < (z : ℝ) := by
      exact_mod_cast hz
    have habs : |(z : ℝ)| = (z : ℝ) := abs_of_pos hzreal
    simp [Def65Support.posPart, ex631RV]
    rw [← ENNReal.ofReal_mul hzreal.le]
    simp [ex631WeightR, ex631BaseMass, habs, pow_two]
    field_simp [hzreal.ne', ex631NormConst_pos.ne']
  · rw [ex631PositiveHarmonic, dif_neg hz, ENNReal.coe_nnreal_eq]
    rw [ex631Measure_apply_singleton]
    by_cases hz0 : z = 0
    · subst hz0
      simp [Def65Support.posPart, ex631RV]
    · have hzlt : z < 0 := by
        exact lt_of_le_of_ne (le_of_not_gt hz) hz0
      have hzreal : (z : ℝ) < 0 := by
        exact_mod_cast hzlt
      simp [Def65Support.posPart, ex631RV, hzreal.le, ex631WeightR]

lemma ex631NegativePointwise (z : ℤ) :
    Def65Support.negPart ex631RV z * ex631Measure {z} =
      (ex631NegativeHarmonic z : ENNReal) := by
  by_cases hz : z < 0
  · rw [ex631NegativeHarmonic, dif_pos hz, ENNReal.coe_nnreal_eq]
    rw [ex631Measure_apply_singleton]
    have hzreal : (z : ℝ) < 0 := by
      exact_mod_cast hz
    have habs : |(z : ℝ)| = -(z : ℝ) := abs_of_neg hzreal
    have hnegNonneg : 0 ≤ -(z : ℝ) := by
      linarith
    simp [Def65Support.negPart, ex631RV]
    rw [← ENNReal.ofReal_mul hnegNonneg]
    simp [ex631WeightR, ex631BaseMass, habs, pow_two]
    field_simp [hzreal.ne, ex631NormConst_pos.ne']
  · rw [ex631NegativeHarmonic, dif_neg hz, ENNReal.coe_nnreal_eq]
    rw [ex631Measure_apply_singleton]
    by_cases hz0 : z = 0
    · subst hz0
      simp [Def65Support.negPart, ex631RV]
    · have hzpos : 0 < z := by
        exact lt_of_le_of_ne (le_of_not_gt hz) (Ne.symm hz0)
      have hzreal : 0 < (z : ℝ) := by
        exact_mod_cast hzpos
      simp [Def65Support.negPart, ex631RV, hzreal.le, ex631WeightR]

lemma ex631PosLIntegral_eq_top :
    Def65Support.posLIntegral ex631Measure ex631RV = ⊤ := by
  rw [Def65Support.posLIntegral, lintegral_countable']
  calc
    ∑' z : ℤ, Def65Support.posPart ex631RV z * ex631Measure {z}
        = ∑' z : ℤ, (ex631PositiveHarmonic z : ENNReal) := by
            exact tsum_congr ex631PositivePointwise
    _ = ⊤ := ex631PositiveHarmonic_tsum_eq_top

lemma ex631NegLIntegral_eq_top :
    Def65Support.negLIntegral ex631Measure ex631RV = ⊤ := by
  rw [Def65Support.negLIntegral, lintegral_countable']
  calc
    ∑' z : ℤ, Def65Support.negPart ex631RV z * ex631Measure {z}
        = ∑' z : ℤ, (ex631NegativeHarmonic z : ENNReal) := by
            exact tsum_congr ex631NegativePointwise
    _ = ⊤ := ex631NegativeHarmonic_tsum_eq_top

/-- Example 6.3.1: for the discrete Cauchy-type law on `ℤ`, the positive and
negative parts of `X(ω)=ω` are both infinite, so the textbook Lebesgue
integral is undefined. -/
theorem ex_6_3_1 :
    textbookIntegral ex631Measure ex631RV = none := by
  rw [textbookIntegral_eq_none_iff]
  exact ⟨ex631PosLIntegral_eq_top, ex631NegLIntegral_eq_top⟩
