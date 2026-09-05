/-
TASK ID: ex_2_1_1
TYPE: Example_Proof
SOURCE PLAN: 40_chap2_countable_sets
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_02.def_2_1




-- WRITE FINAL LEAN CODE BELOW

open Set

noncomputable section

private theorem ex_2_1_1_countable_of_strict {α : Type*} {A : Set α}
    (hA : IsCountableSet A) : A.Countable := by
  rw [IsCountableSet, SameCardinality] at hA
  rcases hA with ⟨e⟩
  haveI : Countable A := Countable.of_equiv (Set.univ : Set ℕ) e.symm
  exact Set.countable_coe_iff.mp inferInstance

private theorem ex_2_1_1_infinite_of_strict {α : Type*} {A : Set α}
    (hA : IsCountableSet A) : A.Infinite := by
  rw [IsCountableSet, SameCardinality] at hA
  rcases hA with ⟨e⟩
  have hUnivSet : (Set.univ : Set ℕ).Infinite := Set.infinite_univ
  have hUnivType : Infinite (Set.univ : Set ℕ) := hUnivSet.to_subtype
  have htype : Infinite A := (Equiv.infinite_iff e).mpr hUnivType
  exact Set.infinite_coe_iff.mp htype

private theorem ex_2_1_1_strict_of_countable_infinite {α : Type*} {A : Set α}
    (hcnt : A.Countable) (hinf : A.Infinite) : IsCountableSet A := by
  rw [IsCountableSet, SameCardinality]
  haveI : Countable A := hcnt.to_subtype
  haveI : Infinite A := hinf.to_subtype
  haveI : Encodable A := Encodable.ofCountable A
  letI : Denumerable A := Denumerable.ofEncodableOfInfinite A
  exact ⟨(Denumerable.eqv A).trans (Equiv.Set.univ ℕ).symm⟩

private theorem ex_2_1_1_countable_of_not_uncountable {α : Type*} {A : Set α}
    (hA : ¬ IsUncountableSet A) : A.Countable := by
  by_cases hInf : A.Infinite
  · have hStrict : IsCountableSet A := by
      by_contra hNotStrict
      exact hA (by
        rw [IsUncountableSet]
        exact ⟨hInf, hNotStrict⟩)
    exact ex_2_1_1_countable_of_strict hStrict
  · exact (Set.not_infinite.mp hInf).countable

 
def positiveEvenNaturals : Set ℕ :=
  {n | ∃ k : ℕ, n = 2 * (k + 1)}

 
def positiveRationals : Set ℚ :=
  {q | 0 < q}

 
def positiveRationalCoprimePairs : Set (ℕ × ℕ) :=
  {p | 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2}

 
structure CountableSetExamples where
  positiveEvenNaturals : Set ℕ
  positiveRationals : Set ℚ

 
def ex_2_1_1 : CountableSetExamples where
  positiveEvenNaturals := positiveEvenNaturals
  positiveRationals := positiveRationals

 
def positiveEvenEnumeration (n : ℕ) : positiveEvenNaturals :=
  ⟨2 * (n + 1), ⟨n, rfl⟩⟩

 
theorem positiveEvenEnumeration_injective :
    Function.Injective positiveEvenEnumeration := by
  intro m n h
  have hval : 2 * (m + 1) = 2 * (n + 1) := congrArg Subtype.val h
  omega

 
theorem positiveEvenEnumeration_surjective :
    Function.Surjective positiveEvenEnumeration := by
  intro m
  rcases m.property with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  apply Subtype.ext
  simp [positiveEvenEnumeration, hk]

 
noncomputable def positiveEvenEquiv : ℕ ≃ positiveEvenNaturals :=
  Equiv.ofBijective positiveEvenEnumeration
    ⟨positiveEvenEnumeration_injective, positiveEvenEnumeration_surjective⟩

 
theorem ex_2_1_1_positive_even_same_cardinality :
    SameCardinality (Set.univ : Set ℕ) positiveEvenNaturals := by
  rw [SameCardinality]
  exact ⟨(Equiv.Set.univ ℕ).trans positiveEvenEquiv⟩

 
theorem ex_2_1_1_positive_even_countable :
    IsCountableSet ex_2_1_1.positiveEvenNaturals := by
  change IsCountableSet positiveEvenNaturals
  rw [IsCountableSet, SameCardinality]
  exact ⟨positiveEvenEquiv.symm.trans (Equiv.Set.univ ℕ).symm⟩

 
def integerNegEquiv : ℤ ≃ ℤ where
  toFun z := -z
  invFun z := -z
  left_inv := by
    intro z
    simp
  right_inv := by
    intro z
    simp

 
noncomputable def integerListingEquiv : ℕ ≃ (Set.univ : Set ℤ) :=
  (Equiv.intEquivNat.symm.trans integerNegEquiv).trans (Equiv.Set.univ ℤ).symm

 
def integerListing (n : ℕ) : ℤ :=
  (integerListingEquiv n).1

 
theorem ex_2_1_1_integers_countable :
    IsCountableSet (Set.univ : Set ℤ) := by
  rw [IsCountableSet, SameCardinality]
  exact ⟨integerListingEquiv.symm.trans (Equiv.Set.univ ℕ).symm⟩

 
theorem ex_2_1_1_infinite_subset_countable {α : Type*} {A B : Set α}
    (hB : IsCountableSet B) (hAB : A ⊆ B) (hAinf : A.Infinite) :
    IsCountableSet A := by
  exact ex_2_1_1_strict_of_countable_infinite
    (Set.Countable.mono hAB (ex_2_1_1_countable_of_strict hB)) hAinf

 
theorem ex_2_1_1_union_countable {α : Type*} {A B : Set α}
    (hA : IsCountableSet A) (hB : IsCountableSet B) :
    IsCountableSet (A ∪ B) := by
  have hcnt : (A ∪ B).Countable :=
    (ex_2_1_1_countable_of_strict hA).union (ex_2_1_1_countable_of_strict hB)
  have hinf : (A ∪ B).Infinite :=
    Set.Infinite.mono (by intro x hx; exact Or.inl hx) (ex_2_1_1_infinite_of_strict hA)
  exact ex_2_1_1_strict_of_countable_infinite hcnt hinf

 
theorem ex_2_1_1_union_uncountable_left_or_right {α : Type*} {A B : Set α}
    (hU : IsUncountableSet (A ∪ B)) :
    IsUncountableSet A ∨ IsUncountableSet B := by
  by_contra hnone
  rw [not_or] at hnone
  rw [IsUncountableSet] at hU
  have hcntA : A.Countable := ex_2_1_1_countable_of_not_uncountable hnone.1
  have hcntB : B.Countable := ex_2_1_1_countable_of_not_uncountable hnone.2
  have hStrictUnion : IsCountableSet (A ∪ B) :=
    ex_2_1_1_strict_of_countable_infinite (hcntA.union hcntB) hU.1
  exact hU.2 hStrictUnion

 
theorem ex_2_1_1_prod_countable {α β : Type*} {A : Set α} {B : Set β}
    (hA : IsCountableSet A) (hB : IsCountableSet B) :
    IsCountableSet (A ×ˢ B) := by
  have hcnt : (A ×ˢ B).Countable :=
    (ex_2_1_1_countable_of_strict hA).prod (ex_2_1_1_countable_of_strict hB)
  have hinf : (A ×ˢ B).Infinite :=
    Set.Infinite.prod_left (ex_2_1_1_infinite_of_strict hA)
      (ex_2_1_1_infinite_of_strict hB).nonempty
  exact ex_2_1_1_strict_of_countable_infinite hcnt hinf

 
theorem ex_2_1_1_nat_prod_countable :
    IsCountableSet (Set.univ : Set (ℕ × ℕ)) := by
  exact ex_2_1_1_strict_of_countable_infinite
    (Set.to_countable (Set.univ : Set (ℕ × ℕ)))
    (Set.infinite_univ : (Set.univ : Set (ℕ × ℕ)).Infinite)

 
def positiveRationalCoprimePair (q : positiveRationals) : positiveRationalCoprimePairs :=
  ⟨(q.1.num.natAbs, q.1.den), by
    constructor
    · exact Int.natAbs_pos.mpr (ne_of_gt ((Rat.num_pos).2 q.2))
    · constructor
      · exact Rat.den_pos q.1
      · exact q.1.reduced⟩

 
def positiveRationalCoprimePairValue (q : positiveRationals) : ℕ × ℕ :=
  (positiveRationalCoprimePair q).1

 
theorem positiveRationalCoprimePair_injective :
    Function.Injective positiveRationalCoprimePair := by
  intro q r h
  have hpair : (q.1.num.natAbs, q.1.den) = (r.1.num.natAbs, r.1.den) :=
    congrArg Subtype.val h
  apply Subtype.ext
  apply Rat.ext
  · have hnumAbs : q.1.num.natAbs = r.1.num.natAbs := congrArg Prod.fst hpair
    have hqnonneg : 0 ≤ q.1.num := le_of_lt ((Rat.num_pos).2 q.2)
    have hrnonneg : 0 ≤ r.1.num := le_of_lt ((Rat.num_pos).2 r.2)
    have hq : (q.1.num.natAbs : ℤ) = q.1.num := Int.ofNat_natAbs_of_nonneg hqnonneg
    have hr : (r.1.num.natAbs : ℤ) = r.1.num := Int.ofNat_natAbs_of_nonneg hrnonneg
    have hnumInt : (q.1.num.natAbs : ℤ) = (r.1.num.natAbs : ℤ) := by
      exact_mod_cast hnumAbs
    rwa [hq, hr] at hnumInt
  · exact congrArg Prod.snd hpair

 
theorem positiveRationalCoprimePairValue_injective :
    Function.Injective positiveRationalCoprimePairValue := by
  intro q r h
  apply positiveRationalCoprimePair_injective
  apply Subtype.ext
  exact h

 
noncomputable def positiveRationalCoprimePairRangeEquiv :
    positiveRationals ≃ Set.range positiveRationalCoprimePairValue :=
  Equiv.ofInjective positiveRationalCoprimePairValue positiveRationalCoprimePairValue_injective

 
theorem positiveRationalCoprimePairRange_subset :
    Set.range positiveRationalCoprimePairValue ⊆ positiveRationalCoprimePairs := by
  intro p hp
  rcases hp with ⟨q, rfl⟩
  exact (positiveRationalCoprimePair q).2

 
theorem ex_2_1_1_positive_rationals_same_cardinality_coprime_pair_subset :
    SameCardinality positiveRationals (Set.range positiveRationalCoprimePairValue) := by
  rw [SameCardinality]
  exact ⟨positiveRationalCoprimePairRangeEquiv⟩

private theorem ex_2_1_1_positive_rationals_infinite : positiveRationals.Infinite := by
  let f : ℕ → ℚ := fun n => ((n + 1 : ℕ) : ℚ)
  have hf : Function.Injective f := by
    intro m n h
    have hnat : m + 1 = n + 1 := Nat.cast_injective h
    omega
  have hRange : (Set.range f).Infinite := Set.infinite_range_of_injective hf
  refine Set.Infinite.mono ?_ hRange
  intro q hq
  rcases hq with ⟨n, rfl⟩
  dsimp [positiveRationals, f]
  positivity

 
theorem ex_2_1_1_positive_rationals_countable :
    IsCountableSet ex_2_1_1.positiveRationals := by
  change IsCountableSet positiveRationals
  have hCoprimeCountable : positiveRationalCoprimePairs.Countable :=
    (Set.to_countable (Set.univ : Set (ℕ × ℕ))).mono (by
      intro p _hp
      trivial)
  have hRangeCountable : (Set.range positiveRationalCoprimePairValue).Countable :=
    hCoprimeCountable.mono positiveRationalCoprimePairRange_subset
  haveI : Countable (Set.range positiveRationalCoprimePairValue) :=
    hRangeCountable.to_subtype
  haveI : Countable positiveRationals :=
    Countable.of_equiv (Set.range positiveRationalCoprimePairValue)
      positiveRationalCoprimePairRangeEquiv.symm
  have hcnt : positiveRationals.Countable :=
    Set.countable_coe_iff.mp (by infer_instance : Countable positiveRationals)
  exact ex_2_1_1_strict_of_countable_infinite
    hcnt ex_2_1_1_positive_rationals_infinite

private theorem ex_2_1_1_unit_interval_rationals_infinite :
    ({q : ℚ | 0 < q ∧ q < 1} : Set ℚ).Infinite := by
  let f : ℕ → ℚ := fun n => (1 : ℚ) / ((n + 2 : ℕ) : ℚ)
  have hf : Function.Injective f := by
    intro m n h
    change (1 : ℚ) / (((m + 2 : ℕ) : ℚ)) =
        (1 : ℚ) / (((n + 2 : ℕ) : ℚ)) at h
    have hInv : (((m + 2 : ℕ) : ℚ))⁻¹ = (((n + 2 : ℕ) : ℚ))⁻¹ := by
      simpa [one_div] using h
    have hden : (((m + 2 : ℕ) : ℚ)) = (((n + 2 : ℕ) : ℚ)) := inv_inj.mp hInv
    have hnat : m + 2 = n + 2 := Nat.cast_injective hden
    omega
  have hRange : (Set.range f).Infinite := Set.infinite_range_of_injective hf
  refine Set.Infinite.mono ?_ hRange
  intro q hq
  rcases hq with ⟨n, rfl⟩
  dsimp [f]
  constructor
  · positivity
  · have hden_gt_one : (1 : ℚ) < ((n + 2 : ℕ) : ℚ) := by
      exact_mod_cast (by omega : 1 < n + 2)
    simpa [one_div] using inv_lt_one_of_one_lt₀ hden_gt_one

 
theorem ex_2_1_1_unit_interval_rationals_countable :
    IsCountableSet {q : ℚ | 0 < q ∧ q < 1} := by
  exact ex_2_1_1_strict_of_countable_infinite
    (Set.Countable.mono (by
      intro q hq
      exact hq.1) (ex_2_1_1_countable_of_strict ex_2_1_1_positive_rationals_countable))
    ex_2_1_1_unit_interval_rationals_infinite
