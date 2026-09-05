/-
TASK ID: thm_2_9_vitali_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_02.def_2_5

open Set
open scoped BigOperators

noncomputable section

namespace MATVitaliSupport

abbrev UnitInterval := Set.Ico (0 : ℝ) 1
abbrev ClosedUnitInterval := Set.Icc (0 : ℝ) 1
abbrev UnitPowerset := {A : Set ℝ // A ⊆ ClosedUnitInterval}
abbrev RatShift := {q : ℚ // 0 ≤ q ∧ q < 1}

def vitaliRel (x y : UnitInterval) : Prop :=
  ∃ q : ℚ, x.1 - y.1 = q

instance : Setoid UnitInterval where
  r := vitaliRel
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      refine ⟨0, by norm_num⟩
    · intro x y hxy
      rcases hxy with ⟨q, hq⟩
      refine ⟨-q, ?_⟩
      norm_num [sub_eq_add_neg] at hq ⊢
      linarith
    · intro x y z hxy hyz
      rcases hxy with ⟨q1, h1⟩
      rcases hyz with ⟨q2, h2⟩
      refine ⟨q1 + q2, ?_⟩
      norm_num [sub_eq_add_neg] at h1 h2 ⊢
      linarith

abbrev VitaliQuot := Quotient (inferInstance : Setoid UnitInterval)

def rep (Q : VitaliQuot) : UnitInterval :=
  Quotient.out Q

theorem rep_eq (Q : VitaliQuot) : Quotient.mk _ (rep Q) = Q :=
  Quotient.out_eq Q

def vitaliSet : Set ℝ :=
  Set.range fun Q : VitaliQuot => (rep Q).1

def modShift (A : Set ℝ) (r : RatShift) : Set ℝ :=
  (fun x : ℝ => Int.fract (x + (r : ℚ))) '' A

def shiftSet (r : RatShift) : Set ℝ :=
  modShift vitaliSet r

lemma mem_vitaliSet_rep (Q : VitaliQuot) : (rep Q).1 ∈ vitaliSet := by
  exact ⟨Q, rfl⟩

lemma unitInterval_subset_closedUnitInterval :
    UnitInterval ⊆ ClosedUnitInterval :=
  Ico_subset_Icc_self

lemma vitaliSet_subset_unitInterval : vitaliSet ⊆ UnitInterval := by
  intro x hx
  rcases hx with ⟨Q, rfl⟩
  exact (rep Q).2

lemma vitaliSet_subset_closedUnitInterval : vitaliSet ⊆ ClosedUnitInterval :=
  fun _ hx => unitInterval_subset_closedUnitInterval (vitaliSet_subset_unitInterval hx)

lemma modShift_subset_unitInterval (A : Set ℝ) (r : RatShift) :
    modShift A r ⊆ UnitInterval := by
  intro x hx
  rcases hx with ⟨y, -, rfl⟩
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

lemma modShift_subset_closedUnitInterval (A : Set ℝ) (r : RatShift) :
    modShift A r ⊆ ClosedUnitInterval :=
  fun _ hx => unitInterval_subset_closedUnitInterval (modShift_subset_unitInterval A r hx)

lemma shiftSet_subset_unitInterval (r : RatShift) : shiftSet r ⊆ Set.Ico (0 : ℝ) 1 := by
  exact modShift_subset_unitInterval vitaliSet r

lemma shiftSet_subset_closedUnitInterval (r : RatShift) :
    shiftSet r ⊆ ClosedUnitInterval :=
  modShift_subset_closedUnitInterval vitaliSet r

lemma rep_equiv_of_mem_vitaliSet {x : ℝ} (hx : x ∈ vitaliSet) :
    ∃ Q : VitaliQuot, (rep Q).1 = x := by
  simpa [vitaliSet] using hx

lemma rep_rel_mk (x : UnitInterval) : vitaliRel (rep (Quotient.mk _ x)) x := by
  exact Quotient.exact (rep_eq (Quotient.mk _ x))

lemma mk_rel_rep (x : UnitInterval) : vitaliRel x (rep (Quotient.mk _ x)) := by
  rcases rep_rel_mk x with ⟨q, hq⟩
  refine ⟨-q, ?_⟩
  norm_num [sub_eq_add_neg] at hq ⊢
  linarith

lemma shift_exists_of_mem_unitInterval (x : UnitInterval) :
    ∃ r : RatShift, x.1 ∈ shiftSet r := by
  let Q : VitaliQuot := Quotient.mk _ x
  rcases mk_rel_rep x with ⟨q, hq⟩
  let r : RatShift := ⟨Int.fract q, Int.fract_nonneg q, Int.fract_lt_one q⟩
  refine ⟨r, ?_⟩
  refine ⟨(rep Q).1, mem_vitaliSet_rep Q, ?_⟩
  have hqz : ∃ z : ℤ, q - (r : ℚ) = z := by
    rcases (Int.fract_eq_iff (a := q) (b := (r : ℚ))).mp rfl with ⟨_, _, z, hz⟩
    exact ⟨z, hz⟩
  rcases hqz with ⟨z, hz⟩
  have hxself : Int.fract x.1 = x.1 := by
    exact Int.fract_eq_self.mpr x.2
  have hstep : Int.fract ((rep Q).1 + (r : ℚ)) = Int.fract x.1 := by
    have hxeq : x.1 = (rep Q).1 + (q : ℚ) := by
      linarith
    rw [hxeq]
    have hz' : q = (r : ℚ) + z := by
      linarith
    have : (rep Q).1 + (q : ℚ) = (rep Q).1 + (r : ℚ) + (z : ℤ) := by
      calc
        (rep Q).1 + (q : ℚ) = (rep Q).1 + ((r : ℚ) + z) := by norm_num [hz']
        _ = (rep Q).1 + (r : ℚ) + (z : ℤ) := by ring
    rw [this, Int.fract_add_intCast]
  simpa [hxself] using hstep

lemma unitInterval_eq_iUnion_shiftSet : Set.Ico (0 : ℝ) 1 = ⋃ r : RatShift, shiftSet r := by
  ext x
  constructor
  · intro hx
    let ux : UnitInterval := ⟨x, hx⟩
    rcases shift_exists_of_mem_unitInterval ux with ⟨r, hr⟩
    exact mem_iUnion.2 ⟨r, hr⟩
  · intro hx
    rcases mem_iUnion.1 hx with ⟨r, hr⟩
    exact shiftSet_subset_unitInterval r hr

lemma shiftSet_disjoint {r1 r2 : RatShift} (hne : r1 ≠ r2) :
    Disjoint (shiftSet r1) (shiftSet r2) := by
  refine disjoint_left.2 ?_
  intro z hz1 hz2
  rcases hz1 with ⟨v1, hv1, hz1'⟩
  rcases hz2 with ⟨v2, hv2, hz2'⟩
  rcases rep_equiv_of_mem_vitaliSet hv1 with ⟨Q1, hQ1⟩
  rcases rep_equiv_of_mem_vitaliSet hv2 with ⟨Q2, hQ2⟩
  subst hQ1
  subst hQ2
  have hfract :
      Int.fract ((rep Q1).1 + (r1 : ℚ)) = Int.fract ((rep Q2).1 + (r2 : ℚ)) := by
    simpa [hz1', hz2']
  rcases (Int.fract_eq_fract).1 hfract with ⟨k, hk⟩
  have hrel : vitaliRel (rep Q1) (rep Q2) := by
    refine ⟨(k : ℚ) - (r1 : ℚ) + (r2 : ℚ), ?_⟩
    norm_num [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] at hk ⊢
    linarith
  have hQQ : Q1 = Q2 := by
    calc
      Q1 = Quotient.mk _ (rep Q1) := (rep_eq Q1).symm
      _ = Quotient.mk _ (rep Q2) := Quotient.sound hrel
      _ = Q2 := rep_eq Q2
  have hkRat : (r1 : ℚ) - r2 = k := by
    have hk' : ((r1 : ℚ) : ℝ) - (r2 : ℚ) = (k : ℤ) := by
      simpa [hQQ] using hk
    exact_mod_cast hk'
  have hk_lt : (k : ℚ) < 1 := by
    linarith [r1.2.2, r2.2.1, hkRat]
  have hk_gt : (-1 : ℚ) < k := by
    linarith [r1.2.1, r2.2.2, hkRat]
  have hk_lt_int : k < 1 := by exact_mod_cast hk_lt
  have hk_gt_int : -1 < k := by exact_mod_cast hk_gt
  have hk_zero : k = 0 := by omega
  have hrEq : (r1 : ℚ) = r2 := by
    have hzero : (r1 : ℚ) - r2 = 0 := by simpa [hk_zero] using hkRat
    linarith
  exact hne (Subtype.ext hrEq)

lemma pairwise_disjoint_shiftSet : Pairwise fun r1 r2 => Disjoint (shiftSet r1) (shiftSet r2) := by
  intro r1 r2 hne
  exact shiftSet_disjoint hne

structure VitaliAxioms (m : UnitPowerset → ENNReal) : Prop where
  finite : ∀ A : UnitPowerset, m A ≠ ⊤
  monotone :
    ∀ {A B : Set ℝ} (hA : A ⊆ ClosedUnitInterval) (hB : B ⊆ ClosedUnitInterval),
      A ⊆ B → m ⟨A, hA⟩ ≤ m ⟨B, hB⟩
  countablyAdditive :
    ∀ (f : ℕ → Set ℝ) (hf : ∀ n, f n ⊆ ClosedUnitInterval)
      (hUnion : (⋃ n, f n) ⊆ ClosedUnitInterval),
      Pairwise (fun i j : ℕ => Disjoint (f i) (f j)) →
        m ⟨⋃ i, f i, hUnion⟩ = ∑' i, m ⟨f i, hf i⟩
  translationInvariant :
    ∀ (A : Set ℝ) (hA : A ⊆ ClosedUnitInterval) (r : RatShift),
      m ⟨modShift A r, modShift_subset_closedUnitInterval A r⟩ = m ⟨A, hA⟩
  intervalLength :
    ∀ {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1), a < b →
      m ⟨Set.Icc a b, fun x hx => ⟨le_trans ha hx.1, le_trans hx.2 hb⟩⟩ =
        ENNReal.ofReal (b - a)

def natShift (n : ℕ) : RatShift :=
  ⟨1 / (n + 2 : ℚ), by positivity, by
    have hpos : (0 : ℚ) < n + 2 := by positivity
    have hn : (0 : ℚ) ≤ n := by exact_mod_cast Nat.zero_le n
    have hone : (1 : ℚ) < n + 2 := by linarith
    exact (div_lt_one hpos).2 hone⟩

lemma natShift_injective : Function.Injective natShift := by
  intro m n h
  have hval : (1 / (m + 2 : ℚ)) = 1 / (n + 2 : ℚ) := congrArg Subtype.val h
  have hden : (m + 2 : ℚ) = n + 2 := by
    apply inv_injective
    simpa [one_div] using hval
  norm_num at hden
  exact hden

def codedShiftSet (n : ℕ) : Set ℝ :=
  match Encodable.decode₂ RatShift n with
  | some r => shiftSet r
  | none => ∅

lemma pairwise_disjoint_codedShiftSet :
    Pairwise (fun n m : ℕ => Disjoint (codedShiftSet n) (codedShiftSet m)) := by
  intro n m hnm
  dsimp [codedShiftSet]
  cases h1 : Encodable.decode₂ RatShift n with
  | none =>
      simp [codedShiftSet, h1]
  | some r1 =>
      cases h2 : Encodable.decode₂ RatShift m with
      | none =>
          simp [codedShiftSet, h2]
      | some r2 =>
          have hr1 : Encodable.encode r1 = n := (Encodable.decode₂_eq_some).1 h1
          have hr2 : Encodable.encode r2 = m := (Encodable.decode₂_eq_some).1 h2
          have hrne : r1 ≠ r2 := by
            intro hre
            apply hnm
            rw [← hr1, ← hr2, hre]
          simpa [codedShiftSet, h1, h2] using shiftSet_disjoint hrne

lemma iUnion_codedShiftSet : (⋃ n : ℕ, codedShiftSet n) = Set.Ico (0 : ℝ) 1 := by
  ext x
  constructor
  · intro hx
    rcases mem_iUnion.mp hx with ⟨n, hx⟩
    dsimp [codedShiftSet] at hx
    cases hdec : Encodable.decode₂ RatShift n with
    | none =>
        simpa [codedShiftSet, hdec] using hx
    | some r =>
        have hx' : x ∈ shiftSet r := by simpa [codedShiftSet, hdec] using hx
        exact shiftSet_subset_unitInterval r hx'
  · intro hx
    let ux : UnitInterval := ⟨x, hx⟩
    rcases shift_exists_of_mem_unitInterval ux with ⟨r, hr⟩
    refine mem_iUnion.mpr ?_
    refine ⟨Encodable.encode r, ?_⟩
    simpa [codedShiftSet, hr]

def natShiftSet (n : ℕ) : Set ℝ :=
  shiftSet (natShift n)

lemma pairwise_disjoint_natShiftSet :
    Pairwise (fun n m : ℕ => Disjoint (natShiftSet n) (natShiftSet m)) := by
  intro n m hnm
  apply shiftSet_disjoint
  intro hEq
  exact hnm (natShift_injective hEq)

theorem thm_2_9_ennreal :
    ¬ ∃ m : UnitPowerset → ENNReal, VitaliAxioms m := by
  intro h
  rcases h with ⟨m, hm⟩
  rcases hm with ⟨_hfinite, hmono, hadd, htrans, hlen⟩
  let μ := fun (A : Set ℝ) (hA : A ⊆ ClosedUnitInterval) => m ⟨A, hA⟩
  have hIco : Set.Ico (0 : ℝ) 1 ⊆ ClosedUnitInterval :=
    unitInterval_subset_closedUnitInterval
  have hIcc01 : Set.Icc (0 : ℝ) 1 ⊆ ClosedUnitInterval := fun _ hx => hx
  have hvitali : vitaliSet ⊆ ClosedUnitInterval :=
    vitaliSet_subset_closedUnitInterval
  have hcodedSubset : ∀ n : ℕ, codedShiftSet n ⊆ ClosedUnitInterval := by
    intro n
    dsimp [codedShiftSet]
    cases hdec : Encodable.decode₂ RatShift n with
    | none =>
        intro x hx
        simp [codedShiftSet, hdec] at hx
    | some r =>
        simpa [codedShiftSet, hdec] using shiftSet_subset_closedUnitInterval r
  have hsum :
      μ (Set.Ico (0 : ℝ) 1) hIco =
        ∑' n : ℕ, μ (codedShiftSet n) (hcodedSubset n) := by
    have hUnion : (⋃ n : ℕ, codedShiftSet n) ⊆ ClosedUnitInterval := by
      rw [iUnion_codedShiftSet]
      exact hIco
    have hraw := hadd codedShiftSet hcodedSubset hUnion pairwise_disjoint_codedShiftSet
    have hUnit :
        (⟨⋃ n : ℕ, codedShiftSet n, hUnion⟩ : UnitPowerset) =
          ⟨Set.Ico (0 : ℝ) 1, hIco⟩ := by
      apply Subtype.ext
      exact iUnion_codedShiftSet
    simpa [μ, hUnit] using hraw
  have hconst : ∀ r : RatShift, μ (shiftSet r) (shiftSet_subset_closedUnitInterval r) =
      μ vitaliSet hvitali := by
    intro r
    simpa [μ, shiftSet] using htrans vitaliSet hvitali r
  have hnatSubset : ∀ n : ℕ, natShiftSet n ⊆ ClosedUnitInterval := by
    intro n
    exact shiftSet_subset_closedUnitInterval (natShift n)
  have hnatConst :
      ∀ n : ℕ, μ (natShiftSet n) (hnatSubset n) = μ vitaliSet hvitali := by
    intro n
    simpa [natShiftSet] using hconst (natShift n)
  have hupper : μ (Set.Ico (0 : ℝ) 1) hIco ≤ 1 := by
    calc
      μ (Set.Ico (0 : ℝ) 1) hIco ≤ μ (Set.Icc (0 : ℝ) 1) hIcc01 :=
        hmono hIco hIcc01 Ico_subset_Icc_self
      _ = 1 := by
        simpa [μ] using
          hlen (show (0 : ℝ) ≤ 0 by norm_num) (show (1 : ℝ) ≤ 1 by norm_num)
            (show (0 : ℝ) < 1 by norm_num)
  have hEmpty : (∅ : Set ℝ) ⊆ ClosedUnitInterval := by
    intro x hx
    cases hx
  have hempty : μ ∅ hEmpty = 0 := by
    have hemptySum : μ ∅ hEmpty = ∑' n : ℕ, μ ∅ hEmpty := by
      have hraw := hadd (fun _ : ℕ => (∅ : Set ℝ)) (fun _ => hEmpty) (by
        intro x hx
        rcases mem_iUnion.mp hx with ⟨n, hn⟩
        cases hn) (by
        intro i j hij
        simp)
      simpa [μ] using hraw
    by_cases hz : μ ∅ hEmpty = 0
    · exact hz
    · have htop : (∑' n : ℕ, μ ∅ hEmpty) = (⊤ : ENNReal) :=
        ENNReal.tsum_const_eq_top_of_ne_zero hz
      have htopEmpty : μ ∅ hEmpty = (⊤ : ENNReal) := by rw [hemptySum, htop]
      have hempty_le : μ ∅ hEmpty ≤ 1 := by
        calc
          μ ∅ hEmpty ≤ μ (Set.Ico (0 : ℝ) 1) hIco :=
            hmono hEmpty hIco (by intro x hx; cases hx)
          _ ≤ 1 := hupper
      have : (⊤ : ENNReal) ≤ 1 := by simpa [htopEmpty] using hempty_le
      exact (not_le_of_gt (show (1 : ENNReal) < ⊤ by simp) this).elim
  have hlower : ENNReal.ofReal (1 / 2 : ℝ) ≤ μ (Set.Ico (0 : ℝ) 1) hIco := by
    have hsub : Set.Icc (0 : ℝ) (1 / 2 : ℝ) ⊆ Set.Ico (0 : ℝ) 1 := by
      intro x hx
      rcases hx with ⟨hx0, hxhalf⟩
      constructor
      · exact hx0
      · linarith
    have hhalfClosed : Set.Icc (0 : ℝ) (1 / 2 : ℝ) ⊆ ClosedUnitInterval := by
      intro x hx
      exact hIco (hsub hx)
    calc
      ENNReal.ofReal (1 / 2 : ℝ) =
          μ (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) hhalfClosed := by
        symm
        simpa [μ] using
          hlen (show (0 : ℝ) ≤ 0 by norm_num) (show ((1 / 2 : ℝ)) ≤ 1 by norm_num)
            (show (0 : ℝ) < (1 / 2 : ℝ) by norm_num)
      _ ≤ μ (Set.Ico (0 : ℝ) 1) hIco := hmono hhalfClosed hIco hsub
  have hnatUnionSubsetIco : (⋃ n : ℕ, natShiftSet n) ⊆ Set.Ico (0 : ℝ) 1 := by
    intro x hx
    rcases mem_iUnion.mp hx with ⟨n, hx⟩
    exact shiftSet_subset_unitInterval (natShift n) hx
  have hnatUnionSubset : (⋃ n : ℕ, natShiftSet n) ⊆ ClosedUnitInterval := by
    intro x hx
    exact hIco (hnatUnionSubsetIco hx)
  have hnatSum :
      μ (⋃ n : ℕ, natShiftSet n) hnatUnionSubset =
        ∑' n : ℕ, μ (natShiftSet n) (hnatSubset n) := by
    have hraw := hadd natShiftSet hnatSubset hnatUnionSubset pairwise_disjoint_natShiftSet
    simpa [μ] using hraw
  have hnatUpper : ∑' n : ℕ, μ (natShiftSet n) (hnatSubset n) ≤ 1 := by
    calc
      ∑' n : ℕ, μ (natShiftSet n) (hnatSubset n) =
          μ (⋃ n : ℕ, natShiftSet n) hnatUnionSubset := by
        symm
        exact hnatSum
      _ ≤ μ (Set.Ico (0 : ℝ) 1) hIco := hmono hnatUnionSubset hIco hnatUnionSubsetIco
      _ ≤ 1 := hupper
  by_cases hzero : μ vitaliSet hvitali = 0
  · have hcodedZero : ∀ n : ℕ, μ (codedShiftSet n) (hcodedSubset n) = 0 := by
      intro n
      cases hdec : Encodable.decode₂ RatShift n with
      | none =>
          have hset : codedShiftSet n = (∅ : Set ℝ) := by
            simp [codedShiftSet, hdec]
          have hunit :
              (⟨codedShiftSet n, hcodedSubset n⟩ : UnitPowerset) = ⟨∅, hEmpty⟩ := by
            apply Subtype.ext
            exact hset
          simpa [μ, hunit] using hempty
      | some r =>
          have hset : codedShiftSet n = shiftSet r := by
            simp [codedShiftSet, hdec]
          have hunit :
              (⟨codedShiftSet n, hcodedSubset n⟩ : UnitPowerset) =
                ⟨shiftSet r, shiftSet_subset_closedUnitInterval r⟩ := by
            apply Subtype.ext
            exact hset
          have hshift : μ (shiftSet r) (shiftSet_subset_closedUnitInterval r) = 0 := by
            simpa [hzero] using hconst r
          simpa [μ, hunit] using hshift
    have hvanish : μ (Set.Ico (0 : ℝ) 1) hIco = 0 := by
      rw [hsum]
      simp [hcodedZero]
    have hhalf_pos : (0 : ENNReal) < ENNReal.ofReal (1 / 2 : ℝ) := by norm_num
    exact (not_lt_of_ge (hvanish ▸ hlower)) hhalf_pos
  · have htop : (∑' n : ℕ, μ (natShiftSet n) (hnatSubset n)) = (⊤ : ENNReal) := by
      calc
        (∑' n : ℕ, μ (natShiftSet n) (hnatSubset n)) =
            ∑' _ : ℕ, μ vitaliSet hvitali := by
          simp [hnatConst]
        _ = (⊤ : ENNReal) := ENNReal.tsum_const_eq_top_of_ne_zero hzero
    have hle : (⊤ : ENNReal) ≤ 1 := by simpa [htop] using hnatUpper
    exact not_le_of_gt (show (1 : ENNReal) < ⊤ by simp) hle



structure VitaliAxiomsNNReal (m : UnitPowerset → NNReal) : Prop where
  monotone :
    ∀ {A B : Set ℝ} (hA : A ⊆ ClosedUnitInterval) (hB : B ⊆ ClosedUnitInterval),
      A ⊆ B → m ⟨A, hA⟩ ≤ m ⟨B, hB⟩
  countablyAdditive :
    ∀ (f : ℕ → Set ℝ) (hf : ∀ n, f n ⊆ ClosedUnitInterval)
      (hUnion : (⋃ n, f n) ⊆ ClosedUnitInterval),
      Pairwise (fun i j : ℕ => Disjoint (f i) (f j)) →
        (m ⟨⋃ i, f i, hUnion⟩ : ENNReal) =
          ∑' i, (m ⟨f i, hf i⟩ : ENNReal)
  translationInvariant :
    ∀ (A : Set ℝ) (hA : A ⊆ ClosedUnitInterval) (r : RatShift),
      m ⟨modShift A r, modShift_subset_closedUnitInterval A r⟩ = m ⟨A, hA⟩
  intervalLength :
    ∀ {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1), a < b →
      m ⟨Set.Icc a b, fun x hx => ⟨le_trans ha hx.1, le_trans hx.2 hb⟩⟩ =
        Real.toNNReal (b - a)

theorem VitaliAxiomsNNReal.toVitaliAxioms {m : UnitPowerset → NNReal}
    (hm : VitaliAxiomsNNReal m) : VitaliAxioms (fun A => (m A : ENNReal)) where
  finite := by
    intro A
    exact ENNReal.coe_ne_top
  monotone := by
    intro A B hA hB hAB
    exact_mod_cast hm.monotone hA hB hAB
  countablyAdditive := by
    intro f hf hUnion hdisj
    exact hm.countablyAdditive f hf hUnion hdisj
  translationInvariant := by
    intro A hA r
    exact_mod_cast hm.translationInvariant A hA r
  intervalLength := by
    intro a b ha hb hab
    have hnn := hm.intervalLength ha hb hab
    change (m ⟨Set.Icc a b, fun x hx => ⟨le_trans ha hx.1, le_trans hx.2 hb⟩⟩ :
        ENNReal) = ENNReal.ofReal (b - a)
    rw [hnn]
    simp [ENNReal.ofReal]

theorem thm_2_9 :
    ¬ ∃ m : UnitPowerset → NNReal, VitaliAxiomsNNReal m := by
  rintro ⟨m, hm⟩
  exact thm_2_9_ennreal
    ⟨fun A : UnitPowerset => (m A : ENNReal), VitaliAxiomsNNReal.toVitaliAxioms hm⟩

end MATVitaliSupport
