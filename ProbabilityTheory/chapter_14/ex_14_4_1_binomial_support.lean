/-
TASK ID: ex_14_4_1_legacy_l3_derive_binomial_finite_sum_law_source_proof_spine_finite_sum_atom_partition_by_success_patterns
TYPE: Phase2ObligationTask
SOURCE PLAN: chapter14-central-limit-theorems
TASK ID: ex_14_4_1_legacy_l4_derive_binomial_finite_sum_law_source_proof_spine_iid_bernoulli_pattern_weight_iid_bernoulli_pattern_weight
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_14.ex_14_4_1_source_support

 




open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section



theorem ex_14_4_1_legacy_apply_lindeberg_levy_clt
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω)
    (hBridge : ex_14_4_1_resolvedSourceBridges S) :
    ex_14_4_1_sourceConclusion S :=
  ex_14_4_1_normalApproximation_of_resolvedSourceBridges S hBridge






open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

 
theorem ex_14_4_1_legacy_l2_apply_lindeberg_levy_clt_source_proof_spine
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω)
    (hBridge : ex_14_4_1_resolvedSourceBridges S) :
    ex_14_4_1_sourceConclusion S :=
  ex_14_4_1_legacy_apply_lindeberg_levy_clt S hBridge









-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section



def ex_14_4_1_legacy_finitePrefixSum
    {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ i : Fin (n + 1), X i.val ω



def ex_14_4_1_legacy_successPatternEvent
    {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ)
    (a : Finset (Fin (n + 1))) : Set Ω :=
  {ω |
    (∀ i : Fin (n + 1), i ∈ a → X i.val ω = 1) ∧
      (∀ i : Fin (n + 1), i ∉ a → X i.val ω = 0)}



theorem ex_14_4_1_legacy_partialSum_eq_card_of_successPatternEvent
    {Ω : Type*} (X : ℕ → Ω → ℝ) {n : ℕ}
    {a : Finset (Fin (n + 1))} {ω : Ω}
    (hω : ω ∈ ex_14_4_1_legacy_successPatternEvent X n a) :
    ex_14_4_1_legacy_finitePrefixSum X n ω = (a.card : ℝ) := by
  classical
  rw [ex_14_4_1_legacy_finitePrefixSum]
  calc
    (∑ i : Fin (n + 1), X i.val ω)
        = ∑ i : Fin (n + 1), if i ∈ a then (1 : ℝ) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          by_cases hia : i ∈ a
          · simp [hia, hω.1 i hia]
          · simp [hia, hω.2 i hia]
    _ = (a.card : ℝ) := by
          simp



theorem ex_14_4_1_legacy_successPatternEvent_eq_of_mem
    {Ω : Type*} (X : ℕ → Ω → ℝ) {n : ℕ}
    {a b : Finset (Fin (n + 1))} {ω : Ω}
    (ha : ω ∈ ex_14_4_1_legacy_successPatternEvent X n a)
    (hb : ω ∈ ex_14_4_1_legacy_successPatternEvent X n b) :
    a = b := by
  classical
  ext i
  constructor
  · intro hia
    by_contra hib
    have hOne : X i.val ω = 1 := ha.1 i hia
    have hZero : X i.val ω = 0 := hb.2 i hib
    have : (1 : ℝ) = 0 := by
      rw [← hOne, hZero]
    norm_num at this
  · intro hib
    by_contra hia
    have hOne : X i.val ω = 1 := hb.1 i hib
    have hZero : X i.val ω = 0 := ha.2 i hia
    have : (1 : ℝ) = 0 := by
      rw [← hOne, hZero]
    norm_num at this



theorem ex_14_4_1_legacy_finite_sum_atom_partition_by_success_patterns
    {Ω : Type*} (X : ℕ → Ω → ℝ) (n k : ℕ) (ω : Ω) :
    (ex_14_4_1_legacy_finitePrefixSum X n ω = (k : ℝ) ∧
        ∀ i : Fin (n + 1), X i.val ω = 0 ∨ X i.val ω = 1) ↔
      ∃ a ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard k,
        ω ∈ ex_14_4_1_legacy_successPatternEvent X n a := by
  classical
  constructor
  · rintro ⟨hsum, hsupport⟩
    let a : Finset (Fin (n + 1)) :=
      (Finset.univ : Finset (Fin (n + 1))).filter
        (fun i => X i.val ω = 1)
    have haEvent : ω ∈ ex_14_4_1_legacy_successPatternEvent X n a := by
      constructor
      · intro i hi
        simpa [a] using (Finset.mem_filter.mp hi).2
      · intro i hi
        rcases hsupport i with hZero | hOne
        · exact hZero
        · exfalso
          exact hi (by simp [a, hOne])
    have hsumCard :
        ex_14_4_1_legacy_finitePrefixSum X n ω = (a.card : ℝ) :=
      ex_14_4_1_legacy_partialSum_eq_card_of_successPatternEvent X haEvent
    have hcardReal : (a.card : ℝ) = (k : ℝ) :=
      hsumCard.symm.trans hsum
    have hcard : a.card = k := by
      exact_mod_cast hcardReal
    refine ⟨a, ?_, haEvent⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ a, hcard⟩
  · rintro ⟨a, ha, hω⟩
    have hsumCard :
        ex_14_4_1_legacy_finitePrefixSum X n ω = (a.card : ℝ) :=
      ex_14_4_1_legacy_partialSum_eq_card_of_successPatternEvent X hω
    have hcard : a.card = k := (Finset.mem_powersetCard.mp ha).2
    constructor
    · rw [hsumCard, hcard]
    · intro i
      by_cases hia : i ∈ a
      · exact Or.inr (hω.1 i hia)
      · exact Or.inl (hω.2 i hia)



def ex_14_4_1_legacy_localBinomialPMF (p : ℝ) (n k : ℕ) : ℝ :=
  if k ≤ n then (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) else 0



theorem ex_14_4_1_legacy_pattern_weight_sum_eq_binomialPMF
    (p : ℝ) (n k : ℕ) :
    (∑ a ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard k,
        p ^ a.card * (1 - p) ^ ((n + 1) - a.card)) =
      ex_14_4_1_legacy_localBinomialPMF p (n + 1) k := by
  classical
  calc
    (∑ a ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard k,
        p ^ a.card * (1 - p) ^ ((n + 1) - a.card))
        = ∑ _a ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard k,
            p ^ k * (1 - p) ^ ((n + 1) - k) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          have hcard : a.card = k := (Finset.mem_powersetCard.mp ha).2
          simp [hcard]
    _ = ((Finset.univ : Finset (Fin (n + 1))).powersetCard k).card *
          (p ^ k * (1 - p) ^ ((n + 1) - k)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = ex_14_4_1_legacy_localBinomialPMF p (n + 1) k := by
          by_cases hk : k ≤ n + 1
          · simp [ex_14_4_1_legacy_localBinomialPMF, hk, Finset.card_powersetCard,
              Fintype.card_fin, mul_assoc]
          · have hlt : n + 1 < k := Nat.lt_of_not_ge hk
            simp [ex_14_4_1_legacy_localBinomialPMF, hk, Finset.card_powersetCard,
              Fintype.card_fin, Nat.choose_eq_zero_of_lt hlt]



theorem ex_14_4_1_legacy_successPatternEvent_factorization_from_iIndepFun
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (X : ℕ → Ω → ℝ)
    (n : ℕ) (a : Finset (Fin (n + 1)))
    (hIndep : ProbabilityTheory.iIndepFun X P) :
    P (ex_14_4_1_legacy_successPatternEvent X n a) =
      ∏ i : Fin (n + 1),
        P (if i ∈ a then {ω | X i.val ω = 1} else {ω | X i.val ω = 0}) := by
  classical
  let sets : (i : Fin (n + 1)) → Set ℝ :=
    fun i => if i ∈ a then ({1} : Set ℝ) else ({0} : Set ℝ)
  have hPrefix :
      ProbabilityTheory.iIndepFun (fun i : Fin (n + 1) => X i.val) P := by
    exact ProbabilityTheory.iIndepFun.precomp (fun _ _ h => Fin.ext h) hIndep
  have hFactor :=
    hPrefix.measure_inter_preimage_eq_mul (Finset.univ : Finset (Fin (n + 1)))
      (sets := sets) (by
        intro i hi
        by_cases hia : i ∈ a <;> simp [sets, hia])
  have hEvent :
      ex_14_4_1_legacy_successPatternEvent X n a =
        ⋂ i ∈ (Finset.univ : Finset (Fin (n + 1))),
          (fun ω => X i.val ω) ⁻¹' sets i := by
    ext ω
    simp [ex_14_4_1_legacy_successPatternEvent, sets]
    constructor
    · intro h i
      by_cases hia : i ∈ a
      · simp [hia, h.1 i hia]
      · simp [hia, h.2 i hia]
    · intro h
      constructor
      · intro i hia
        have hi := h i
        simpa [hia] using hi
      · intro i hia
        have hi := h i
        simpa [hia] using hi
  rw [hEvent, hFactor]
  refine Finset.prod_congr rfl ?_
  intro i hi
  by_cases hia : i ∈ a
  · simp [sets, hia]
    apply congrArg P
    ext ω
    simp
  · simp [sets, hia]
    apply congrArg P
    ext ω
    simp



lemma ex_14_4_1_legacy_prod_const_by_pattern_card_owner
    {m : ℕ} (a : Finset (Fin m)) (x y : ℝ) :
    (∏ i : Fin m, if i ∈ a then x else y) =
      x ^ a.card * y ^ (m - a.card) := by
  classical
  let s : Finset (Fin m) := Finset.univ
  have hfilter : s.filter (fun i : Fin m => i ∈ a) = a := by
    ext i
    simp [s]
  have hfilterCard :
      (s.filter (fun i : Fin m => i ∈ a)).card = a.card := by
    rw [hfilter]
  have hnotFilterCard :
      (s.filter (fun i : Fin m => ¬ i ∈ a)).card = m - a.card := by
    have hsum :=
      Finset.card_filter_add_card_filter_not
        (s := s) (p := fun i : Fin m => i ∈ a)
    have hsCard : s.card = m := by
      simp [s]
    omega
  calc
    (∏ i : Fin m, if i ∈ a then x else y)
        =
          (s.filter (fun i : Fin m => i ∈ a)).prod
              (fun i => if i ∈ a then x else y) *
            (s.filter (fun i : Fin m => ¬ i ∈ a)).prod
              (fun i => if i ∈ a then x else y) := by
          simpa [s] using
            (Finset.prod_filter_mul_prod_filter_not
              (s := s) (p := fun i : Fin m => i ∈ a)
              (f := fun i : Fin m => if i ∈ a then x else y)).symm
    _ =
          x ^ (s.filter (fun i : Fin m => i ∈ a)).card *
            y ^ (s.filter (fun i : Fin m => ¬ i ∈ a)).card := by
          have hyes :
              (s.filter (fun i : Fin m => i ∈ a)).prod
                  (fun i => if i ∈ a then x else y) =
                (s.filter (fun i : Fin m => i ∈ a)).prod (fun _ => x) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            have hia : i ∈ a := (Finset.mem_filter.mp hi).2
            simp [hia]
          have hno :
              (s.filter (fun i : Fin m => ¬ i ∈ a)).prod
                  (fun i => if i ∈ a then x else y) =
                (s.filter (fun i : Fin m => ¬ i ∈ a)).prod (fun _ => y) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            have hia : i ∉ a := (Finset.mem_filter.mp hi).2
            simp [hia]
          rw [hyes, hno]
          simp
    _ = x ^ a.card * y ^ (m - a.card) := by
          rw [hfilterCard, hnotFilterCard]



theorem ex_14_4_1_legacy_source_successPattern_weight
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω)
    (hSource : ex_14_4_1_bernoulliSourceLaw S)
    (n : ℕ) (a : Finset (Fin (n + 1))) :
    (S.P (ex_14_4_1_legacy_successPatternEvent S.X n a)).toReal =
      S.p ^ a.card * (1 - S.p) ^ ((n + 1) - a.card) := by
  classical
  have hFactorMeasure :
      S.P (ex_14_4_1_legacy_successPatternEvent S.X n a) =
        ∏ i : Fin (n + 1),
          S.P (if i ∈ a then {ω | S.X i.val ω = 1} else {ω | S.X i.val ω = 0}) :=
    ex_14_4_1_legacy_successPatternEvent_factorization_from_iIndepFun
      S.P S.X n a S.hIndep
  have hFactorSuccess :
      (S.P (ex_14_4_1_legacy_successPatternEvent S.X n a)).toReal =
        ∏ i : Fin (n + 1),
          (S.P (if i ∈ a then {ω | S.X i.val ω = 1} else {ω | S.X i.val ω = 0})).toReal := by
    rw [hFactorMeasure]
    simp
  have hOne : ∀ i : Fin (n + 1), (S.P {ω | S.X i.val ω = 1}).toReal = S.p := by
    intro i
    exact (hSource i.val).1
  have hZero : ∀ i : Fin (n + 1), (S.P {ω | S.X i.val ω = 0}).toReal = 1 - S.p := by
    intro i
    exact (hSource i.val).2.1
  rw [hFactorSuccess]
  calc
    (∏ i : Fin (n + 1),
        (S.P (if i ∈ a then {ω | S.X i.val ω = 1} else {ω | S.X i.val ω = 0})).toReal)
        = ∏ i : Fin (n + 1), if i ∈ a then S.p else 1 - S.p := by
          refine Finset.prod_congr rfl ?_
          intro i _hi
          by_cases hia : i ∈ a
          · simp [hia, hOne i]
          · simp [hia, hZero i]
    _ = S.p ^ a.card * (1 - S.p) ^ ((n + 1) - a.card) := by
          simpa using
            (ex_14_4_1_legacy_prod_const_by_pattern_card_owner
              (m := n + 1) a S.p (1 - S.p))



theorem ex_14_4_1_legacy_prefix_support_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω)
    (hSource : ex_14_4_1_bernoulliSourceLaw S)
    (n : ℕ) :
    ∀ᵐ ω ∂S.P, ∀ i : Fin (n + 1), S.X i.val ω = 0 ∨ S.X i.val ω = 1 := by
  have h :
      ∀ᵐ ω ∂S.P, ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))),
        S.X i.val ω = 0 ∨ S.X i.val ω = 1 := by
    rw [Filter.eventually_all_finset]
    intro i _hi
    have hNull : S.P {ω | S.X i.val ω ≠ 0 ∧ S.X i.val ω ≠ 1} = 0 :=
      (hSource i.val).2.2
    rw [ae_iff]
    simpa [not_or] using hNull
  filter_upwards [h] with ω hω i
  exact hω i (by simp)



theorem ex_14_4_1_legacy_successPatternEvent_nullMeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω)
    (n : ℕ) (a : Finset (Fin (n + 1))) :
    NullMeasurableSet (ex_14_4_1_legacy_successPatternEvent S.X n a) S.P := by
  classical
  have hEq :
      ex_14_4_1_legacy_successPatternEvent S.X n a =
        ⋂ i : Fin (n + 1),
          if i ∈ a then {ω | S.X i.val ω = 1} else {ω | S.X i.val ω = 0} := by
    ext ω
    simp [ex_14_4_1_legacy_successPatternEvent]
    constructor
    · intro h i
      by_cases hia : i ∈ a
      · simp [hia, h.1 i hia]
      · simp [hia, h.2 i hia]
    · intro h
      constructor
      · intro i hia
        have hi := h i
        simpa [hia] using hi
      · intro i hia
        have hi := h i
        simpa [hia] using hi
  rw [hEq]
  refine NullMeasurableSet.iInter ?_
  intro i
  by_cases hia : i ∈ a
  · simp [hia]
    simpa [Set.preimage, Set.mem_singleton_iff] using
      (S.hX i.val).nullMeasurableSet_preimage (measurableSet_singleton (1 : ℝ))
  · simp [hia]
    simpa [Set.preimage, Set.mem_singleton_iff] using
      (S.hX i.val).nullMeasurableSet_preimage (measurableSet_singleton (0 : ℝ))

theorem ex_14_4_1_legacy_partialSum_eq_finitePrefixSum
    {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) :
    ex_14_4_1_partialSum X n = ex_14_4_1_legacy_finitePrefixSum X n := by
  rfl



theorem ex_14_4_1_legacy_atom_event_ae_eq_pattern_union
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω)
    (hSource : ex_14_4_1_bernoulliSourceLaw S)
    (n k : ℕ) :
    {ω | ex_14_4_1_partialSum S.X n ω = (k : ℝ)} =ᵐ[S.P]
      ⋃ a ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard k,
        ex_14_4_1_legacy_successPatternEvent S.X n a := by
  filter_upwards [ex_14_4_1_legacy_prefix_support_ae S hSource n] with ω hSupport
  apply propext
  change (ex_14_4_1_partialSum S.X n ω = (k : ℝ)) ↔
    ω ∈ ⋃ a ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard k,
      ex_14_4_1_legacy_successPatternEvent S.X n a
  constructor
  · intro hsum
    have hsumLocal :
        ex_14_4_1_legacy_finitePrefixSum S.X n ω = (k : ℝ) := by
      simpa [ex_14_4_1_legacy_partialSum_eq_finitePrefixSum] using hsum
    have hPart :=
      (ex_14_4_1_legacy_finite_sum_atom_partition_by_success_patterns
        S.X n k ω).1 ⟨hsumLocal, hSupport⟩
    rcases hPart with ⟨a, ha, hωa⟩
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨ha, hωa⟩⟩
  · intro hUnion
    rcases Set.mem_iUnion.mp hUnion with ⟨a, hUnionA⟩
    rcases Set.mem_iUnion.mp hUnionA with ⟨ha, hωa⟩
    have hPart :=
      (ex_14_4_1_legacy_finite_sum_atom_partition_by_success_patterns
        S.X n k ω).2 ⟨a, ha, hωa⟩
    have hsumLocal : ex_14_4_1_legacy_finitePrefixSum S.X n ω = (k : ℝ) := hPart.1
    simpa [ex_14_4_1_legacy_partialSum_eq_finitePrefixSum] using hsumLocal

 
theorem ex_14_4_1_legacy_atom_measure_eq_pattern_sum
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω)
    (hSource : ex_14_4_1_bernoulliSourceLaw S)
    (n k : ℕ) :
    S.P {ω | ex_14_4_1_partialSum S.X n ω = (k : ℝ)} =
      ∑ a ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard k,
        S.P (ex_14_4_1_legacy_successPatternEvent S.X n a) := by
  classical
  let patterns : Finset (Finset (Fin (n + 1))) :=
    (Finset.univ : Finset (Fin (n + 1))).powersetCard k
  have hAe := ex_14_4_1_legacy_atom_event_ae_eq_pattern_union S hSource n k
  have hDisj :
      Set.PairwiseDisjoint (↑patterns)
        (fun a => ex_14_4_1_legacy_successPatternEvent S.X n a) := by
    intro a _ha b _hb hne
    change Disjoint
      (ex_14_4_1_legacy_successPatternEvent S.X n a)
      (ex_14_4_1_legacy_successPatternEvent S.X n b)
    rw [Set.disjoint_left]
    intro ω hωa hωb
    exact hne (ex_14_4_1_legacy_successPatternEvent_eq_of_mem S.X hωa hωb)
  have hNull :
      ∀ a ∈ patterns,
        NullMeasurableSet (ex_14_4_1_legacy_successPatternEvent S.X n a) S.P := by
    intro a _ha
    exact ex_14_4_1_legacy_successPatternEvent_nullMeasurable S n a
  calc
    S.P {ω | ex_14_4_1_partialSum S.X n ω = (k : ℝ)}
        = S.P (⋃ a ∈ patterns, ex_14_4_1_legacy_successPatternEvent S.X n a) := by
          exact measure_congr hAe
    _ = ∑ a ∈ patterns, S.P (ex_14_4_1_legacy_successPatternEvent S.X n a) := by
          exact measure_biUnion_finset₀ hDisj.aedisjoint hNull



theorem ex_14_4_1_legacy_assemble_binomial_finite_sum_atom_formula
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω)
    (hSource : ex_14_4_1_bernoulliSourceLaw S) :
    ∀ n k : ℕ,
      (S.P {ω | ex_14_4_1_partialSum S.X n ω = (k : ℝ)}).toReal =
        ex_14_4_1_binomialPMF S.p (n + 1) k := by
  classical
  letI : IsProbabilityMeasure S.P := S.isProbabilityMeasure
  intro n k
  let patterns : Finset (Finset (Fin (n + 1))) :=
    (Finset.univ : Finset (Fin (n + 1))).powersetCard k
  have hMeasure := ex_14_4_1_legacy_atom_measure_eq_pattern_sum S hSource n k
  calc
    (S.P {ω | ex_14_4_1_partialSum S.X n ω = (k : ℝ)}).toReal
        = ∑ a ∈ patterns,
            (S.P (ex_14_4_1_legacy_successPatternEvent S.X n a)).toReal := by
          rw [hMeasure]
          rw [ENNReal.toReal_sum]
          intro a _ha
          finiteness
    _ = ∑ a ∈ patterns,
          S.p ^ a.card * (1 - S.p) ^ ((n + 1) - a.card) := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          exact ex_14_4_1_legacy_source_successPattern_weight S hSource n a
    _ = ex_14_4_1_legacy_localBinomialPMF S.p (n + 1) k :=
          ex_14_4_1_legacy_pattern_weight_sum_eq_binomialPMF S.p n k
    _ = ex_14_4_1_binomialPMF S.p (n + 1) k := by
          rfl

 
theorem ex_14_4_1_legacy_l3_derive_binomial_finite_sum_law_source_proof_spine_finite_sum_atom_partition_by_success_patterns
    {Ω : Type*} (X : ℕ → Ω → ℝ) (n k : ℕ) (ω : Ω) :
    (ex_14_4_1_legacy_finitePrefixSum X n ω = (k : ℝ) ∧
        ∀ i : Fin (n + 1), X i.val ω = 0 ∨ X i.val ω = 1) ↔
      ∃ a ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard k,
        ω ∈ ex_14_4_1_legacy_successPatternEvent X n a :=
  ex_14_4_1_legacy_finite_sum_atom_partition_by_success_patterns X n k ω

 
theorem ex_14_4_1_legacy_l2_derive_binomial_finite_sum_law_source_proof_spine
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω)
    (hSource : ex_14_4_1_bernoulliSourceLaw S) :
    ∀ n k : ℕ,
      (S.P {ω | ex_14_4_1_partialSum S.X n ω = (k : ℝ)}).toReal =
        ex_14_4_1_binomialPMF S.p (n + 1) k :=
  ex_14_4_1_legacy_assemble_binomial_finite_sum_atom_formula S hSource

 
theorem ex_14_4_1_legacy_derive_binomial_finite_sum_law
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω)
    (hSource : ex_14_4_1_bernoulliSourceLaw S) :
    ex_14_4_1_binomialFiniteSumBridge S :=
  ex_14_4_1_legacy_l2_derive_binomial_finite_sum_law_source_proof_spine S hSource






open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

 
theorem ex_14_4_1_legacy_l3_derive_binomial_finite_sum_law_source_proof_spine_assemble_binomial_finite_sum_atom_formula
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω)
    (hSource : ex_14_4_1_bernoulliSourceLaw S) :
    ∀ n k : ℕ,
      (S.P {ω | ex_14_4_1_partialSum S.X n ω = (k : ℝ)}).toReal =
        ex_14_4_1_binomialPMF S.p (n + 1) k :=
  ex_14_4_1_legacy_assemble_binomial_finite_sum_atom_formula S hSource









-- WRITE FINAL LEAN CODE BELOW

open scoped BigOperators

noncomputable section



def ex_14_4_1_legacy_iidBernoulliPatternEvent
    {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ)
    (a : Finset (Fin (n + 1))) : Set Ω :=
  {ω |
    (∀ i : Fin (n + 1), i ∈ a → X i.val ω = 1) ∧
      (∀ i : Fin (n + 1), i ∉ a → X i.val ω = 0)}



lemma ex_14_4_1_legacy_prod_const_by_pattern_card
    {m : ℕ} (a : Finset (Fin m)) (x y : ℝ) :
    (∏ i : Fin m, if i ∈ a then x else y) =
      x ^ a.card * y ^ (m - a.card) := by
  classical
  let s : Finset (Fin m) := Finset.univ
  have hfilter : s.filter (fun i : Fin m => i ∈ a) = a := by
    ext i
    simp [s]
  have hfilterCard :
      (s.filter (fun i : Fin m => i ∈ a)).card = a.card := by
    rw [hfilter]
  have hnotFilterCard :
      (s.filter (fun i : Fin m => ¬ i ∈ a)).card = m - a.card := by
    have hsum :=
      Finset.card_filter_add_card_filter_not
        (s := s) (p := fun i : Fin m => i ∈ a)
    have hsCard : s.card = m := by
      simp [s]
    omega
  calc
    (∏ i : Fin m, if i ∈ a then x else y)
        =
          (s.filter (fun i : Fin m => i ∈ a)).prod
              (fun i => if i ∈ a then x else y) *
            (s.filter (fun i : Fin m => ¬ i ∈ a)).prod
              (fun i => if i ∈ a then x else y) := by
          simpa [s] using
            (Finset.prod_filter_mul_prod_filter_not
              (s := s) (p := fun i : Fin m => i ∈ a)
              (f := fun i : Fin m => if i ∈ a then x else y)).symm
    _ =
          x ^ (s.filter (fun i : Fin m => i ∈ a)).card *
            y ^ (s.filter (fun i : Fin m => ¬ i ∈ a)).card := by
          have hyes :
              (s.filter (fun i : Fin m => i ∈ a)).prod
                  (fun i => if i ∈ a then x else y) =
                (s.filter (fun i : Fin m => i ∈ a)).prod (fun _ => x) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            have hia : i ∈ a := (Finset.mem_filter.mp hi).2
            simp [hia]
          have hno :
              (s.filter (fun i : Fin m => ¬ i ∈ a)).prod
                  (fun i => if i ∈ a then x else y) =
                (s.filter (fun i : Fin m => ¬ i ∈ a)).prod (fun _ => y) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            have hia : i ∉ a := (Finset.mem_filter.mp hi).2
            simp [hia]
          rw [hyes, hno]
          simp
    _ = x ^ a.card * y ^ (m - a.card) := by
          rw [hfilterCard, hnotFilterCard]



theorem ex_14_4_1_legacy_iid_bernoulli_pattern_weight
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (X : ℕ → Ω → ℝ) (n : ℕ) (a : Finset (Fin (n + 1))) (p : ℝ)
    (hFactor :
      (P (ex_14_4_1_legacy_iidBernoulliPatternEvent X n a)).toReal =
        ∏ i : Fin (n + 1),
          (P (if i ∈ a then {ω | X i.val ω = 1} else {ω | X i.val ω = 0})).toReal)
    (hOne : ∀ i : Fin (n + 1), (P {ω | X i.val ω = 1}).toReal = p)
    (hZero : ∀ i : Fin (n + 1), (P {ω | X i.val ω = 0}).toReal = 1 - p) :
    (P (ex_14_4_1_legacy_iidBernoulliPatternEvent X n a)).toReal =
      p ^ a.card * (1 - p) ^ ((n + 1) - a.card) := by
  classical
  rw [hFactor]
  calc
    (∏ i : Fin (n + 1),
        (P (if i ∈ a then {ω | X i.val ω = 1} else {ω | X i.val ω = 0})).toReal)
        = ∏ i : Fin (n + 1), if i ∈ a then p else 1 - p := by
          refine Finset.prod_congr rfl ?_
          intro i _hi
          by_cases hia : i ∈ a
          · simp [hia, hOne i]
          · simp [hia, hZero i]
    _ = p ^ a.card * (1 - p) ^ ((n + 1) - a.card) := by
          simpa using
            (ex_14_4_1_legacy_prod_const_by_pattern_card
              (m := n + 1) a p (1 - p))

 
theorem ex_14_4_1_legacy_l3_derive_binomial_finite_sum_law_source_proof_spine_iid_bernoulli_pattern_weight
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (X : ℕ → Ω → ℝ) (n : ℕ) (a : Finset (Fin (n + 1))) (p : ℝ)
    (hFactor :
      (P (ex_14_4_1_legacy_iidBernoulliPatternEvent X n a)).toReal =
        ∏ i : Fin (n + 1),
          (P (if i ∈ a then {ω | X i.val ω = 1} else {ω | X i.val ω = 0})).toReal)
    (hOne : ∀ i : Fin (n + 1), (P {ω | X i.val ω = 1}).toReal = p)
    (hZero : ∀ i : Fin (n + 1), (P {ω | X i.val ω = 0}).toReal = 1 - p) :
    (P (ex_14_4_1_legacy_iidBernoulliPatternEvent X n a)).toReal =
      p ^ a.card * (1 - p) ^ ((n + 1) - a.card) :=
  ex_14_4_1_legacy_iid_bernoulli_pattern_weight P X n a p hFactor hOne hZero



theorem ex_14_4_1_legacy_l4_derive_binomial_finite_sum_law_source_proof_spine_iid_bernoulli_pattern_weight_iid_bernoulli_pattern_weight
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (X : ℕ → Ω → ℝ) (n : ℕ) (a : Finset (Fin (n + 1))) (p : ℝ)
    (hFactor :
      (P (ex_14_4_1_legacy_iidBernoulliPatternEvent X n a)).toReal =
        ∏ i : Fin (n + 1),
          (P (if i ∈ a then {ω | X i.val ω = 1} else {ω | X i.val ω = 0})).toReal)
    (hOne : ∀ i : Fin (n + 1), (P {ω | X i.val ω = 1}).toReal = p)
    (hZero : ∀ i : Fin (n + 1), (P {ω | X i.val ω = 0}).toReal = 1 - p) :
    (P (ex_14_4_1_legacy_iidBernoulliPatternEvent X n a)).toReal =
      p ^ a.card * (1 - p) ^ ((n + 1) - a.card) :=
  ex_14_4_1_legacy_iid_bernoulli_pattern_weight P X n a p hFactor hOne hZero
