/-
TASK ID: thm_3_1
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_3_1
import ToyApollo.Output.def_3_2
import ToyApollo.Output.def_3_3

-- Public extension contracts use Definition 3.2's canonical `IsExtension` interface.

open Set MeasureTheory ENNReal

variable {X : Type*}

lemma FieldOfSets.inter_mem (F₀ : FieldOfSets X) {s t : Set X}
    (hs : s ∈ F₀.carrier) (ht : t ∈ F₀.carrier) : s ∩ t ∈ F₀.carrier := by
  convert F₀.compl_mem _ (F₀.union_mem _ _ (F₀.compl_mem _ hs) (F₀.compl_mem _ ht)) using 1; aesop

lemma FieldOfSets.diff_mem (F₀ : FieldOfSets X) {s t : Set X}
    (hs : s ∈ F₀.carrier) (ht : t ∈ F₀.carrier) : s \ t ∈ F₀.carrier := by
  have hset : s \ t = s ∩ tᶜ := by
    ext x
    simp
  rw [hset]
  exact FieldOfSets.inter_mem F₀ hs (F₀.compl_mem t ht)

lemma FieldOfSets.univ_mem (F₀ : FieldOfSets X) : univ ∈ F₀.carrier := by
  simpa using F₀.compl_mem _ F₀.empty_mem

lemma FieldOfSets.isPiSystem (F₀ : FieldOfSets X) : IsPiSystem F₀.carrier := by
  intro s hs t ht _; exact FieldOfSets.inter_mem F₀ hs ht

lemma FieldOfSets.biUnion_range_mem (F₀ : FieldOfSets X) {A : ℕ → Set X}
    (hA : ∀ i, A i ∈ F₀.carrier) (n : ℕ) :
    (⋃ i ∈ Finset.range n, A i) ∈ F₀.carrier := by
  induction' n with n ih;
  · simpa using F₀.empty_mem;
  · simp_all +decide [ Finset.range_add_one ];
    exact F₀.union_mem _ _ ( hA _ ) ih

lemma Premeasure.additive {F₀ : FieldOfSets X} (pm : Premeasure F₀)
    {s t : Set X} (hs : s ∈ F₀.carrier) (ht : t ∈ F₀.carrier)
    (hst : Disjoint s t) (hut : s ∪ t ∈ F₀.carrier) :
    pm.μ₀ ⟨s ∪ t, hut⟩ = pm.μ₀ ⟨s, hs⟩ + pm.μ₀ ⟨t, ht⟩ := by
  convert pm.sigma_additive ( fun i => if i = 0 then s else if i = 1 then t else ∅ ) ?_ ?_ ?_ using 1;
  convert rfl;
  any_goals intro i; rcases i with ( _ | _ | i ) <;> simp +decide [ * ];
  any_goals rw [ tsum_eq_sum ];
  any_goals exact Finset.range 2;
  any_goals exact F₀.empty_mem;
  any_goals intro j hj; rcases j with ( _ | _ | j ) <;> simp_all +decide [ Function.onFun ];
  · ext x; simp [Set.mem_iUnion];
    exact ⟨ fun ⟨ i, hi ⟩ => by rcases i with ( _ | _ | i ) <;> tauto, fun hx => hx.elim ( fun hx => ⟨ 0, hx ⟩ ) fun hx => ⟨ 1, hx ⟩ ⟩;
  · simp +decide [ Finset.sum_range_succ ];
  · exact pm.map_empty;
  · convert hut using 1;
    ext x ; simp +decide [ Set.ext_iff ];
    exact ⟨ fun ⟨ i, hi ⟩ => by rcases i with ( _ | _ | i ) <;> tauto, fun hx => hx.elim ( fun hx => ⟨ 0, hx ⟩ ) fun hx => ⟨ 1, hx ⟩ ⟩;
  · exact hst.symm

lemma Premeasure.mono {F₀ : FieldOfSets X} (pm : Premeasure F₀)
    {s t : Set X} (hs : s ∈ F₀.carrier) (ht : t ∈ F₀.carrier) (hst : s ⊆ t) :
    pm.μ₀ ⟨s, hs⟩ ≤ pm.μ₀ ⟨t, ht⟩ := by
  -- Since $s \subseteq t$, we have $t = s \cup (t \ s)$.
  have ht_eq : t = s ∪ (t \ s) := by
    rw [ Set.union_diff_cancel hst ];
  -- Since $s \cap (t \ s) = \emptyset$, we can apply the additivity property of the pre-measure.
  have h_add : pm.μ₀ ⟨s ∪ (t \ s), by
    grind +ring⟩ = pm.μ₀ ⟨s, hs⟩ + pm.μ₀ ⟨t \ s, by
    exact?⟩ := by
    apply Premeasure.additive;
    exact disjoint_sdiff_self_right
  generalize_proofs at *;
  calc
    pm.μ₀ ⟨s, hs⟩ ≤ pm.μ₀ ⟨s, hs⟩ + pm.μ₀ ⟨t \ s, by assumption⟩ := le_add_right le_rfl
    _ = pm.μ₀ ⟨s ∪ (t \ s), by assumption⟩ := h_add.symm
    _ = pm.μ₀ ⟨t, ht⟩ := congrArg pm.μ₀ (Subtype.ext ht_eq.symm)

noncomputable def Premeasure.outerMeasure {F₀ : FieldOfSets X} (pm : Premeasure F₀) :
    OuterMeasure X :=
  inducedOuterMeasure (fun s (hs : s ∈ F₀.carrier) => pm.μ₀ ⟨s, hs⟩) F₀.empty_mem pm.map_empty

lemma Premeasure.outerMeasure_le {F₀ : FieldOfSets X} (pm : Premeasure F₀)
    {s : Set X} (hs : s ∈ F₀.carrier) :
    pm.outerMeasure s ≤ pm.μ₀ ⟨s, hs⟩ := by
  apply iInf_le_of_le (fun i => if i = 0 then s else ∅) (by
  refine' le_trans ( ciInf_le _ _ ) _;
  · exact?;
  · exact fun x hx => Set.mem_iUnion.2 ⟨ 0, by simpa using hx ⟩;
  · rw [ tsum_eq_single 0 ] <;> simp +decide [ hs ];
    · refine' csInf_le _ _ <;> norm_num [ hs ];
    · simp +contextual [ pm.map_empty, extend ];
      exact fun _ _ => iInf_pos F₀.empty_mem)

lemma Premeasure.countably_subadditive {F₀ : FieldOfSets X} (pm : Premeasure F₀)
    {s : Set X} (hs : s ∈ F₀.carrier) {A : ℕ → Set X} (hA : ∀ i, A i ∈ F₀.carrier)
    (hcover : s ⊆ ⋃ i, A i) :
    pm.μ₀ ⟨s, hs⟩ ≤ ∑' i, pm.μ₀ ⟨A i, hA i⟩ := by
  -- Define B_i = A_i \ (⋃ j < i, A_j) for each i.
  set B : ℕ → Set X := fun i => (A i) \ (⋃ j < i, A j);
  -- By definition of $B$, we know that $s \subseteq \bigcup_{i=0}^{\infty} B_i$.
  have h_subset : s ⊆ ⋃ i, B i := by
    intro x hx;
    obtain ⟨ i, hi ⟩ := Set.mem_iUnion.1 ( hcover hx );
    induction' i using Nat.strong_induction_on with i ih;
    by_cases h : ∃ j < i, x ∈ A j <;> aesop;
  -- Since $B_i$ are pairwise disjoint and their union is $s$, we can apply the countable additivity of the premeasure.
  have h_countable_additivity : pm.μ₀ ⟨s, hs⟩ ≤ ∑' i, pm.μ₀ ⟨B i ∩ s, by
    convert FieldOfSets.inter_mem F₀ ( hA i ) hs |> fun h => FieldOfSets.diff_mem F₀ h ( show ( ⋃ j < i, A j ) ∈ F₀.carrier from ?_ ) using 1;
    · grind;
    · convert FieldOfSets.biUnion_range_mem F₀ ( fun j => hA j ) i using 1;
      simp +decide [ Finset.mem_range, Set.ext_iff ]⟩ := by
    all_goals generalize_proofs at *;
    have h_countable_additivity : pm.μ₀ ⟨⋃ i, (B i ∩ s), by
      convert hs using 1;
      exact Set.Subset.antisymm ( Set.iUnion_subset fun i => Set.inter_subset_right ) fun x hx => by rcases Set.mem_iUnion.1 ( h_subset hx ) with ⟨ i, hi ⟩ ; exact Set.mem_iUnion.2 ⟨ i, hi, hx ⟩ ;⟩ = ∑' i, pm.μ₀ ⟨B i ∩ s, by
      solve_by_elim⟩ := by
      apply pm.sigma_additive;
      intro i j hij; simp_all +decide [ Set.disjoint_left ] ;
      cases lt_or_gt_of_ne hij <;> aesop
    generalize_proofs at *;
    rw [ ← h_countable_additivity ];
    apply_rules [ Premeasure.mono ];
    exact fun x hx => by rcases Set.mem_iUnion.1 ( h_subset hx ) with ⟨ i, hi ⟩ ; exact Set.mem_iUnion.2 ⟨ i, hi, hx ⟩ ;
  generalize_proofs at *;
  refine' le_trans h_countable_additivity ( ENNReal.tsum_le_tsum fun i => _ );
  apply_rules [ Premeasure.mono ];
  exact fun x hx => hx.1.1

lemma Premeasure.outerMeasure_eq {F₀ : FieldOfSets X} (pm : Premeasure F₀)
    {s : Set X} (hs : s ∈ F₀.carrier) :
    pm.outerMeasure s = pm.μ₀ ⟨s, hs⟩ := by
  refine' le_antisymm _ _;
  · exact?;
  · refine' le_iInf fun f => le_iInf fun hf => _;
    by_cases h : ∃ i, f i∉F₀.carrier <;> simp_all +decide [ extend ];
    · obtain ⟨ i, hi ⟩ := h; rw [ ENNReal.tsum_eq_top_of_eq_top ] ; aesop;
      exact ⟨ i, by aesop ⟩;
    · exact?

lemma Premeasure.isCaratheodory {F₀ : FieldOfSets X} (pm : Premeasure F₀)
    {s : Set X} (hs : s ∈ F₀.carrier) :
    pm.outerMeasure.IsCaratheodory s := by
  -- By definition of outer measure, we know that for any set $t$, $\mu^*(t) \geq \mu^*(A \cap t) + \mu^*(t \setminus A)$.
  have h_outer_measure_ge : ∀ t : Set X, pm.outerMeasure t ≥ pm.outerMeasure (t ∩ s) + pm.outerMeasure (t \ s) := by
    intro t
    unfold Premeasure.outerMeasure
    refine' le_of_forall_le _;
    intro c hc;
    refine' le_trans hc _;
    refine' le_iInf fun f => le_iInf fun hf => _;
    refine' le_trans ( add_le_add ( iInf_le _ ( fun i => f i ∩ s ) ) ( iInf_le _ ( fun i => f i \ s ) ) ) _;
    refine' le_trans ( add_le_add ( iInf_le _ _ ) ( iInf_le _ _ ) ) _;
    · exact fun x hx => by rcases Set.mem_iUnion.1 ( hf hx.1 ) with ⟨ i, hi ⟩ ; exact Set.mem_iUnion.2 ⟨ i, hi, hx.2 ⟩ ;
    · exact fun x hx => by rcases Set.mem_iUnion.1 ( hf hx.1 ) with ⟨ i, hi ⟩ ; exact Set.mem_iUnion.2 ⟨ i, hi, hx.2 ⟩ ;
    · rw [ ← ENNReal.tsum_add ];
      refine' ENNReal.tsum_le_tsum fun i => _;
      by_cases hi : f i ∈ F₀.carrier <;> by_cases hi' : f i ∩ s ∈ F₀.carrier <;> by_cases hi'' : f i \ s ∈ F₀.carrier <;> simp +decide [ *, extend ];
      · have hdisj : Disjoint (f i ∩ s) (f i \ s) := by
          exact Set.disjoint_left.mpr fun _ hx₁ hx₂ => hx₂.2 hx₁.2
        have hunion_mem : (f i ∩ s) ∪ (f i \ s) ∈ F₀.carrier :=
          F₀.union_mem _ _ hi' hi''
        have hadd := Premeasure.additive pm hi' hi'' hdisj hunion_mem
        have hunion : (f i ∩ s) ∪ (f i \ s) = f i := Set.inter_union_sdiff _ _
        exact (hadd.symm.trans (congrArg pm.μ₀ (Subtype.ext hunion))).le
      · exact False.elim ( hi'' ( F₀.diff_mem hi hs ) );
      · exact False.elim ( hi' ( F₀.inter_mem hi hs ) );
      · exact False.elim ( hi' ( F₀.inter_mem hi hs ) );
  refine' fun t => le_antisymm _ _;
  · exact?;
  · exact h_outer_measure_ge t

lemma Premeasure.generateFrom_le_caratheodory {F₀ : FieldOfSets X} (pm : Premeasure F₀) :
    MeasurableSpace.generateFrom F₀.carrier ≤ pm.outerMeasure.caratheodory := by
  refine' MeasurableSpace.generateFrom_le _;
  intro s hs
  apply Premeasure.isCaratheodory pm hs

theorem extension_exists (F₀ : FieldOfSets X) (pm : Premeasure F₀) :
    ∃ μ : @Measure X (MeasurableSpace.generateFrom F₀.carrier),
      IsExtension F₀ pm μ := by
  letI : MeasurableSpace X := MeasurableSpace.generateFrom F₀.carrier
  let μ : Measure X :=
    Premeasure.outerMeasure pm |>.toMeasure <| Premeasure.generateFrom_le_caratheodory pm
  refine ⟨μ, ?_⟩
  unfold IsExtension
  intro s hs;
  have hmeas : MeasurableSet s := MeasurableSpace.measurableSet_generateFrom hs
  calc
    μ s = Premeasure.outerMeasure pm s := MeasureTheory.toMeasure_apply _ _ hmeas
    _ = pm.μ₀ ⟨s, hs⟩ := Premeasure.outerMeasure_eq pm hs

theorem extension_unique (F₀ : FieldOfSets X) (pm : Premeasure F₀)
    (hσ : IsSigmaFinite pm) :
    ∃! μ : @Measure X (MeasurableSpace.generateFrom F₀.carrier),
      IsExtension F₀ pm μ := by
  obtain ⟨ μ, hμ ⟩ := @extension_exists X F₀ pm;
  refine' ⟨ μ, hμ, fun ν hν => _ ⟩;
  obtain ⟨ A, hA₁, hA₂, hA₃ ⟩ := hσ;
  apply_rules [ MeasureTheory.Measure.ext_of_generateFrom_of_iUnion ];
  · exact?;
  · exact fun i => by rw [ hν _ ( hA₁ i ) ] ; exact ne_of_lt ( hA₃ i ) ;
  · intro s hs
    exact (hν s hs).trans (hμ s hs).symm

theorem thm_3_1 (F₀ : FieldOfSets X) (pm : Premeasure F₀) :
    (∃ μ : @Measure X (MeasurableSpace.generateFrom F₀.carrier),
      IsExtension F₀ pm μ) ∧
    (IsSigmaFinite pm →
      ∃! μ : @Measure X (MeasurableSpace.generateFrom F₀.carrier),
        IsExtension F₀ pm μ) :=
  ⟨extension_exists F₀ pm, extension_unique F₀ pm⟩
