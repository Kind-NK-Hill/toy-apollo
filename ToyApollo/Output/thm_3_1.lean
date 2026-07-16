import Mathlib
import ToyApollo.Output.def_3_1
import ToyApollo.Output.def_3_2
import ToyApollo.Output.def_3_3

-- Public extension contracts use Definition 3.2's canonical `IsExtension` interface.

/-!
# Carathéodory Extension Theorem

Let F₀ be a field of sets. A pre-measure μ₀ defined on F₀ extends to a measure on σ(F₀).
If μ₀ is σ-finite, the extension is unique.
-/

open Set MeasureTheory ENNReal

variable {X : Type*}

/-! ## Field of Sets properties -/

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

/-
PROVIDED SOLUTION
By induction on n. Base case: ⋃ i ∈ Finset.range 0, A i = ∅ ∈ F₀. Inductive step: ⋃ i ∈ Finset.range (n+1), A i = (⋃ i ∈ Finset.range n, A i) ∪ A n, which is in F₀ by union_mem and the IH.
-/
lemma FieldOfSets.biUnion_range_mem (F₀ : FieldOfSets X) {A : ℕ → Set X}
    (hA : ∀ i, A i ∈ F₀.carrier) (n : ℕ) :
    (⋃ i ∈ Finset.range n, A i) ∈ F₀.carrier := by
  induction' n with n ih;
  · simpa using F₀.empty_mem;
  · simp_all +decide [ Finset.range_add_one ];
    exact F₀.union_mem _ _ ( hA _ ) ih

/-! ## Premeasure properties -/

/-
PROVIDED SOLUTION
Use pm.sigma_additive with the sequence B where B 0 = s, B 1 = t, B i = ∅ for i ≥ 2. This is pairwise disjoint (using hst and later sets being ∅). The union is s ∪ t. The σ-additivity gives pm(⋃ B) = ∑' pm(B i). The tsum telescopes to pm(s) + pm(t) since pm(∅) = 0 for i ≥ 2.
-/
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

/-
PROVIDED SOLUTION
Since s ⊆ t, we have t = s ∪ (t \ s). Both s and t \ s are in F₀ (by diff_mem). They are disjoint. By Premeasure.additive, pm(t) = pm(s ∪ (t \ s)) = pm(s) + pm(t \ s) ≥ pm(s).
-/
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

/-! ## Outer measure construction -/

/-- The outer measure constructed from a premeasure on a field of sets. -/
noncomputable def Premeasure.outerMeasure {F₀ : FieldOfSets X} (pm : Premeasure F₀) :
    OuterMeasure X :=
  inducedOuterMeasure (fun s (hs : s ∈ F₀.carrier) => pm.μ₀ ⟨s, hs⟩) F₀.empty_mem pm.map_empty

/-
PROBLEM
The outer measure is at most the premeasure on field sets.

PROVIDED SOLUTION
pm.outerMeasure = inducedOuterMeasure ... = OuterMeasure.ofFunction (extend m) .... By OuterMeasure.ofFunction_le, μ*(s) ≤ extend m s. By extend_eq with hs, extend m s = pm.μ₀ ⟨s, hs⟩.
-/
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

/-
PROBLEM
Countable subadditivity of the premeasure on the field.

PROVIDED SOLUTION
Define B_i = s ∩ A_i \ (⋃ j ∈ Finset.range i, A j).

Properties:
- B_i ∈ F₀ (by inter_mem, diff_mem, biUnion_range_mem)
- B_i are pairwise disjoint
- ⋃ B_i = s (since s ⊆ ⋃ A_i)
- B_i ⊆ A_i

Then by σ-additivity of pm (since B_i are disjoint and ⋃ B_i = s ∈ F₀):
pm(s) = ∑ pm(B_i)

By monotonicity (pm.mono, since B_i ⊆ A_i, both in F₀):
pm(B_i) ≤ pm(A_i)

Hence pm(s) = ∑ pm(B_i) ≤ ∑ pm(A_i).
-/
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

/-
PROBLEM
The outer measure equals the premeasure on field sets.

PROVIDED SOLUTION
Apply le_antisymm.
- Upper bound: pm.outerMeasure_le hs gives pm.outerMeasure s ≤ pm.μ₀ ⟨s, hs⟩
- Lower bound: We need pm.μ₀ ⟨s, hs⟩ ≤ pm.outerMeasure s.
  Unfold pm.outerMeasure = inducedOuterMeasure ... = OuterMeasure.ofFunction (extend m) ....
  By ofFunction_apply, pm.outerMeasure s = ⨅ f, ⨅ (s ⊆ ⋃ f), ∑' n, extend m (f n).
  Need: pm.μ₀ ⟨s, hs⟩ ≤ ⨅ f, ⨅ (s ⊆ ⋃ f), ∑' n, extend m (f n).

  Use le_iInf twice: for any f with s ⊆ ⋃ f, show pm.μ₀ ⟨s, hs⟩ ≤ ∑' n, extend m (f n).

  By extend_eq_top, if any f n ∉ F₀.carrier, extend m (f n) = ⊤ and the sum is ⊤ ≥ pm.μ₀ ⟨s, hs⟩.

  If all f n ∈ F₀.carrier, then extend m (f n) = pm.μ₀ ⟨f n, _⟩ by extend_eq.
  Then use countably_subadditive: pm.μ₀ ⟨s, hs⟩ ≤ ∑' pm.μ₀ ⟨f n, _⟩ = ∑' extend m (f n).

  But we need to handle the case where not all f n are in F₀. We can use ENNReal.le_tsum_of_le or show the sum is ⊤ by finding one term that is ⊤.
-/
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

/-! ## Carathéodory measurability -/

/-
PROBLEM
Sets in the field are Carathéodory-measurable for the induced outer measure.

PROVIDED SOLUTION
Need to show ∀ t, pm.outerMeasure t = pm.outerMeasure (t ∩ s) + pm.outerMeasure (t \ s).

By OuterMeasure.isCaratheodory_iff_le', it suffices to show:
∀ t, pm.outerMeasure (t ∩ s) + pm.outerMeasure (t \ s) ≤ pm.outerMeasure t.

Unfold pm.outerMeasure = inducedOuterMeasure ... = OuterMeasure.ofFunction (extend m) ....

By ofFunction_apply, pm.outerMeasure t = ⨅ f, ⨅ (t ⊆ ⋃ f), ∑' n, extend m (f n).

For any cover f with t ⊆ ⋃ f:
- (fun n => f n ∩ s) covers t ∩ s
- (fun n => f n \ s) covers t \ s
- For each n: extend m (f n) ≥ extend m (f n ∩ s) + extend m (f n \ s)
  - If f n ∈ F₀: equality by additivity (f n = (f n ∩ s) ∪ (f n \ s), disjoint)
  - If f n ∉ F₀: extend m (f n) = ⊤ ≥ anything
- So ∑' extend m (f n) ≥ ∑' extend m (f n ∩ s) + ∑' extend m (f n \ s) ≥ μ*(t ∩ s) + μ*(t \ s)

Taking inf: μ*(t) ≥ μ*(t ∩ s) + μ*(t \ s).
-/
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

/-
PROBLEM
The generated σ-algebra is contained in the Carathéodory σ-algebra.

PROVIDED SOLUTION
Use MeasurableSpace.generateFrom_le. For every s ∈ F₀.carrier, we need s to be in the Carathéodory σ-algebra. This follows from Premeasure.isCaratheodory applied to s.
-/
lemma Premeasure.generateFrom_le_caratheodory {F₀ : FieldOfSets X} (pm : Premeasure F₀) :
    MeasurableSpace.generateFrom F₀.carrier ≤ pm.outerMeasure.caratheodory := by
  refine' MeasurableSpace.generateFrom_le _;
  intro s hs
  apply Premeasure.isCaratheodory pm hs

/-! ## Main theorems -/

/-
PROBLEM
Existence part of the extension theorem.

PROVIDED SOLUTION
Construct μ := pm.outerMeasure.toMeasure pm.generateFrom_le_caratheodory.

Use ⟨μ, fun s hs => ...⟩.

For any s with hs : s ∈ F₀.carrier:
- s is measurable in generateFrom F₀.carrier by measurableSet_generateFrom hs
- μ s = pm.outerMeasure s by toMeasure_apply (since s is measurable)
- pm.outerMeasure s = pm.μ₀ ⟨s, hs⟩ by outerMeasure_eq
-/
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

/-
PROBLEM
Uniqueness part of the extension theorem for σ-finite premeasures.

PROVIDED SOLUTION
From hσ, obtain (A, hA) where hA.1 : ∀ i, A i ∈ F₀.carrier, hA.2.1 : ⋃ i, A i = univ, hA.2.2 : ∀ i, pm.μ₀ ⟨A i, _⟩ < ∞.

From extension_exists, get ⟨μ, hμ⟩.

For uniqueness: take any ν with hν. Apply MeasureTheory.Measure.ext_of_generateFrom_of_iUnion with:
- C = F₀.carrier
- B = A
- rfl for the σ-algebra
- FieldOfSets.isPiSystem F₀
- hA.2.1 for the union = univ
- hA.1 for B i ∈ C
- For ν (B i) ≠ ⊤: by hν, ν (A i) = pm.μ₀ ⟨A i, _⟩ < ∞
- For agreement: ∀ s ∈ C, ν s = μ s since both equal pm.μ₀
-/
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

/--
**Carathéodory Extension Theorem (Existence + Uniqueness)**

Let F₀ be a field of sets and pm a pre-measure on F₀. Then:
1. There exists a measure μ on σ(F₀) that extends pm.
2. If pm is σ-finite, this extension is unique.
-/
theorem thm_3_1 (F₀ : FieldOfSets X) (pm : Premeasure F₀) :
    (∃ μ : @Measure X (MeasurableSpace.generateFrom F₀.carrier),
      IsExtension F₀ pm μ) ∧
    (IsSigmaFinite pm →
      ∃! μ : @Measure X (MeasurableSpace.generateFrom F₀.carrier),
        IsExtension F₀ pm μ) :=
  ⟨extension_exists F₀ pm, extension_unique F₀ pm⟩
