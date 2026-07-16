import ToyApollo.Output.def_3_5
import ToyApollo.Output.thm_3_1
import ToyApollo.Output.ex_3_1_2
import ToyApollo.Output.ex_3_1_4
import Mathlib

open MeasureTheory Set ENNReal Filter Topology

/-!
# Theorem 3.3: construction of the Lebesgue--Stieltjes measure

The proof deliberately stays on Mathlib's public `length`/`outer` construction layer.  The
project premeasure on `B0` is obtained by restricting that outer measure, and the final Borel
measure is obtained from the project's Caratheodory extension theorem (`extension_unique`).
-/

/-- The Mathlib Stieltjes-function construction core associated to the project's input data. -/
abbrev thm33Core (F : StieltjesMeasureFunction) : StieltjesFunction ℝ :=
  F.toStieltjesFunction

/-- The endpoint cost assigned to `(a, b]`. -/
noncomputable def thm33IntervalCost
    (F : StieltjesMeasureFunction) (a b : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (F b - F a)

/-- The carrier of a finite presentation by half-open intervals. -/
noncomputable def thm33IocUnion (I : Finset (ℝ × ℝ)) : Set ℝ :=
  ⋃ p ∈ I, Ioc p.1 p.2

/-- The total endpoint cost of a finite interval presentation. -/
noncomputable def thm33IocCost
    (F : StieltjesMeasureFunction) (I : Finset (ℝ × ℝ)) : ℝ≥0∞ :=
  ∑ p ∈ I, thm33IntervalCost F p.1 p.2

theorem thm33_intervalCost_nonneg
    (F : StieltjesMeasureFunction) (a b : ℝ) :
    0 ≤ thm33IntervalCost F a b :=
  bot_le

/-- Endpoint costs telescope on adjacent ordered intervals. -/
theorem thm33_intervalCost_telescope
    (F : StieltjesMeasureFunction) {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    thm33IntervalCost F a c =
      thm33IntervalCost F a b + thm33IntervalCost F b c := by
  unfold thm33IntervalCost
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr (F.non_decreasing hab))
    (sub_nonneg.mpr (F.non_decreasing hbc))]
  congr 1
  ring

/-- Mathlib's public interval-length construction has the required endpoint value. -/
theorem thm33_length_Ioc
    (F : StieltjesMeasureFunction) (a b : ℝ) :
    (thm33Core F).length (Ioc a b) = thm33IntervalCost F a b := by
  simpa [thm33Core, thm33IntervalCost,
    StieltjesMeasureFunction.toStieltjesFunction] using
    ((thm33Core F).length_Ioc a b)

/-- The public outer-measure construction has the required endpoint value. -/
theorem thm33_outer_Ioc
    (F : StieltjesMeasureFunction) (a b : ℝ) :
    (thm33Core F).outer (Ioc a b) = thm33IntervalCost F a b := by
  simpa [thm33Core, thm33IntervalCost,
    StieltjesMeasureFunction.toStieltjesFunction] using
    ((thm33Core F).outer_Ioc a b)

/-- Every half-open interval is measurable for the construction's Caratheodory space. -/
theorem thm33_Ioc_caratheodory
    (F : StieltjesMeasureFunction) (a b : ℝ) :
    MeasurableSet[(thm33Core F).outer.caratheodory] (Ioc a b) :=
  (thm33Core F).borel_le_measurable _ <| by
    borelize ℝ
    exact measurableSet_Ioc

/-- A finite union of half-open intervals is Caratheodory measurable. -/
theorem thm33_iocUnion_caratheodory
    (F : StieltjesMeasureFunction) (I : Finset (ℝ × ℝ)) :
    MeasurableSet[(thm33Core F).outer.caratheodory] (thm33IocUnion I) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [thm33IocUnion]
  | @insert p I hp hI =>
      simpa [thm33IocUnion, hp] using
        (thm33_Ioc_caratheodory F p.1 p.2).union hI

/-- The outer measure viewed as a measure on its own Caratheodory measurable space.
The measurable-space instance is explicit so that typeclass inference cannot select the standard
Borel instance on `ℝ`. -/
private noncomputable def thm33CaratheodoryMeasure
    (F : StieltjesMeasureFunction) :
    @Measure ℝ (thm33Core F).outer.caratheodory :=
  @OuterMeasure.toMeasure ℝ (thm33Core F).outer.caratheodory
    (thm33Core F).outer le_rfl

private theorem thm33CaratheodoryMeasure_apply
    (F : StieltjesMeasureFunction) {s : Set ℝ}
    (hs : MeasurableSet[(thm33Core F).outer.caratheodory] s) :
    thm33CaratheodoryMeasure F s = (thm33Core F).outer s :=
  @MeasureTheory.toMeasure_apply ℝ (thm33Core F).outer.caratheodory
    (thm33Core F).outer le_rfl s hs

/-- The outer measure of a finite disjoint presentation is its endpoint sum. -/
theorem thm33_outer_finiteDisjointIoc
    (F : StieltjesMeasureFunction) (I : Finset (ℝ × ℝ))
    (hI : (I : Set (ℝ × ℝ)).PairwiseDisjoint
      (fun p => Ioc p.1 p.2)) :
    (thm33Core F).outer (thm33IocUnion I) = thm33IocCost F I := by
  classical
  let m : @Measure ℝ (thm33Core F).outer.caratheodory :=
    thm33CaratheodoryMeasure F
  calc
    (thm33Core F).outer (thm33IocUnion I) = m (thm33IocUnion I) := by
      symm
      simpa [m] using
        (thm33CaratheodoryMeasure_apply F
          (thm33_iocUnion_caratheodory F I))
    _ = ∑ p ∈ I, m (Ioc p.1 p.2) := by
      simpa [thm33IocUnion] using
        (measure_biUnion_finset (μ := m) hI
          (fun p _ => thm33_Ioc_caratheodory F p.1 p.2))
    _ = ∑ p ∈ I, (thm33Core F).outer (Ioc p.1 p.2) := by
      apply Finset.sum_congr rfl
      intro p _
      simpa [m] using
        (thm33CaratheodoryMeasure_apply F
          (thm33_Ioc_caratheodory F p.1 p.2))
    _ = thm33IocCost F I := by
      simp [thm33IocCost, thm33IntervalCost, thm33Core,
        StieltjesMeasureFunction.toStieltjesFunction]

/-- The endpoint sum is independent of the chosen finite disjoint presentation. -/
theorem thm33_iocCost_wellDefined
    (F : StieltjesMeasureFunction) (I J : Finset (ℝ × ℝ))
    (hI : (I : Set (ℝ × ℝ)).PairwiseDisjoint
      (fun p => Ioc p.1 p.2))
    (hJ : (J : Set (ℝ × ℝ)).PairwiseDisjoint
      (fun p => Ioc p.1 p.2))
    (hcarrier : thm33IocUnion I = thm33IocUnion J) :
    thm33IocCost F I = thm33IocCost F J := by
  calc
    thm33IocCost F I = (thm33Core F).outer (thm33IocUnion I) :=
      (thm33_outer_finiteDisjointIoc F I hI).symm
    _ = (thm33Core F).outer (thm33IocUnion J) := congrArg _ hcarrier
    _ = thm33IocCost F J := thm33_outer_finiteDisjointIoc F J hJ

/-- The construction is finitely additive on disjoint finite interval presentations. -/
theorem thm33_iocCost_finitelyAdditive
    (F : StieltjesMeasureFunction) (I J : Finset (ℝ × ℝ))
    (hI : (I : Set (ℝ × ℝ)).PairwiseDisjoint
      (fun p => Ioc p.1 p.2))
    (hJ : (J : Set (ℝ × ℝ)).PairwiseDisjoint
      (fun p => Ioc p.1 p.2))
    (hIJ : Disjoint (thm33IocUnion I) (thm33IocUnion J)) :
    (thm33Core F).outer (thm33IocUnion I ∪ thm33IocUnion J) =
      thm33IocCost F I + thm33IocCost F J := by
  let m : @Measure ℝ (thm33Core F).outer.caratheodory :=
    thm33CaratheodoryMeasure F
  have hIc := thm33_iocUnion_caratheodory F I
  have hJc := thm33_iocUnion_caratheodory F J
  calc
    (thm33Core F).outer (thm33IocUnion I ∪ thm33IocUnion J) =
        m (thm33IocUnion I ∪ thm33IocUnion J) := by
      symm
      simpa [m] using
        (thm33CaratheodoryMeasure_apply F (hIc.union hJc))
    _ = m (thm33IocUnion I) + m (thm33IocUnion J) :=
      measure_union hIJ hJc
    _ = (thm33Core F).outer (thm33IocUnion I) +
        (thm33Core F).outer (thm33IocUnion J) := by
      rw [show m (thm33IocUnion I) = (thm33Core F).outer (thm33IocUnion I) by
          simpa [m] using thm33CaratheodoryMeasure_apply F hIc,
        show m (thm33IocUnion J) = (thm33Core F).outer (thm33IocUnion J) by
          simpa [m] using thm33CaratheodoryMeasure_apply F hJc]
    _ = thm33IocCost F I + thm33IocCost F J := by
      rw [thm33_outer_finiteDisjointIoc F I hI,
        thm33_outer_finiteDisjointIoc F J hJ]

/-- Right continuity supplies a strictly larger right endpoint of arbitrarily small cost. -/
theorem thm33_right_enlarge
    (F : StieltjesMeasureFunction) (a : ℝ) {eps : ℝ}
    (heps : 0 < eps) :
    ∃ a' : ℝ, a < a' ∧ F a' - F a < eps := by
  have hcont : ContinuousWithinAt (fun r : ℝ => F r - F a) (Ioi a) a := by
    refine ContinuousWithinAt.sub ?_ continuousWithinAt_const
    exact (F.right_continuous a).mono Ioi_subset_Ici_self
  have hbase : F a - F a < eps := by
    simpa using heps
  have : (𝓝[>] a).NeBot :=
    nhdsGT_neBot_of_exists_gt ⟨a + 1, by linarith⟩
  rcases (((tendsto_order.1 hcont).2 _ hbase).and self_mem_nhdsWithin).exists with
    ⟨a', hdiff, ha'⟩
  exact ⟨a', ha', hdiff⟩

/-- The compact-cover estimate used in the interval outer-measure construction. -/
theorem thm33_compact_cover_estimate
    (F : StieltjesMeasureFunction) {a b : ℝ}
    {c d : ℕ → ℝ}
    (hcover : Icc a b ⊆ ⋃ i, Iotop (c i) (d i)) :
    thm33IntervalCost F a b ≤
      ∑' i, thm33IntervalCost F (c i) (d i) := by
  simpa [thm33Core, thm33IntervalCost,
    StieltjesMeasureFunction.toStieltjesFunction] using
    ((thm33Core F).length_subadditive_Icc_Ioo hcover)

/-- Countable subadditivity for a half-open interval cover. -/
theorem thm33_interval_countablySubadditive
    (F : StieltjesMeasureFunction) {a b : ℝ}
    {c d : ℕ → ℝ}
    (hcover : Ioc a b ⊆ ⋃ i, Ioc (c i) (d i)) :
    thm33IntervalCost F a b ≤
      ∑' i, thm33IntervalCost F (c i) (d i) := by
  calc
    thm33IntervalCost F a b = (thm33Core F).outer (Ioc a b) :=
      (thm33_outer_Ioc F a b).symm
    _ ≤ (thm33Core F).outer (⋃ i, Ioc (c i) (d i)) := measure_mono hcover
    _ ≤ ∑' i, (thm33Core F).outer (Ioc (c i) (d i)) :=
      measure_iUnion_le _
    _ = ∑' i, thm33IntervalCost F (c i) (d i) := by
      simp only [thm33_outer_Ioc]

/-- Every member of the project's interval field is Caratheodory measurable. -/
theorem thm33_B0_caratheodory
    (F : StieltjesMeasureFunction) (s : Set ℝ)
    (hs : s ∈ B0.carrier) :
    MeasurableSet[(thm33Core F).outer.caratheodory] s :=
  (thm33Core F).borel_le_measurable _ <| by
    borelize ℝ
    exact measurable_of_mem_B0 s hs

/-- The source premeasure: restriction of the constructed outer measure to `B0`. -/
noncomputable def thm33B0Premeasure
    (F : StieltjesMeasureFunction) : Premeasure B0 where
  μ₀ := fun s => (thm33Core F).outer s.1
  map_empty := by
    simp
  sigma_additive := by
    intro A hA _ hdisj
    exact (thm33Core F).outer.iUnion_eq_of_caratheodory
      (fun i => thm33_B0_caratheodory F (A i) (hA i)) hdisj

/-- The project premeasure evaluates a generator `(a, b]` by endpoint difference. -/
theorem thm33B0Premeasure_Ioc
    (F : StieltjesMeasureFunction) (a b : ℝ) :
    (thm33B0Premeasure F).μ₀
        ⟨Ioc a b, GeneratedField.basic _ (Or.inl ⟨a, b, rfl⟩)⟩ =
      ENNReal.ofReal (F b - F a) := by
  change (thm33Core F).outer (Ioc a b) = thm33IntervalCost F a b
  exact thm33_outer_Ioc F a b

/-- Symmetric integer windows used for sigma-finiteness. -/
noncomputable def thm33Window (n : ℕ) : Set ℝ :=
  Ioc (-((n + 1 : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))

theorem thm33Window_mem_B0 (n : ℕ) :
    thm33Window n ∈ B0.carrier :=
  GeneratedField.basic _
    (Or.inl ⟨-((n + 1 : ℕ) : ℝ), ((n + 1 : ℕ) : ℝ), rfl⟩)

theorem iUnion_thm33Window :
    (⋃ n : ℕ, thm33Window n) = (univ : Set ℝ) := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    rcases exists_nat_gt |x| with ⟨n, hn⟩
    refine mem_iUnion.mpr ⟨n, ?_⟩
    rw [thm33Window, mem_Ioc]
    have hbound : |x| < (((n + 1 : ℕ) : ℝ)) := by
      exact hn.trans (by exact_mod_cast Nat.lt_succ_self n)
    exact ⟨(neg_lt_neg hbound).trans_le (neg_abs_le x),
      (le_abs_self x).trans hbound.le⟩

theorem thm33Window_cost_lt_top
    (F : StieltjesMeasureFunction) (n : ℕ) :
    (thm33B0Premeasure F).μ₀
      ⟨thm33Window n, thm33Window_mem_B0 n⟩ < ∞ := by
  change (thm33Core F).outer (thm33Window n) < ∞
  rw [thm33Window, thm33_outer_Ioc]
  exact ENNReal.ofReal_lt_top

/-- The source premeasure is sigma-finite by integer interval exhaustion. -/
theorem thm33B0Premeasure_sigmaFinite
    (F : StieltjesMeasureFunction) :
    IsSigmaFinite (thm33B0Premeasure F) := by
  refine ⟨thm33Window, thm33Window_mem_B0, iUnion_thm33Window, ?_⟩
  exact thm33Window_cost_lt_top F

/-- The unique extension supplied by the project's Theorem 3.1. -/
theorem thm33_projectExtension_unique
    (F : StieltjesMeasureFunction) :
    ∃! μ : @Measure ℝ (MeasurableSpace.generateFrom B0.carrier),
      ∀ (s : Set ℝ) (hs : s ∈ B0.carrier),
        μ s = (thm33B0Premeasure F).μ₀ ⟨s, hs⟩ := by
  simpa only [IsExtension] using
    (extension_unique B0 (thm33B0Premeasure F)
      (thm33B0Premeasure_sigmaFinite F))

private theorem thm33_generateFrom_B0_eq_real_measurable :
    MeasurableSpace.generateFrom B0.carrier =
      (inferInstance : MeasurableSpace ℝ) :=
  generateFrom_B0_eq_borel.trans BorelSpace.measurable_eq.symm

private theorem thm33_castMeasure_apply
    {X : Type*} {m₁ m₂ : MeasurableSpace X}
    (h : m₁ = m₂) (μ : @Measure X m₁) (s : Set X) :
    (Eq.mp (congrArg (fun m => @Measure X m) h) μ) s = μ s := by
  subst m₂
  rfl

/-- Transport a project extension from `generateFrom B0` to the standard Borel space. -/
noncomputable def thm33TransportToBorel
    (μ : @Measure ℝ (MeasurableSpace.generateFrom B0.carrier)) :
    Measure ℝ :=
  Eq.mp
    (congrArg (fun m => @Measure ℝ m) thm33_generateFrom_B0_eq_real_measurable)
    μ

theorem thm33_projectExtension_Ioc
    (F : StieltjesMeasureFunction)
    (μ₀ : @Measure ℝ (MeasurableSpace.generateFrom B0.carrier))
    (hμ₀ : ∀ (s : Set ℝ) (hs : s ∈ B0.carrier),
      μ₀ s = (thm33B0Premeasure F).μ₀ ⟨s, hs⟩)
    (a b : ℝ) :
    thm33TransportToBorel μ₀ (Ioc a b) =
      ENNReal.ofReal (F b - F a) := by
  let hIoc : Ioc a b ∈ B0.carrier :=
    GeneratedField.basic _ (Or.inl ⟨a, b, rfl⟩)
  calc
    thm33TransportToBorel μ₀ (Ioc a b) = μ₀ (Ioc a b) := by
      simpa [thm33TransportToBorel] using
        (thm33_castMeasure_apply thm33_generateFrom_B0_eq_real_measurable
          μ₀ (Ioc a b))
    _ = (thm33B0Premeasure F).μ₀ ⟨Ioc a b, hIoc⟩ := hμ₀ _ hIoc
    _ = ENNReal.ofReal (F b - F a) := thm33B0Premeasure_Ioc F a b

/-- Any Borel measure satisfying the interval formula is locally finite. -/
theorem thm33_isLocallyFinite_of_Ioc_formula
    (F : StieltjesMeasureFunction)
    (μ : Measure ℝ)
    (hμ : ∀ a b : ℝ,
      μ (Ioc a b) = ENNReal.ofReal (F b - F a)) :
    IsLocallyFiniteMeasure μ := by
  constructor
  intro x
  refine ⟨Ioo (x - 1) (x + 1),
    Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  calc
    μ (Ioo (x - 1) (x + 1)) ≤ μ (Ioc (x - 1) (x + 1)) :=
      measure_mono Ioo_subset_Ioc_self
    _ = ENNReal.ofReal (F (x + 1) - F (x - 1)) := hμ (x - 1) (x + 1)
    _ < ∞ := ENNReal.ofReal_lt_top

/--
The Lebesgue--Stieltjes measure induced by a nondecreasing right-continuous function.

The witness is obtained from the project premeasure and the project's extension theorem.  The
interval extensionality theorem appears only after that construction, to express uniqueness in
the source's interval-only public interface.
-/
theorem thm_3_3 (F : StieltjesMeasureFunction) :
    ∃! μ : Measure ℝ,
      ∀ a b : ℝ, μ (Ioc a b) = ENNReal.ofReal (F b - F a) := by
  rcases thm33_projectExtension_unique F with ⟨μ₀, hμ₀, _huniq₀⟩
  let μ : Measure ℝ := thm33TransportToBorel μ₀
  have hIoc : ∀ a b : ℝ,
      μ (Ioc a b) = ENNReal.ofReal (F b - F a) :=
    thm33_projectExtension_Ioc F μ₀ hμ₀
  refine ⟨μ, hIoc, ?_⟩
  intro ν hν
  letI : IsLocallyFiniteMeasure μ :=
    thm33_isLocallyFinite_of_Ioc_formula F μ hIoc
  symm
  exact Measure.ext_of_Ioc μ ν fun a b _ =>
    (hIoc a b).trans (hν a b).symm
