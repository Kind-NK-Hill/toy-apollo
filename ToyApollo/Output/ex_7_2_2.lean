/-
TASK ID: ex_7_2_2
TYPE: Example_Proof
SOURCE PLAN: 26_chap7_fatou_dct
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set

abbrev UnitIntervalRat : Set ℚ := Set.Icc (0 : ℚ) 1

lemma unitIntervalRat_countable : (UnitIntervalRat).Countable := by
  refine Set.Countable.mono (fun _ hx => by simp) Set.countable_univ

lemma unitIntervalRat_infinite : (UnitIntervalRat).Infinite := by
  simpa [UnitIntervalRat] using
    (Set.Icc_infinite (α := ℚ) (a := (0 : ℚ)) (b := 1) (by norm_num : (0 : ℚ) < 1))

@[reducible] noncomputable def unitIntervalRatDenumerable : Denumerable UnitIntervalRat := by
  exact
    Classical.choice
      ((Set.countable_infinite_iff_nonempty_denumerable).1
        ⟨unitIntervalRat_countable, unitIntervalRat_infinite⟩)

attribute [local instance] unitIntervalRatDenumerable

noncomputable def ex722Rat : ℕ → UnitIntervalRat :=
  (Denumerable.eqv UnitIntervalRat).symm

noncomputable def ex722RatReal (n : ℕ) : ℝ :=
  ((ex722Rat n : ℚ) : ℝ)

theorem ex722Rat_injective : Function.Injective ex722Rat := by
  simpa [ex722Rat] using (Denumerable.eqv UnitIntervalRat).symm.injective

theorem ex722Rat_surjective : Function.Surjective ex722Rat := by
  simpa [ex722Rat] using (Denumerable.eqv UnitIntervalRat).symm.surjective

theorem ex722RatReal_injective : Function.Injective ex722RatReal := by
  intro m n h
  apply ex722Rat_injective
  exact Subtype.ext (Rat.cast_injective h)

theorem ex722RatReal_mem_unitInterval (n : ℕ) : ex722RatReal n ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · change (0 : ℝ) ≤ (((ex722Rat n : ℚ) : ℝ))
    exact_mod_cast (ex722Rat n).property.1
  · change (((ex722Rat n : ℚ) : ℝ)) ≤ (1 : ℝ)
    exact_mod_cast (ex722Rat n).property.2

noncomputable def ex722PartialSupport (n : ℕ) : Set ℝ :=
  ↑((Finset.range n).image ex722RatReal)

theorem mem_ex722PartialSupport_iff {n : ℕ} {x : ℝ} :
    x ∈ ex722PartialSupport n ↔ ∃ k < n, x = ex722RatReal k := by
  simp [ex722PartialSupport, eq_comm]

theorem ex722PartialSupport_finite (n : ℕ) : (ex722PartialSupport n).Finite := by
  classical
  simpa [ex722PartialSupport] using (((Finset.range n).image ex722RatReal).finite_toSet)

theorem ex722PartialSupport_subset_unitInterval (n : ℕ) :
    ex722PartialSupport n ⊆ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  rcases (mem_ex722PartialSupport_iff.mp hx) with ⟨k, hk, rfl⟩
  exact ex722RatReal_mem_unitInterval k

theorem ex722PartialSupport_measure_zero (n : ℕ) :
    volume (ex722PartialSupport n) = 0 := by
  exact (ex722PartialSupport_finite n).measure_zero volume

noncomputable def ex722PartialFun (n : ℕ) : ℝ → ℝ := fun x =>
  ∑ k ∈ Finset.range n,
    (({ex722RatReal k} : Set ℝ).indicator (fun _ : ℝ => (1 : ℝ))) x

theorem ex722PartialFun_eq_zero_of_notMem (n : ℕ) {x : ℝ} (hx : x ∉ ex722PartialSupport n) :
    ex722PartialFun n x = 0 := by
  rw [ex722PartialFun]
  refine Finset.sum_eq_zero ?_
  intro k hk
  have hnot : x ∉ ({ex722RatReal k} : Set ℝ) := by
    intro hxk
    apply hx
    exact mem_ex722PartialSupport_iff.mpr ⟨k, Finset.mem_range.mp hk, by simpa using hxk⟩
  rw [Set.indicator_of_notMem hnot]

theorem ex722PartialFun_continuousAt_of_notMem (n : ℕ) {x : ℝ} (hx : x ∉ ex722PartialSupport n) :
    ContinuousAt (ex722PartialFun n) x := by
  have hclosed : IsClosed (ex722PartialSupport n) := (ex722PartialSupport_finite n).isClosed
  have hnhds : (ex722PartialSupport n)ᶜ ∈ nhds x := hclosed.isOpen_compl.mem_nhds hx
  have hzero : ∀ᶠ y in nhds x, ex722PartialFun n y = 0 := by
    filter_upwards [hnhds] with y hy
    exact ex722PartialFun_eq_zero_of_notMem n hy
  have hx0 : ex722PartialFun n x = 0 := ex722PartialFun_eq_zero_of_notMem n hx
  have hzero' : (fun _ : ℝ => (0 : ℝ)) =ᶠ[nhds x] ex722PartialFun n := by
    filter_upwards [hzero] with y hy
    exact hy.symm
  have hconst : Tendsto (fun _ : ℝ => (0 : ℝ)) (nhds x) (nhds (0 : ℝ)) := tendsto_const_nhds
  rw [ContinuousAt]
  have ht : Tendsto (ex722PartialFun n) (nhds x) (nhds (0 : ℝ)) :=
    Tendsto.congr' hzero' hconst
  simpa [hx0] using ht

theorem ex722PartialFun_ae_eq_zero (n : ℕ) :
    ex722PartialFun n =ᵐ[volume] fun _ : ℝ => (0 : ℝ) := by
  have hzero : ∀ᵐ x ∂volume, ex722PartialFun n x = 0 := by
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_ (ex722PartialSupport_measure_zero n)
    intro x hx
    by_contra hx_support
    exact hx (ex722PartialFun_eq_zero_of_notMem n hx_support)
  filter_upwards [hzero] with x hx
  exact hx

theorem ex722PartialFun_integral_zero (n : ℕ) :
    ∫ x, ex722PartialFun n x ∂volume = 0 := by
  calc
    ∫ x, ex722PartialFun n x ∂volume = ∫ x, (0 : ℝ) ∂volume := by
      exact integral_congr_ae (ex722PartialFun_ae_eq_zero n)
    _ = 0 := by simp

theorem ex722PartialFun_integral_unitInterval_zero (n : ℕ) :
    ∫ x in Set.Icc (0 : ℝ) 1, ex722PartialFun n x ∂volume = 0 := by
  rw [← integral_indicator measurableSet_Icc]
  have hrestrict :
      (Set.Icc (0 : ℝ) 1).indicator (ex722PartialFun n) = ex722PartialFun n := by
    funext x
    by_cases hxI : x ∈ Set.Icc (0 : ℝ) 1
    · simp [hxI]
    · have hxnot : x ∉ ex722PartialSupport n := by
        intro hx
        exact hxI (ex722PartialSupport_subset_unitInterval n hx)
      simp [hxI, ex722PartialFun_eq_zero_of_notMem n hxnot]
  rw [hrestrict]
  exact ex722PartialFun_integral_zero n

def ex722LimitSupport : Set ℝ :=
  {x | x ∈ Set.Icc (0 : ℝ) 1 ∧ ∃ q : ℚ, x = q}

noncomputable def ex722LimitFun (x : ℝ) : ℝ :=
  by
    classical
    exact if x ∈ ex722LimitSupport then 1 else 0

theorem ex722PartialSupport_subset_limitSupport (n : ℕ) :
    ex722PartialSupport n ⊆ ex722LimitSupport := by
  intro x hx
  rcases (mem_ex722PartialSupport_iff.mp hx) with ⟨k, hk, rfl⟩
  exact ⟨ex722RatReal_mem_unitInterval k, (ex722Rat k : ℚ), rfl⟩

theorem ex722LimitFun_eq_one_of_rational {q : ℚ} (hq : (q : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    ex722LimitFun (q : ℝ) = 1 := by
  classical
  have hmem : (q : ℝ) ∈ ex722LimitSupport := ⟨hq, q, rfl⟩
  rw [ex722LimitFun, if_pos hmem]

theorem ex722LimitFun_eq_zero_of_irrational {x : ℝ} (hx : Irrational x) :
    ex722LimitFun x = 0 := by
  classical
  have hnot : x ∉ ex722LimitSupport := by
    intro hmem
    rcases hmem with ⟨hxI, q, hq⟩
    have : Irrational ((q : ℚ) : ℝ) := by simpa [hq] using hx
    exact (Rat.not_irrational q) this
  rw [ex722LimitFun, if_neg hnot]

theorem ex722LimitFun_eq_zero_of_not_mem_unitInterval {x : ℝ}
    (hx : x ∉ Set.Icc (0 : ℝ) 1) : ex722LimitFun x = 0 := by
  classical
  have hnot : x ∉ ex722LimitSupport := fun hmem => hx hmem.1
  rw [ex722LimitFun, if_neg hnot]

theorem ex722PartialFun_eq_one_of_encode_lt {q : UnitIntervalRat} {n : ℕ}
    (hq : (Denumerable.eqv UnitIntervalRat) q < n) : ex722PartialFun n ((q : ℚ) : ℝ) = 1 := by
  classical
  let k : ℕ := (Denumerable.eqv UnitIntervalRat) q
  have hk_mem : k ∈ Finset.range n := by
    simpa [k] using hq
  have hk_rat : ex722Rat k = q := by
    change (Denumerable.eqv UnitIntervalRat).symm ((Denumerable.eqv UnitIntervalRat) q) = q
    exact (Denumerable.eqv UnitIntervalRat).symm_apply_apply q
  have hk_val : ex722RatReal k = ((q : ℚ) : ℝ) := by
    simpa [ex722RatReal, hk_rat]
  rw [ex722PartialFun, Finset.sum_eq_single k]
  · have hmem : ((q : ℚ) : ℝ) ∈ ({ex722RatReal k} : Set ℝ) := by
      simp [hk_val]
    rw [Set.indicator_of_mem hmem]
  · intro j hj hjne
    have hnot : ((q : ℚ) : ℝ) ∉ ({ex722RatReal j} : Set ℝ) := by
      intro hjq
      apply hjne
      apply ex722RatReal_injective
      exact hjq.symm.trans hk_val.symm
    rw [Set.indicator_of_notMem hnot]
  · intro hk_not_mem
    exact (hk_not_mem hk_mem).elim

theorem ex722PartialFun_eventually_eq_one {q : ℚ} (hq : (q : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᶠ n in atTop, ex722PartialFun n (q : ℝ) = 1 := by
  let uq : UnitIntervalRat :=
    ⟨q, by exact_mod_cast hq.1, by exact_mod_cast hq.2⟩
  let k : ℕ := (Denumerable.eqv UnitIntervalRat) uq
  filter_upwards [eventually_ge_atTop (k + 1)] with n hn
  have hlt : (Denumerable.eqv UnitIntervalRat) uq < n := by
    exact lt_of_lt_of_le (Nat.lt_succ_self k) hn
  simpa [uq] using ex722PartialFun_eq_one_of_encode_lt (q := uq) hlt

theorem ex722PartialFun_eq_zero_of_irrational (n : ℕ) {x : ℝ} (hx : Irrational x) :
    ex722PartialFun n x = 0 := by
  classical
  rw [ex722PartialFun]
  refine Finset.sum_eq_zero ?_
  intro k hk
  have hnot : x ∉ ({ex722RatReal k} : Set ℝ) := by
    intro hxk
    have hxeq : x = ex722RatReal k := by simpa using hxk
    have hqirr : Irrational (ex722RatReal k) := by simpa [hxeq] using hx
    exact (Rat.not_irrational (ex722Rat k : ℚ)) hqirr
  rw [Set.indicator_of_notMem hnot]

theorem ex722PartialFun_tendsto_at_rational {q : ℚ} (hq : (q : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n => ex722PartialFun n (q : ℝ)) atTop (nhds (ex722LimitFun (q : ℝ))) := by
  have hevent : ∀ᶠ n in atTop, ex722PartialFun n (q : ℝ) = 1 :=
    ex722PartialFun_eventually_eq_one hq
  have hlimit : ex722LimitFun (q : ℝ) = 1 := ex722LimitFun_eq_one_of_rational hq
  have hevent' : (fun _ : ℕ => (1 : ℝ)) =ᶠ[atTop] fun n => ex722PartialFun n (q : ℝ) := by
    filter_upwards [hevent] with n hn
    exact hn.symm
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds (1 : ℝ)) := tendsto_const_nhds
  have ht : Tendsto (fun n => ex722PartialFun n (q : ℝ)) atTop (nhds (1 : ℝ)) :=
    Tendsto.congr' hevent' hconst
  simpa [hlimit] using ht

theorem ex722PartialFun_tendsto_at_irrational {x : ℝ} (hx : Irrational x) :
    Tendsto (fun n => ex722PartialFun n x) atTop (nhds (ex722LimitFun x)) := by
  have hevent : ∀ᶠ n in atTop, ex722PartialFun n x = 0 :=
    Filter.Eventually.of_forall fun n => ex722PartialFun_eq_zero_of_irrational n hx
  have hlimit : ex722LimitFun x = 0 := ex722LimitFun_eq_zero_of_irrational hx
  have hevent' : (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop] fun n => ex722PartialFun n x := by
    filter_upwards [hevent] with n hn
    exact hn.symm
  have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds (0 : ℝ)) := tendsto_const_nhds
  have ht : Tendsto (fun n => ex722PartialFun n x) atTop (nhds (0 : ℝ)) :=
    Tendsto.congr' hevent' hconst
  simpa [hlimit] using ht

theorem ex722PartialFun_tendsto_outside_unitInterval {x : ℝ} (hx : x ∉ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n => ex722PartialFun n x) atTop (nhds (ex722LimitFun x)) := by
  have hevent : ∀ᶠ n in atTop, ex722PartialFun n x = 0 := by
    refine Filter.Eventually.of_forall ?_
    intro n
    exact ex722PartialFun_eq_zero_of_notMem n (by
      intro hmem
      exact hx (ex722PartialSupport_subset_unitInterval n hmem))
  have hlimit : ex722LimitFun x = 0 := ex722LimitFun_eq_zero_of_not_mem_unitInterval hx
  have hevent' : (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop] fun n => ex722PartialFun n x := by
    filter_upwards [hevent] with n hn
    exact hn.symm
  have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds (0 : ℝ)) := tendsto_const_nhds
  have ht : Tendsto (fun n => ex722PartialFun n x) atTop (nhds (0 : ℝ)) :=
    Tendsto.congr' hevent' hconst
  simpa [hlimit] using ht

theorem ex722PartialFun_tendsto_limit (x : ℝ) :
    Tendsto (fun n => ex722PartialFun n x) atTop (nhds (ex722LimitFun x)) := by
  by_cases hxI : x ∈ Set.Icc (0 : ℝ) 1
  · by_cases hxirr : Irrational x
    · exact ex722PartialFun_tendsto_at_irrational hxirr
    · rcases exists_rat_of_not_irrational hxirr with ⟨q, rfl⟩
      exact ex722PartialFun_tendsto_at_rational hxI
  · exact ex722PartialFun_tendsto_outside_unitInterval hxI

theorem ex722LimitFun_hits_one_on_every_open_subinterval {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ x ∈ Set.Ioo a b, ex722LimitFun x = 1 := by
  obtain ⟨q, haq, hqb⟩ := exists_rat_btwn hab
  refine ⟨(q : ℝ), ⟨haq, hqb⟩, ?_⟩
  have hqI : (q : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact le_of_lt (lt_of_le_of_lt ha haq)
    · exact le_trans hqb.le hb
  exact ex722LimitFun_eq_one_of_rational hqI

theorem ex722LimitFun_hits_zero_on_every_open_subinterval {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ x ∈ Set.Ioo a b, ex722LimitFun x = 0 := by
  obtain ⟨x, hxirr, hax, hxb⟩ := exists_irrational_btwn hab
  exact ⟨x, ⟨hax, hxb⟩, ex722LimitFun_eq_zero_of_irrational hxirr⟩

structure LimitOfRiemannIntegrableFunctionsCounterexample where
  ratEnum : ℕ → UnitIntervalRat
  ratEnum_def : ratEnum = ex722Rat
  ratEnum_injective : Function.Injective ratEnum
  ratEnum_surjective : Function.Surjective ratEnum
  partialSupport : ℕ → Set ℝ
  partialSupport_def : partialSupport = ex722PartialSupport
  partialSeq : ℕ → ℝ → ℝ
  partialSeq_def : partialSeq = ex722PartialFun
  support_finite : ∀ n, (partialSupport n).Finite
  support_subset_unitInterval : ∀ n, partialSupport n ⊆ Set.Icc (0 : ℝ) 1
  continuous_off_support : ∀ n {x}, x ∉ partialSupport n → ContinuousAt (partialSeq n) x
  integral_unitInterval_zero : ∀ n, ∫ x in Set.Icc (0 : ℝ) 1, partialSeq n x ∂volume = 0
  limitFun : ℝ → ℝ
  limitFun_def : limitFun = ex722LimitFun
  pointwise_tendsto : ∀ x, Tendsto (fun n => partialSeq n x) atTop (nhds (limitFun x))
  rational_value : ∀ {q : ℚ}, (q : ℝ) ∈ Set.Icc (0 : ℝ) 1 → limitFun (q : ℝ) = 1
  irrational_value : ∀ {x : ℝ}, Irrational x → limitFun x = 0
  hits_one_on_every_open_subinterval :
    ∀ {a b : ℝ}, 0 ≤ a → a < b → b ≤ 1 → ∃ x ∈ Set.Ioo a b, limitFun x = 1
  hits_zero_on_every_open_subinterval :
    ∀ {a b : ℝ}, 0 ≤ a → a < b → b ≤ 1 → ∃ x ∈ Set.Ioo a b, limitFun x = 0

noncomputable def ex_7_2_2 : LimitOfRiemannIntegrableFunctionsCounterexample where
  ratEnum := ex722Rat
  ratEnum_def := rfl
  ratEnum_injective := ex722Rat_injective
  ratEnum_surjective := ex722Rat_surjective
  partialSupport := ex722PartialSupport
  partialSupport_def := rfl
  partialSeq := ex722PartialFun
  partialSeq_def := rfl
  support_finite := ex722PartialSupport_finite
  support_subset_unitInterval := ex722PartialSupport_subset_unitInterval
  continuous_off_support := fun n {x} hx => ex722PartialFun_continuousAt_of_notMem n hx
  integral_unitInterval_zero := ex722PartialFun_integral_unitInterval_zero
  limitFun := ex722LimitFun
  limitFun_def := rfl
  pointwise_tendsto := ex722PartialFun_tendsto_limit
  rational_value := fun {_q} hq => ex722LimitFun_eq_one_of_rational hq
  irrational_value := fun {_x} hx => ex722LimitFun_eq_zero_of_irrational hx
  hits_one_on_every_open_subinterval := fun {_a _b} ha hab hb =>
    ex722LimitFun_hits_one_on_every_open_subinterval ha hab hb
  hits_zero_on_every_open_subinterval := fun {_a _b} ha hab hb =>
    ex722LimitFun_hits_zero_on_every_open_subinterval ha hab hb
