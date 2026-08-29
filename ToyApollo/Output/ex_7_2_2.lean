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

abbrev Ex722RiemannIndex := Fin 1

noncomputable def ex722RiemannUnitBox : BoxIntegral.Box Ex722RiemannIndex where
  lower := fun _ => 0
  upper := fun _ => 1
  lower_lt_upper := fun _ => zero_lt_one

def ex722LiftToRiemannBox (f : ℝ → ℝ) : (Ex722RiemannIndex → ℝ) → ℝ :=
  fun x => f (x 0)

noncomputable def ex722RiemannVolume :
    BoxIntegral.BoxAdditiveMap Ex722RiemannIndex (ℝ →L[ℝ] ℝ) ⊤ :=
  (volume : Measure (Ex722RiemannIndex → ℝ)).toBoxAdditive.toSMul

theorem ex722RiemannUnitBox_hasIntegralVertices :
    BoxIntegral.hasIntegralVertices ex722RiemannUnitBox := by
  refine ⟨fun _ => 0, fun _ => 1, ?_, ?_⟩
  · intro i
    simp [ex722RiemannUnitBox]
  · intro i
    simp [ex722RiemannUnitBox]

def ex722LiftedPartialSupport (n : ℕ) : Set (Ex722RiemannIndex → ℝ) :=
  {x | x 0 ∈ ex722PartialSupport n}

theorem ex722LiftedPartialSupport_finite (n : ℕ) :
    (ex722LiftedPartialSupport n).Finite := by
  have hEval : Function.Injective (fun x : Ex722RiemannIndex → ℝ => x 0) := by
    intro x y hxy
    funext i
    fin_cases i
    exact hxy
  exact (ex722PartialSupport_finite n).preimage hEval.injOn

theorem ex722LiftedPartialSupport_measure_zero (n : ℕ) :
    (volume : Measure (Ex722RiemannIndex → ℝ)) (ex722LiftedPartialSupport n) = 0 := by
  exact (ex722LiftedPartialSupport_finite n).measure_zero volume

theorem ex722LiftedPartialFun_ae_eq_zero (n : ℕ) :
    ex722LiftToRiemannBox (ex722PartialFun n) =ᵐ[
      (volume : Measure (Ex722RiemannIndex → ℝ))] fun _ => 0 := by
  have hzero : ∀ᵐ x ∂(volume : Measure (Ex722RiemannIndex → ℝ)),
      ex722LiftToRiemannBox (ex722PartialFun n) x = 0 := by
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_ (ex722LiftedPartialSupport_measure_zero n)
    intro x hx
    by_contra hxSupport
    apply hx
    exact ex722PartialFun_eq_zero_of_notMem n hxSupport
  filter_upwards [hzero] with x hx
  exact hx

theorem ex722LiftedPartialFun_ae_continuous (n : ℕ) :
    ∀ᵐ x ∂(volume : Measure (Ex722RiemannIndex → ℝ)),
      ContinuousAt (ex722LiftToRiemannBox (ex722PartialFun n)) x := by
  filter_upwards [compl_mem_ae_iff.mpr (ex722LiftedPartialSupport_measure_zero n)] with x hx
  have hx' : x 0 ∉ ex722PartialSupport n := by
    simpa [ex722LiftedPartialSupport] using hx
  have hscalar : ContinuousAt (ex722PartialFun n) (x 0) :=
    ex722PartialFun_continuousAt_of_notMem n hx'
  have heval : ContinuousAt (fun y : Ex722RiemannIndex → ℝ => y 0) x :=
    continuousAt_apply (0 : Ex722RiemannIndex) x
  change ContinuousAt (fun y : Ex722RiemannIndex → ℝ => ex722PartialFun n (y 0)) x
  exact ContinuousAt.comp' (f := fun y : Ex722RiemannIndex → ℝ => y 0) hscalar heval

theorem ex722LiftedPartialFun_bounded (n : ℕ) :
    ∃ C : ℝ, ∀ x ∈ BoxIntegral.Box.Icc ex722RiemannUnitBox,
      ‖ex722LiftToRiemannBox (ex722PartialFun n) x‖ ≤ C := by
  refine ⟨n, ?_⟩
  intro x hx
  rw [ex722LiftToRiemannBox, ex722PartialFun]
  calc
    ‖∑ k ∈ Finset.range n,
        (({ex722RatReal k} : Set ℝ).indicator (fun _ : ℝ => (1 : ℝ))) (x 0)‖
        ≤ ∑ k ∈ Finset.range n,
            ‖(({ex722RatReal k} : Set ℝ).indicator (fun _ : ℝ => (1 : ℝ))) (x 0)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n, (1 : ℝ) := by
      gcongr with k hk
      by_cases hmem : x 0 ∈ ({ex722RatReal k} : Set ℝ)
      · simp [Set.indicator_of_mem hmem]
      · simp [Set.indicator_of_notMem hmem]
    _ = (n : ℝ) := by simp

theorem ex722PartialFun_hasRiemannIntegral_zero (n : ℕ) :
    BoxIntegral.HasIntegral ex722RiemannUnitBox
      BoxIntegral.IntegrationParams.Riemann
      (ex722LiftToRiemannBox (ex722PartialFun n)) ex722RiemannVolume 0 := by
  have hbox :
      BoxIntegral.HasIntegral ex722RiemannUnitBox
        BoxIntegral.IntegrationParams.Riemann
        (ex722LiftToRiemannBox (ex722PartialFun n))
        ((volume : Measure (Ex722RiemannIndex → ℝ)).toBoxAdditive.toSMul)
        (∫ x in (ex722RiemannUnitBox : Set (Ex722RiemannIndex → ℝ)),
          ex722LiftToRiemannBox (ex722PartialFun n) x
          ∂(volume : Measure (Ex722RiemannIndex → ℝ))) :=
    MeasureTheory.AEContinuous.hasBoxIntegral
      (volume : Measure (Ex722RiemannIndex → ℝ))
      (ex722LiftedPartialFun_bounded n)
      (ex722LiftedPartialFun_ae_continuous n)
      BoxIntegral.IntegrationParams.Riemann
  have hzero :
      ∫ x in (ex722RiemannUnitBox : Set (Ex722RiemannIndex → ℝ)),
          ex722LiftToRiemannBox (ex722PartialFun n) x
          ∂(volume : Measure (Ex722RiemannIndex → ℝ)) = 0 := by
    have hae : ex722LiftToRiemannBox (ex722PartialFun n) =ᵐ[
        (volume : Measure (Ex722RiemannIndex → ℝ)).restrict ex722RiemannUnitBox]
        fun _ => 0 :=
      Filter.Eventually.filter_mono
        (ae_mono (Measure.restrict_le_self :
          (volume : Measure (Ex722RiemannIndex → ℝ)).restrict ex722RiemannUnitBox ≤ volume))
        (ex722LiftedPartialFun_ae_eq_zero n)
    calc
      ∫ x in (ex722RiemannUnitBox : Set (Ex722RiemannIndex → ℝ)),
          ex722LiftToRiemannBox (ex722PartialFun n) x
          ∂(volume : Measure (Ex722RiemannIndex → ℝ)) =
          ∫ x in (ex722RiemannUnitBox : Set (Ex722RiemannIndex → ℝ)),
            (0 : ℝ) ∂(volume : Measure (Ex722RiemannIndex → ℝ)) :=
        integral_congr_ae hae
      _ = 0 := by simp
  simpa [ex722RiemannVolume, hzero] using hbox

theorem ex722PartialFun_riemannIntegrable (n : ℕ) :
    BoxIntegral.Integrable ex722RiemannUnitBox
      BoxIntegral.IntegrationParams.Riemann
      (ex722LiftToRiemannBox (ex722PartialFun n)) ex722RiemannVolume :=
  (ex722PartialFun_hasRiemannIntegral_zero n).integrable

noncomputable def ex722IrrationalTag
    (J : BoxIntegral.Box Ex722RiemannIndex) : Ex722RiemannIndex → ℝ :=
  fun _ => Classical.choose (exists_irrational_btwn (J.lower_lt_upper 0))

theorem ex722IrrationalTag_irrational (J : BoxIntegral.Box Ex722RiemannIndex) :
    Irrational (ex722IrrationalTag J 0) := by
  exact (Classical.choose_spec (exists_irrational_btwn (J.lower_lt_upper 0))).1

theorem ex722IrrationalTag_mem_Icc (J : BoxIntegral.Box Ex722RiemannIndex) :
    ex722IrrationalTag J ∈ BoxIntegral.Box.Icc J := by
  change J.lower ≤ ex722IrrationalTag J ∧ ex722IrrationalTag J ≤ J.upper
  constructor <;> intro i
  · have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact (Classical.choose_spec (exists_irrational_btwn (J.lower_lt_upper 0))).2.1.le
  · have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact (Classical.choose_spec (exists_irrational_btwn (J.lower_lt_upper 0))).2.2.le

noncomputable def ex722IrrationalRetag
    (π : BoxIntegral.TaggedPrepartition ex722RiemannUnitBox) :
    BoxIntegral.TaggedPrepartition ex722RiemannUnitBox := by
  classical
  exact
    { toPrepartition := π.toPrepartition
      tag J := if hJ : J ∈ π then ex722IrrationalTag J else π.tag J
      tag_mem_Icc J := by
        by_cases hJ : J ∈ π
        · rw [dif_pos hJ]
          exact BoxIntegral.Box.le_iff_Icc.1 (π.le_of_mem' J hJ)
            (ex722IrrationalTag_mem_Icc J)
        · rw [dif_neg hJ]
          exact π.tag_mem_Icc J }

@[simp] theorem ex722IrrationalRetag_mem
    {π : BoxIntegral.TaggedPrepartition ex722RiemannUnitBox}
    {J : BoxIntegral.Box Ex722RiemannIndex} :
    J ∈ ex722IrrationalRetag π ↔ J ∈ π := Iff.rfl

theorem ex722IrrationalRetag_tag_of_mem
    {π : BoxIntegral.TaggedPrepartition ex722RiemannUnitBox}
    {J : BoxIntegral.Box Ex722RiemannIndex} (hJ : J ∈ π) :
    (ex722IrrationalRetag π).tag J = ex722IrrationalTag J := by
  classical
  simp [ex722IrrationalRetag, hJ]

theorem ex722IrrationalRetag_isPartition
    {π : BoxIntegral.TaggedPrepartition ex722RiemannUnitBox}
    (hπ : π.IsPartition) : (ex722IrrationalRetag π).IsPartition := hπ

theorem ex722IrrationalRetag_isHenstock
    (π : BoxIntegral.TaggedPrepartition ex722RiemannUnitBox) :
    (ex722IrrationalRetag π).IsHenstock := by
  intro J hJ
  have hJ' : J ∈ π := hJ
  rw [ex722IrrationalRetag_tag_of_mem (π := π) hJ']
  exact ex722IrrationalTag_mem_Icc J

theorem ex722RiemannVolume_unit_one :
    ex722RiemannVolume ex722RiemannUnitBox 1 = (1 : ℝ) := by
  rw [ex722RiemannVolume, BoxIntegral.BoxAdditiveMap.toSMul_apply]
  rw [smul_eq_mul, mul_one]
  change (volume : Measure (Ex722RiemannIndex → ℝ)).toBoxAdditive
    ex722RiemannUnitBox = 1
  rw [BoxIntegral.Box.volume_apply]
  simp [ex722RiemannUnitBox]

theorem ex722UnitPartition_limit_value_one (N : ℕ) [NeZero N]
    {J : BoxIntegral.Box Ex722RiemannIndex}
    (hJ : J ∈ BoxIntegral.unitPartition.prepartition N ex722RiemannUnitBox) :
    ex722LiftToRiemannBox ex722LimitFun
      ((BoxIntegral.unitPartition.prepartition N ex722RiemannUnitBox).tag J) = 1 := by
  rcases BoxIntegral.unitPartition.mem_prepartition_iff.mp hJ with ⟨ν, hν, rfl⟩
  rw [BoxIntegral.unitPartition.prepartition_tag N hν]
  let q : ℚ := ((ν 0 + 1 : ℤ) : ℚ) / (N : ℚ)
  have hqcast : (q : ℝ) = BoxIntegral.unitPartition.tag N ν 0 := by
    simp [q, BoxIntegral.unitPartition.tag_apply]
  have htag :=
    (BoxIntegral.unitPartition.prepartition N ex722RiemannUnitBox).tag_mem_Icc
      (BoxIntegral.unitPartition.box N ν)
  have hscalar : BoxIntegral.unitPartition.tag N ν 0 ∈ Set.Icc (0 : ℝ) 1 := by
    rw [BoxIntegral.unitPartition.prepartition_tag N hν] at htag
    exact ⟨by simpa [ex722RiemannUnitBox] using htag.1 0,
      by simpa [ex722RiemannUnitBox] using htag.2 0⟩
  rw [← hqcast] at hscalar
  change ex722LimitFun (BoxIntegral.unitPartition.tag N ν 0) = 1
  rw [← hqcast]
  exact ex722LimitFun_eq_one_of_rational hscalar

theorem ex722IrrationalRetag_limit_value_zero
    (π : BoxIntegral.TaggedPrepartition ex722RiemannUnitBox)
    {J : BoxIntegral.Box Ex722RiemannIndex} (hJ : J ∈ π) :
    ex722LiftToRiemannBox ex722LimitFun ((ex722IrrationalRetag π).tag J) = 0 := by
  rw [ex722IrrationalRetag_tag_of_mem (π := π) hJ]
  exact ex722LimitFun_eq_zero_of_irrational (ex722IrrationalTag_irrational J)

theorem ex722UnitPartition_integralSum_one (N : ℕ) [NeZero N] :
    BoxIntegral.integralSum (ex722LiftToRiemannBox ex722LimitFun)
      ex722RiemannVolume
      (BoxIntegral.unitPartition.prepartition N ex722RiemannUnitBox) = 1 := by
  let π := BoxIntegral.unitPartition.prepartition N ex722RiemannUnitBox
  have hπ : π.IsPartition :=
    BoxIntegral.unitPartition.prepartition_isPartition N
      ex722RiemannUnitBox_hasIntegralVertices
  calc
    BoxIntegral.integralSum (ex722LiftToRiemannBox ex722LimitFun)
        ex722RiemannVolume π =
        ∑ J ∈ π.boxes, ex722RiemannVolume J 1 := by
      rw [BoxIntegral.integralSum]
      exact Finset.sum_congr rfl fun J hJ => by
        rw [ex722UnitPartition_limit_value_one N hJ]
    _ = ex722RiemannVolume ex722RiemannUnitBox 1 := by
      exact
        (ex722RiemannVolume.map
          ⟨⟨fun g : ℝ →L[ℝ] ℝ => g 1, rfl⟩, fun _ _ => rfl⟩).sum_partition_boxes
            le_top hπ
    _ = 1 := ex722RiemannVolume_unit_one

theorem ex722IrrationalRetag_integralSum_zero
    (π : BoxIntegral.TaggedPrepartition ex722RiemannUnitBox) :
    BoxIntegral.integralSum (ex722LiftToRiemannBox ex722LimitFun)
      ex722RiemannVolume (ex722IrrationalRetag π) = 0 := by
  rw [BoxIntegral.integralSum]
  apply Finset.sum_eq_zero
  intro J hJ
  have hJ' : J ∈ π := hJ
  rw [ex722IrrationalRetag_limit_value_zero π hJ']
  exact map_zero (ex722RiemannVolume J)

theorem ex722IrrationalUnitPartition_isSubordinate (N : ℕ) [NeZero N]
    {r : (Ex722RiemannIndex → ℝ) → Set.Ioi (0 : ℝ)}
    (hr : ∀ x, r x = r 0) (hN : 1 / (N : ℝ) ≤ (r 0 : ℝ)) :
    (ex722IrrationalRetag
      (BoxIntegral.unitPartition.prepartition N ex722RiemannUnitBox)).IsSubordinate r := by
  let π := BoxIntegral.unitPartition.prepartition N ex722RiemannUnitBox
  intro J hJ x hx
  have hJ' : J ∈ π := hJ
  rcases BoxIntegral.unitPartition.mem_prepartition_iff.mp hJ' with ⟨ν, hν, hνJ⟩
  have htag : (ex722IrrationalRetag π).tag J ∈ BoxIntegral.Box.Icc J :=
    ex722IrrationalRetag_isHenstock π J hJ
  change dist x ((ex722IrrationalRetag π).tag J) ≤ (r ((ex722IrrationalRetag π).tag J) : ℝ)
  calc
    dist x ((ex722IrrationalRetag π).tag J) ≤ Metric.diam (BoxIntegral.Box.Icc J) :=
      Metric.dist_le_diam_of_mem (BoxIntegral.Box.isBounded_Icc J) hx htag
    _ ≤ 1 / (N : ℝ) := by
      rw [← hνJ]
      exact BoxIntegral.unitPartition.diam_boxIcc N ν
    _ ≤ (r 0 : ℝ) := hN
    _ = (r ((ex722IrrationalRetag π).tag J) : ℝ) := by
      exact congrArg Subtype.val (hr _).symm

theorem ex722LimitFun_not_riemannIntegrable :
    ¬ BoxIntegral.Integrable ex722RiemannUnitBox
      BoxIntegral.IntegrationParams.Riemann
      (ex722LiftToRiemannBox ex722LimitFun) ex722RiemannVolume := by
  intro hIntegrable
  obtain ⟨r, hrCond, hCauchy⟩ :=
    (BoxIntegral.integrable_iff_cauchy_basis.mp hIntegrable)
      (1 / 2 : ℝ) (by norm_num)
  let N : ℕ := ⌈(r 0 0 : ℝ)⁻¹⌉₊
  haveI : NeZero N :=
    ⟨Nat.ne_zero_iff_zero_lt.mpr
      (Nat.ceil_pos.mpr (inv_pos.mpr (r 0 0).prop))⟩
  have hN : 1 / (N : ℝ) ≤ (r 0 0 : ℝ) := by
    rw [one_div, inv_le_comm₀ (mod_cast (Nat.pos_of_neZero N)) (r 0 0).prop]
    exact Nat.le_ceil _
  let π := BoxIntegral.unitPartition.prepartition N ex722RiemannUnitBox
  let πIrr := ex722IrrationalRetag π
  have hπ : π.IsPartition :=
    BoxIntegral.unitPartition.prepartition_isPartition N
      ex722RiemannUnitBox_hasIntegralVertices
  have hπIrr : πIrr.IsPartition := ex722IrrationalRetag_isPartition hπ
  have hsub : π.IsSubordinate (r 0) := by
    rw [show r 0 = fun _ => r 0 0 from funext_iff.mpr (hrCond 0 rfl)]
    exact BoxIntegral.unitPartition.prepartition_isSubordinate N
      ex722RiemannUnitBox (r 0 0).prop hN
  have hsubIrr : πIrr.IsSubordinate (r 0) := by
    exact ex722IrrationalUnitPartition_isSubordinate N (hrCond 0 rfl) hN
  have hbase : BoxIntegral.IntegrationParams.Riemann.MemBaseSet
      ex722RiemannUnitBox 0 (r 0) π := by
    refine ⟨hsub, fun _ => BoxIntegral.unitPartition.prepartition_isHenstock N
      ex722RiemannUnitBox, fun h => ?_, fun h => ?_⟩
    · simp only [BoxIntegral.IntegrationParams.Riemann, Bool.false_eq_true] at h
    · simp only [BoxIntegral.IntegrationParams.Riemann, Bool.false_eq_true] at h
  have hbaseIrr : BoxIntegral.IntegrationParams.Riemann.MemBaseSet
      ex722RiemannUnitBox 0 (r 0) πIrr := by
    refine ⟨hsubIrr, fun _ => ex722IrrationalRetag_isHenstock π,
      fun h => ?_, fun h => ?_⟩
    · simp only [BoxIntegral.IntegrationParams.Riemann, Bool.false_eq_true] at h
    · simp only [BoxIntegral.IntegrationParams.Riemann, Bool.false_eq_true] at h
  have hdist := hCauchy 0 0 π πIrr hbase hπ hbaseIrr hπIrr
  have : dist (1 : ℝ) 0 ≤ (1 / 2 : ℝ) := by
    simpa only [π, πIrr, ex722UnitPartition_integralSum_one,
      ex722IrrationalRetag_integralSum_zero] using hdist
  norm_num [Real.dist_eq] at this

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
  partial_riemann_integral_zero : ∀ n,
    BoxIntegral.HasIntegral ex722RiemannUnitBox BoxIntegral.IntegrationParams.Riemann
      (ex722LiftToRiemannBox (partialSeq n)) ex722RiemannVolume 0
  partial_riemann_integrable : ∀ n,
    BoxIntegral.Integrable ex722RiemannUnitBox BoxIntegral.IntegrationParams.Riemann
      (ex722LiftToRiemannBox (partialSeq n)) ex722RiemannVolume
  limitFun : ℝ → ℝ
  limitFun_def : limitFun = ex722LimitFun
  pointwise_tendsto : ∀ x, Tendsto (fun n => partialSeq n x) atTop (nhds (limitFun x))
  limit_not_riemann_integrable :
    ¬ BoxIntegral.Integrable ex722RiemannUnitBox BoxIntegral.IntegrationParams.Riemann
      (ex722LiftToRiemannBox limitFun) ex722RiemannVolume
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
  partial_riemann_integral_zero := ex722PartialFun_hasRiemannIntegral_zero
  partial_riemann_integrable := ex722PartialFun_riemannIntegrable
  limitFun := ex722LimitFun
  limitFun_def := rfl
  pointwise_tendsto := ex722PartialFun_tendsto_limit
  limit_not_riemann_integrable := ex722LimitFun_not_riemannIntegrable
  rational_value := fun {_q} hq => ex722LimitFun_eq_one_of_rational hq
  irrational_value := fun {_x} hx => ex722LimitFun_eq_zero_of_irrational hx
  hits_one_on_every_open_subinterval := fun {_a _b} ha hab hb =>
    ex722LimitFun_hits_one_on_every_open_subinterval ha hab hb
  hits_zero_on_every_open_subinterval := fun {_a _b} ha hab hb =>
    ex722LimitFun_hits_zero_on_every_open_subinterval ha hab hb
