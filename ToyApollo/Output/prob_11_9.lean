import Mathlib
import ToyApollo.Output.def_10_3
import ToyApollo.Output.thm_10_5
import ToyApollo.Output.thm_11_2

/-
TASK ID: prob_11_9
TYPE: Problem
SOURCE PLAN: chapter11-problems
TASK CONTENT:
\textbf{11.9.} Consider the experiment of throwing k distinct balls into n distinct boxes.

Assume the locations of the balls are independent and uniformly chosen among

{1, 2,...,n }We consider an asymptotic scenario in which k and n increase

simultaneously with k/n \to a, for some positive constant aLet Xn denote the

number of empty boxes when the number of boxes is n Prove that X n/n \to e-a in

quadratic mean, and hence in probability as n \to\infty .
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory

noncomputable section

open scoped BigOperators

/-- The proportion `X_n / n` of empty boxes, written with an explicit sequence
of box counts so that the Lean indexing need not identify `n = 0` with the
textbook's first positive number of boxes. -/
noncomputable def prob_11_9_emptyBoxRatio {Ω : Type*}
    (boxes : ℕ → ℕ) (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n ω => X n ω / (boxes n : ℝ)

/-- For a concrete finite balls-in-boxes experiment, the event that box `i` is
empty in experiment `n`. -/
def prob_11_9_oneBoxEmptyEvent {Ω : Type*} (boxes k : ℕ → ℕ)
    (locations : ∀ n : ℕ, Ω → Fin (k n) → Fin (boxes n))
    (n : ℕ) (i : Fin (boxes n)) : Set Ω :=
  {ω | ∀ b : Fin (k n), locations n ω b ≠ i}

/-- The event that two distinct boxes are both empty in experiment `n`. -/
def prob_11_9_twoBoxEmptyEvent {Ω : Type*} (boxes k : ℕ → ℕ)
    (locations : ∀ n : ℕ, Ω → Fin (k n) → Fin (boxes n))
    (n : ℕ) (i j : Fin (boxes n)) : Set Ω :=
  {ω | (∀ b : Fin (k n), locations n ω b ≠ i) ∧
      (∀ b : Fin (k n), locations n ω b ≠ j)}

/-- The concrete empty-box count induced by finite ball locations. -/
noncomputable def prob_11_9_emptyBoxCountFromLocations {Ω : Type*}
    (boxes k : ℕ → ℕ)
    (locations : ∀ n : ℕ, Ω → Fin (k n) → Fin (boxes n))
    (n : ℕ) (ω : Ω) : ℕ := by
  classical
  exact (Finset.univ.filter
    (fun i : Fin (boxes n) => ∀ b : Fin (k n), locations n ω b ≠ i)).card

/-- The canonical finite sample space for experiment `n`: each ball is assigned
one of the boxes.  The uniform measure on this function space is the formal
source-facing version of independently and uniformly chosen ball locations. -/
abbrev prob_11_9_locationSpace (boxes k : ℕ → ℕ) (n : ℕ) :=
  Fin (k n) → Fin (boxes n)

instance prob_11_9_instMeasurableSpaceLocationSpace
    (boxes k : ℕ → ℕ) (n : ℕ) :
    MeasurableSpace (prob_11_9_locationSpace boxes k n) := ⊤

lemma prob_11_9_nonempty_locationSpace_of_pos
    (boxes k : ℕ → ℕ) (n : ℕ) (hbox : 0 < boxes n) :
    Nonempty (prob_11_9_locationSpace boxes k n) :=
  ⟨fun _ => ⟨0, hbox⟩⟩

noncomputable def prob_11_9_locationMeasure
    (boxes k : ℕ → ℕ) (n : ℕ) :
    Measure (prob_11_9_locationSpace boxes k n) := by
  classical
  by_cases h : Nonempty (prob_11_9_locationSpace boxes k n)
  · letI := h
    exact (PMF.uniformOfFintype (prob_11_9_locationSpace boxes k n)).toMeasure
  · exact 0

instance prob_11_9_instIsFiniteMeasureLocationMeasure
    (boxes k : ℕ → ℕ) (n : ℕ) :
    IsFiniteMeasure (prob_11_9_locationMeasure boxes k n) := by
  classical
  by_cases h : Nonempty (prob_11_9_locationSpace boxes k n)
  · rw [prob_11_9_locationMeasure, dif_pos h]
    infer_instance
  · rw [prob_11_9_locationMeasure, dif_neg h]
    infer_instance

def prob_11_9_oneBoxEmptyAssignment
    (boxes k : ℕ → ℕ) (n : ℕ) (i : Fin (boxes n)) :
    Set (prob_11_9_locationSpace boxes k n) :=
  {ω | ∀ b : Fin (k n), ω b ≠ i}

def prob_11_9_twoBoxEmptyAssignment
    (boxes k : ℕ → ℕ) (n : ℕ) (i j : Fin (boxes n)) :
    Set (prob_11_9_locationSpace boxes k n) :=
  {ω | (∀ b : Fin (k n), ω b ≠ i) ∧
      (∀ b : Fin (k n), ω b ≠ j)}

theorem prob_11_9_uniformOfFintype_toMeasure_real
    {α : Type*} [MeasurableSpace α] [Fintype α] [Nonempty α]
    [DecidableEq α] [MeasurableSingletonClass α]
    (A : Set α) [DecidablePred (fun x => x ∈ A)] (hA : MeasurableSet A) :
    (PMF.uniformOfFintype α).toMeasure.real A =
      (Fintype.card {x : α // x ∈ A} : ℝ) / (Fintype.card α : ℝ) := by
  rw [← integral_indicator_one (μ := (PMF.uniformOfFintype α).toMeasure)
    (s := A) hA]
  rw [MeasureTheory.integral_fintype]
  · simp [PMF.uniformOfFintype_apply, Measure.real_def]
    rw [← Finset.mul_sum]
    have hsum :
        (∑ x : α, A.indicator (fun _ : α => (1 : ℝ)) x) =
          (Fintype.card {x : α // x ∈ A} : ℝ) := by
      calc
        (∑ x : α, A.indicator (fun _ : α => (1 : ℝ)) x) =
            ∑ x : α, (if x ∈ A then (1 : ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro x _hx
              rw [Set.indicator_apply]
        _ = ((Finset.univ.filter (fun x : α => x ∈ A)).card : ℝ) := by
          rw [Finset.sum_boole]
        _ = (Fintype.card {x : α // x ∈ A} : ℝ) := by
          rw [Fintype.card_subtype]
    change ((Fintype.card α : ℝ)⁻¹) *
        (∑ x : α, A.indicator (fun _ : α => (1 : ℝ)) x) =
      (Fintype.card {x : α // x ∈ A} : ℝ) / (Fintype.card α : ℝ)
    rw [hsum]
    field_simp [show (Fintype.card α : ℝ) ≠ 0 by
      exact_mod_cast Fintype.card_ne_zero]
  · exact Integrable.of_finite (f := A.indicator (fun _ : α => (1 : ℝ)))

lemma prob_11_9_card_binsExcept (m : ℕ) (i : Fin m) :
    Fintype.card {x : Fin m // x ≠ i} = m - 1 := by
  classical
  rw [Fintype.card_subtype]
  rw [Finset.filter_ne']
  have himem : i ∈ (Finset.univ : Finset (Fin m)) := by simp
  rw [Finset.card_erase_of_mem himem]
  simp [Fintype.card_fin]

lemma prob_11_9_card_binsExceptTwo
    (m : ℕ) (i j : Fin m) (hij : i ≠ j) :
    Fintype.card {x : Fin m // x ≠ i ∧ x ≠ j} = m - 2 := by
  classical
  rw [Fintype.card_subtype]
  have hfilter :
      (Finset.univ.filter (fun x : Fin m => x ≠ i ∧ x ≠ j)) =
        (Finset.univ.erase i).erase j := by
    ext x
    simp [and_comm, eq_comm]
  rw [hfilter]
  have hjmem : j ∈ (Finset.univ.erase i : Finset (Fin m)) := by
    simp [hij.symm]
  rw [Finset.card_erase_of_mem hjmem]
  have himem : i ∈ (Finset.univ : Finset (Fin m)) := by simp
  rw [Finset.card_erase_of_mem himem]
  simp [Fintype.card_fin]
  omega

theorem prob_11_9_locationMeasure_real_oneBoxEmptyAssignment
    (boxes k : ℕ → ℕ) {n : ℕ} (hbox : 0 < boxes n)
    (i : Fin (boxes n)) :
    (prob_11_9_locationMeasure boxes k n).real
        (prob_11_9_oneBoxEmptyAssignment boxes k n i) =
      (((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n) := by
  classical
  have hnon : Nonempty (prob_11_9_locationSpace boxes k n) :=
    prob_11_9_nonempty_locationSpace_of_pos boxes k n hbox
  rw [prob_11_9_locationMeasure, dif_pos hnon]
  rw [prob_11_9_uniformOfFintype_toMeasure_real
    (A := prob_11_9_oneBoxEmptyAssignment boxes k n i) (by trivial)]
  have hcard :
      Fintype.card
          {ω : prob_11_9_locationSpace boxes k n //
            ω ∈ prob_11_9_oneBoxEmptyAssignment boxes k n i} =
        (boxes n - 1) ^ (k n) := by
    let e :
        {ω : prob_11_9_locationSpace boxes k n //
          ω ∈ prob_11_9_oneBoxEmptyAssignment boxes k n i} ≃
          (Fin (k n) → {x : Fin (boxes n) // x ≠ i}) :=
    { toFun := fun ω b => ⟨ω.1 b, by exact ω.2 b⟩
      invFun := fun f => ⟨fun b => (f b).1, by intro b; exact (f b).2⟩
      left_inv := by intro ω; ext b; rfl
      right_inv := by intro f; ext b; rfl }
    calc
      Fintype.card
          {ω : prob_11_9_locationSpace boxes k n //
            ω ∈ prob_11_9_oneBoxEmptyAssignment boxes k n i} =
          Fintype.card (Fin (k n) → {x : Fin (boxes n) // x ≠ i}) :=
            Fintype.card_congr e
      _ = (boxes n - 1) ^ (k n) := by
        rw [Fintype.card_fun, prob_11_9_card_binsExcept, Fintype.card_fin]
  have hden :
      Fintype.card (prob_11_9_locationSpace boxes k n) =
        (boxes n) ^ (k n) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  rw [hcard, hden]
  norm_num [Nat.cast_pow]
  rw [div_pow]

theorem prob_11_9_locationMeasure_real_twoBoxEmptyAssignment
    (boxes k : ℕ → ℕ) {n : ℕ} (hbox : 0 < boxes n)
    (i j : Fin (boxes n)) (hij : i ≠ j) :
    (prob_11_9_locationMeasure boxes k n).real
        (prob_11_9_twoBoxEmptyAssignment boxes k n i j) =
      (((boxes n - 2 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n) := by
  classical
  have hnon : Nonempty (prob_11_9_locationSpace boxes k n) :=
    prob_11_9_nonempty_locationSpace_of_pos boxes k n hbox
  rw [prob_11_9_locationMeasure, dif_pos hnon]
  rw [prob_11_9_uniformOfFintype_toMeasure_real
    (A := prob_11_9_twoBoxEmptyAssignment boxes k n i j) (by trivial)]
  have hcard :
      Fintype.card
          {ω : prob_11_9_locationSpace boxes k n //
            ω ∈ prob_11_9_twoBoxEmptyAssignment boxes k n i j} =
        (boxes n - 2) ^ (k n) := by
    let e :
        {ω : prob_11_9_locationSpace boxes k n //
          ω ∈ prob_11_9_twoBoxEmptyAssignment boxes k n i j} ≃
          (Fin (k n) → {x : Fin (boxes n) // x ≠ i ∧ x ≠ j}) :=
    { toFun := fun ω b => ⟨ω.1 b, by exact ⟨ω.2.1 b, ω.2.2 b⟩⟩
      invFun := fun f =>
        ⟨fun b => (f b).1,
          by exact ⟨fun b => (f b).2.1, fun b => (f b).2.2⟩⟩
      left_inv := by intro ω; ext b; rfl
      right_inv := by intro f; ext b; rfl }
    calc
      Fintype.card
          {ω : prob_11_9_locationSpace boxes k n //
            ω ∈ prob_11_9_twoBoxEmptyAssignment boxes k n i j} =
          Fintype.card (Fin (k n) →
            {x : Fin (boxes n) // x ≠ i ∧ x ≠ j}) :=
            Fintype.card_congr e
      _ = (boxes n - 2) ^ (k n) := by
        rw [Fintype.card_fun, prob_11_9_card_binsExceptTwo _ i j hij,
          Fintype.card_fin]
  have hden :
      Fintype.card (prob_11_9_locationSpace boxes k n) =
        (boxes n) ^ (k n) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  rw [hcard, hden]
  norm_num [Nat.cast_pow]
  rw [div_pow]

/-- Source-facing finite independent uniform occupancy model for Problem 11.9.
It ties the public process `X` to concrete ball locations.  The final field
states that, for each `n`, the vector of all ball locations is uniformly
distributed on the finite function space `Fin (k n) → Fin (boxes n)`, which is
the finite-product form of independent uniform ball locations. -/
def prob_11_9_finiteIndependentUniformEmptyBoxModel {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (boxes k : ℕ → ℕ)
    (X : ℕ → Ω → ℝ) : Prop :=
  ∃ locations : ∀ n : ℕ, Ω → Fin (k n) → Fin (boxes n),
    (∀ n ω,
      X n ω = (prob_11_9_emptyBoxCountFromLocations boxes k locations n ω : ℝ)) ∧
    (∀ n (i : Fin (boxes n)),
      MeasurableSet (prob_11_9_oneBoxEmptyEvent boxes k locations n i)) ∧
    (∀ n (i j : Fin (boxes n)),
      MeasurableSet (prob_11_9_twoBoxEmptyEvent boxes k locations n i j)) ∧
    (∀ n : ℕ,
      MeasurePreserving (locations n) P (prob_11_9_locationMeasure boxes k n))

theorem prob_11_9_oneBoxEmptyEvent_probability {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (boxes k : ℕ → ℕ)
    (locations : ∀ n : ℕ, Ω → Fin (k n) → Fin (boxes n))
    {n : ℕ} (hbox : 0 < boxes n) (i : Fin (boxes n))
    (hUniform :
      MeasurePreserving (locations n) P (prob_11_9_locationMeasure boxes k n)) :
    P.real (prob_11_9_oneBoxEmptyEvent boxes k locations n i) =
      (((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n) := by
  classical
  let A := prob_11_9_oneBoxEmptyAssignment boxes k n i
  have hMeasA : MeasurableSet A := by trivial
  have hmeasure := hUniform.measure_preimage hMeasA.nullMeasurableSet
  have hreal :
      P.real ((locations n) ⁻¹' A) =
        (prob_11_9_locationMeasure boxes k n).real A := by
    rw [Measure.real_def, Measure.real_def, hmeasure]
  have hformula :=
    prob_11_9_locationMeasure_real_oneBoxEmptyAssignment boxes k hbox i
  simpa [A, prob_11_9_oneBoxEmptyEvent, prob_11_9_oneBoxEmptyAssignment]
    using hreal.trans hformula

theorem prob_11_9_twoBoxEmptyEvent_probability {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (boxes k : ℕ → ℕ)
    (locations : ∀ n : ℕ, Ω → Fin (k n) → Fin (boxes n))
    {n : ℕ} (hbox : 0 < boxes n) (i j : Fin (boxes n)) (hij : i ≠ j)
    (hUniform :
      MeasurePreserving (locations n) P (prob_11_9_locationMeasure boxes k n)) :
    P.real (prob_11_9_twoBoxEmptyEvent boxes k locations n i j) =
      (((boxes n - 2 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n) := by
  classical
  let A := prob_11_9_twoBoxEmptyAssignment boxes k n i j
  have hMeasA : MeasurableSet A := by trivial
  have hmeasure := hUniform.measure_preimage hMeasA.nullMeasurableSet
  have hreal :
      P.real ((locations n) ⁻¹' A) =
        (prob_11_9_locationMeasure boxes k n).real A := by
    rw [Measure.real_def, Measure.real_def, hmeasure]
  have hformula :=
    prob_11_9_locationMeasure_real_twoBoxEmptyAssignment boxes k hbox i j hij
  simpa [A, prob_11_9_twoBoxEmptyEvent, prob_11_9_twoBoxEmptyAssignment]
    using hreal.trans hformula

theorem prob_11_9_emptyBoxCount_eq_sum_indicators {Ω : Type*}
    (boxes k : ℕ → ℕ)
    (locations : ∀ n : ℕ, Ω → Fin (k n) → Fin (boxes n))
    (n : ℕ) :
    (fun ω : Ω =>
        (prob_11_9_emptyBoxCountFromLocations boxes k locations n ω : ℝ)) =
      fun ω : Ω =>
        ∑ i : Fin (boxes n),
          (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
            (fun _ : Ω => (1 : ℝ)) ω := by
  classical
  funext ω
  unfold prob_11_9_emptyBoxCountFromLocations prob_11_9_oneBoxEmptyEvent
  change ((Finset.univ.filter
      (fun i : Fin (boxes n) => ∀ b : Fin (k n), locations n ω b ≠ i)).card : ℝ) =
    ∑ i : Fin (boxes n),
      ({ω | ∀ b : Fin (k n), locations n ω b ≠ i}.indicator
        (fun _ : Ω => (1 : ℝ)) ω)
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [← Finset.sum_filter]
  simp

theorem prob_11_9_fin_inner_two_probability_sum {m : ℕ}
    (i : Fin m) (pDiag pOff : ℝ) :
    (∑ j : Fin m, (if i = j then pDiag else pOff)) =
      pDiag + ((m - 1 : ℕ) : ℝ) * pOff := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset (Fin m))) (p := fun j => i = j)
    (f := fun j => if i = j then pDiag else pOff)]
  have hdiag :
      (∑ x with i = x, (if i = x then pDiag else pOff)) = pDiag := by
    have hfilter : (Finset.univ.filter (fun x : Fin m => i = x)) = {i} := by
      ext x
      simp [eq_comm]
    rw [hfilter]
    simp
  have hoff :
      (∑ x with ¬i = x, (if i = x then pDiag else pOff)) =
        ((m - 1 : ℕ) : ℝ) * pOff := by
    have hfilter :
        (Finset.univ.filter (fun x : Fin m => ¬i = x)).card = m - 1 := by
      rw [show
          (Finset.univ.filter (fun x : Fin m => ¬i = x)) =
            Finset.univ.filter (fun x : Fin m => x ≠ i) by
        ext x
        simp [eq_comm]]
      rw [Finset.filter_ne']
      have hi : i ∈ (Finset.univ : Finset (Fin m)) := by simp
      have hcard := Finset.card_erase_of_mem hi
      simp [Fintype.card_fin] at hcard ⊢
    rw [show
        (∑ x with ¬i = x, (if i = x then pDiag else pOff)) =
          ∑ x with ¬i = x, pOff by
      apply Finset.sum_congr rfl
      intro x hx
      simp at hx
      simp [hx]]
    rw [Finset.sum_const]
    simp [hfilter]
  rw [hdiag, hoff]

theorem prob_11_9_fin_double_two_probability_sum {m : ℕ}
    (pDiag pOff : ℝ) :
    (∑ i : Fin m, ∑ j : Fin m, (if i = j then pDiag else pOff)) =
      (m : ℝ) * pDiag + (m : ℝ) * ((m - 1 : ℕ) : ℝ) * pOff := by
  classical
  simp_rw [prob_11_9_fin_inner_two_probability_sum]
  rw [Finset.sum_const]
  simp [Fintype.card_fin]
  ring

theorem prob_11_9_tendsto_one_sub_const_div_pow
    {boxes k : ℕ → ℕ} {a c : ℝ}
    (hc : 0 ≤ c)
    (hboxes : Tendsto (fun n : ℕ => (boxes n : ℝ)) atTop atTop)
    (hratio : Tendsto (fun n : ℕ => (k n : ℝ) / (boxes n : ℝ))
      atTop (nhds a)) :
    Tendsto (fun n : ℕ => (1 - c / (boxes n : ℝ)) ^ k n)
      atTop (nhds (Real.exp (-(c * a)))) := by
  have hlog0 :
      Tendsto
        (fun n : ℕ => (boxes n : ℝ) *
          Real.log (1 + (-c) / (boxes n : ℝ)))
        atTop (nhds (-c)) := by
    simpa [sub_eq_add_neg] using
      (Real.tendsto_mul_log_one_add_div_atTop (-c)).comp hboxes
  have hmul0 := hratio.mul hlog0
  have hmul1 :
      Tendsto
        (fun n : ℕ => (k n : ℝ) *
          Real.log (1 + (-c) / (boxes n : ℝ)))
        atTop (nhds (a * (-c))) := by
    refine hmul0.congr' ?_
    filter_upwards [hboxes.eventually_gt_atTop (0 : ℝ)] with n hbn
    have hbne : (boxes n : ℝ) ≠ 0 := ne_of_gt hbn
    field_simp [hbne]
  have hmul :
      Tendsto
        (fun n : ℕ => (k n : ℝ) *
          Real.log (1 + (-c) / (boxes n : ℝ)))
        atTop (nhds (-(c * a))) := by
    convert hmul1 using 1
    ring
  have hexp :
      Tendsto
        (fun n : ℕ =>
          Real.exp ((k n : ℝ) *
            Real.log (1 + (-c) / (boxes n : ℝ))))
        atTop (nhds (Real.exp (-(c * a)))) :=
    (Real.continuous_exp.tendsto _).comp hmul
  refine hexp.congr' ?_
  filter_upwards [hboxes.eventually_gt_atTop (c + 1)] with n hlarge
  have hposbox : 0 < (boxes n : ℝ) := lt_trans (by linarith : 0 < c + 1) hlarge
  have hbase : 0 < 1 + (-c) / (boxes n : ℝ) := by
    have hdivlt : c / (boxes n : ℝ) < 1 := by
      rw [div_lt_one hposbox]
      linarith
    have hsub : 0 < 1 - c / (boxes n : ℝ) := sub_pos.mpr hdivlt
    convert hsub using 1
    ring
  calc
    Real.exp ((k n : ℝ) * Real.log (1 + (-c) / (boxes n : ℝ)))
        = Real.exp (Real.log (1 + (-c) / (boxes n : ℝ)) * (k n : ℝ)) := by
          ring
    _ = (1 + (-c) / (boxes n : ℝ)) ^ ((k n : ℕ) : ℝ) := by
      rw [Real.rpow_def_of_pos hbase]
    _ = (1 + (-c) / (boxes n : ℝ)) ^ k n := by
      rw [Real.rpow_natCast]
    _ = (1 - c / (boxes n : ℝ)) ^ k n := by
      ring_nf

theorem prob_11_9_oneBoxIndicator_integrable {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (boxes k : ℕ → ℕ)
    (locations : ∀ n : ℕ, Ω → Fin (k n) → Fin (boxes n))
    {n : ℕ} (i : Fin (boxes n))
    (hMeas :
      MeasurableSet (prob_11_9_oneBoxEmptyEvent boxes k locations n i)) :
    Integrable
      (fun ω : Ω =>
        (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
          (fun _ : Ω => (1 : ℝ)) ω) P := by
  rw [integrable_indicator_iff hMeas]
  exact (integrable_const (α := Ω) (μ := P) (1 : ℝ)).integrableOn

theorem prob_11_9_twoBoxIndicator_integrable {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (boxes k : ℕ → ℕ)
    (locations : ∀ n : ℕ, Ω → Fin (k n) → Fin (boxes n))
    {n : ℕ} (i j : Fin (boxes n))
    (hMeas :
      MeasurableSet (prob_11_9_twoBoxEmptyEvent boxes k locations n i j)) :
    Integrable
      (fun ω : Ω =>
        (prob_11_9_twoBoxEmptyEvent boxes k locations n i j).indicator
          (fun _ : Ω => (1 : ℝ)) ω) P := by
  rw [integrable_indicator_iff hMeas]
  exact (integrable_const (α := Ω) (μ := P) (1 : ℝ)).integrableOn

theorem prob_11_9_oneBoxIndicator_integral {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (boxes k : ℕ → ℕ)
    (locations : ∀ n : ℕ, Ω → Fin (k n) → Fin (boxes n))
    {n : ℕ} (i : Fin (boxes n))
    (hMeas :
      MeasurableSet (prob_11_9_oneBoxEmptyEvent boxes k locations n i)) :
    ∫ ω : Ω,
        (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
          (fun _ : Ω => (1 : ℝ)) ω ∂P =
      P.real (prob_11_9_oneBoxEmptyEvent boxes k locations n i) := by
  simpa using
    (MeasureTheory.integral_indicator_one (μ := P)
      (s := prob_11_9_oneBoxEmptyEvent boxes k locations n i) hMeas)

theorem prob_11_9_twoBoxIndicator_integral {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (boxes k : ℕ → ℕ)
    (locations : ∀ n : ℕ, Ω → Fin (k n) → Fin (boxes n))
    {n : ℕ} (i j : Fin (boxes n))
    (hMeas :
      MeasurableSet (prob_11_9_twoBoxEmptyEvent boxes k locations n i j)) :
    ∫ ω : Ω,
        (prob_11_9_twoBoxEmptyEvent boxes k locations n i j).indicator
          (fun _ : Ω => (1 : ℝ)) ω ∂P =
      P.real (prob_11_9_twoBoxEmptyEvent boxes k locations n i j) := by
  simpa using
    (MeasureTheory.integral_indicator_one (μ := P)
      (s := prob_11_9_twoBoxEmptyEvent boxes k locations n i j) hMeas)

theorem prob_11_9_oneBoxIndicator_mul_self {Ω : Type*}
    (boxes k : ℕ → ℕ)
    (locations : ∀ n : ℕ, Ω → Fin (k n) → Fin (boxes n))
    {n : ℕ} (i : Fin (boxes n)) :
    (fun ω : Ω =>
        (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
            (fun _ : Ω => (1 : ℝ)) ω *
          (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
            (fun _ : Ω => (1 : ℝ)) ω) =
      fun ω : Ω =>
        (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
          (fun _ : Ω => (1 : ℝ)) ω := by
  classical
  funext ω
  by_cases hω : ω ∈ prob_11_9_oneBoxEmptyEvent boxes k locations n i
  · simp [Set.indicator, hω]
  · simp [Set.indicator, hω]

theorem prob_11_9_oneBoxIndicator_mul_pair {Ω : Type*}
    (boxes k : ℕ → ℕ)
    (locations : ∀ n : ℕ, Ω → Fin (k n) → Fin (boxes n))
    {n : ℕ} (i j : Fin (boxes n)) :
    (fun ω : Ω =>
        (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
            (fun _ : Ω => (1 : ℝ)) ω *
          (prob_11_9_oneBoxEmptyEvent boxes k locations n j).indicator
            (fun _ : Ω => (1 : ℝ)) ω) =
      fun ω : Ω =>
        (prob_11_9_twoBoxEmptyEvent boxes k locations n i j).indicator
          (fun _ : Ω => (1 : ℝ)) ω := by
  classical
  funext ω
  by_cases hi : ∀ b : Fin (k n), locations n ω b ≠ i
  · by_cases hj : ∀ b : Fin (k n), locations n ω b ≠ j
    · simp [prob_11_9_oneBoxEmptyEvent, prob_11_9_twoBoxEmptyEvent,
        Set.indicator, hi, hj]
    · simp [prob_11_9_oneBoxEmptyEvent, prob_11_9_twoBoxEmptyEvent,
        Set.indicator, hi, hj]
  · by_cases hj : ∀ b : Fin (k n), locations n ω b ≠ j
    · simp [prob_11_9_oneBoxEmptyEvent, prob_11_9_twoBoxEmptyEvent,
        Set.indicator, hi, hj]
    · simp [prob_11_9_oneBoxEmptyEvent, prob_11_9_twoBoxEmptyEvent,
        Set.indicator, hi, hj]

theorem prob_11_9_oneBoxIndicator_product_integral {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (boxes k : ℕ → ℕ)
    (locations : ∀ n : ℕ, Ω → Fin (k n) → Fin (boxes n))
    {n : ℕ} (i j : Fin (boxes n))
    (hOneMeas : ∀ i : Fin (boxes n),
      MeasurableSet (prob_11_9_oneBoxEmptyEvent boxes k locations n i))
    (hTwoMeas : ∀ i j : Fin (boxes n),
      MeasurableSet (prob_11_9_twoBoxEmptyEvent boxes k locations n i j))
    (hOneProb : ∀ i : Fin (boxes n),
      P.real (prob_11_9_oneBoxEmptyEvent boxes k locations n i) =
        (((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n))
    (hTwoProb : ∀ i j : Fin (boxes n), i ≠ j →
      P.real (prob_11_9_twoBoxEmptyEvent boxes k locations n i j) =
        (((boxes n - 2 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)) :
    ∫ ω : Ω,
        (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
            (fun _ : Ω => (1 : ℝ)) ω *
          (prob_11_9_oneBoxEmptyEvent boxes k locations n j).indicator
            (fun _ : Ω => (1 : ℝ)) ω ∂P =
      if i = j then
        (((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)
      else
        (((boxes n - 2 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n) := by
  classical
  by_cases hij : i = j
  · subst j
    rw [prob_11_9_oneBoxIndicator_mul_self]
    simpa [hOneProb i] using
      (prob_11_9_oneBoxIndicator_integral P boxes k locations i (hOneMeas i))
  · rw [if_neg hij]
    rw [prob_11_9_oneBoxIndicator_mul_pair boxes k locations i j]
    simpa [hTwoProb i j hij] using
      (prob_11_9_twoBoxIndicator_integral P boxes k locations i j (hTwoMeas i j))

theorem prob_11_9_emptyBoxRatio_integral_eq {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (boxes k : ℕ → ℕ) (X : ℕ → Ω → ℝ) {n : ℕ}
    (hModel : prob_11_9_finiteIndependentUniformEmptyBoxModel P boxes k X)
    (hbox : 0 < boxes n) :
    ∫ ω : Ω, prob_11_9_emptyBoxRatio boxes X n ω ∂P =
      (((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n) := by
  classical
  rcases hModel with
    ⟨locations, hX, hOneMeas, _hTwoMeas, hUniform⟩
  have hOneProb :
      ∀ i : Fin (boxes n),
        P.real (prob_11_9_oneBoxEmptyEvent boxes k locations n i) =
          (((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n) :=
    fun i => prob_11_9_oneBoxEmptyEvent_probability P boxes k locations
      hbox i (hUniform n)
  let p1 : ℝ := (((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)
  have hYeq :
      (fun ω : Ω => prob_11_9_emptyBoxRatio boxes X n ω) =
        fun ω : Ω =>
          (1 / (boxes n : ℝ)) *
            ∑ i : Fin (boxes n),
              (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
                (fun _ : Ω => (1 : ℝ)) ω := by
    funext ω
    have hcount :=
      congrFun (prob_11_9_emptyBoxCount_eq_sum_indicators boxes k locations n) ω
    calc
      prob_11_9_emptyBoxRatio boxes X n ω =
          X n ω / (boxes n : ℝ) := rfl
      _ =
          (prob_11_9_emptyBoxCountFromLocations boxes k locations n ω : ℝ) /
            (boxes n : ℝ) := by
            rw [hX n ω]
      _ =
          (∑ i : Fin (boxes n),
            (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
              (fun _ : Ω => (1 : ℝ)) ω) / (boxes n : ℝ) := by
            rw [hcount]
      _ =
          (1 / (boxes n : ℝ)) *
            ∑ i : Fin (boxes n),
              (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
                (fun _ : Ω => (1 : ℝ)) ω := by
            ring
  have hInt :
      ∀ i ∈ (Finset.univ : Finset (Fin (boxes n))),
        Integrable
          (fun ω : Ω =>
            (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
              (fun _ : Ω => (1 : ℝ)) ω) P := by
    intro i _hi
    exact prob_11_9_oneBoxIndicator_integrable P boxes k locations i
      (hOneMeas n i)
  have hEach :
      ∀ i : Fin (boxes n),
        ∫ ω : Ω,
            (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
              (fun _ : Ω => (1 : ℝ)) ω ∂P = p1 := by
    intro i
    simpa [p1, hOneProb i] using
      (prob_11_9_oneBoxIndicator_integral P boxes k locations i
        (hOneMeas n i))
  rw [hYeq, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finset_sum Finset.univ hInt]
  calc
    (1 / (boxes n : ℝ)) *
        ∑ i : Fin (boxes n),
          ∫ ω : Ω,
            (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
              (fun _ : Ω => (1 : ℝ)) ω ∂P =
        (1 / (boxes n : ℝ)) * ∑ _i : Fin (boxes n), p1 := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _hi
          exact hEach i
    _ = p1 := by
      have hbne : (boxes n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hbox
      rw [Finset.sum_const]
      simp [Fintype.card_fin, hbne]

theorem prob_11_9_emptyBoxRatio_sq_integral_eq {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (boxes k : ℕ → ℕ) (X : ℕ → Ω → ℝ) {n : ℕ}
    (hModel : prob_11_9_finiteIndependentUniformEmptyBoxModel P boxes k X)
    (hbox : 0 < boxes n) :
    ∫ ω : Ω, (prob_11_9_emptyBoxRatio boxes X n ω) ^ 2 ∂P =
      ((((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)) /
          (boxes n : ℝ) +
        ((((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) *
          ((((boxes n - 2 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n))) := by
  classical
  rcases hModel with
    ⟨locations, hX, hOneMeas, hTwoMeas, hUniform⟩
  have hOneProb :
      ∀ i : Fin (boxes n),
        P.real (prob_11_9_oneBoxEmptyEvent boxes k locations n i) =
          (((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n) :=
    fun i => prob_11_9_oneBoxEmptyEvent_probability P boxes k locations
      hbox i (hUniform n)
  have hTwoProb :
      ∀ i j : Fin (boxes n), i ≠ j →
        P.real (prob_11_9_twoBoxEmptyEvent boxes k locations n i j) =
          (((boxes n - 2 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n) :=
    fun i j hij => prob_11_9_twoBoxEmptyEvent_probability P boxes k locations
      hbox i j hij (hUniform n)
  let p1 : ℝ := (((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)
  let p2 : ℝ := (((boxes n - 2 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)
  let b : ℝ := (boxes n : ℝ)
  have hbne : b ≠ 0 := by
    dsimp [b]
    exact_mod_cast ne_of_gt hbox
  have hYsqeq :
      (fun ω : Ω => (prob_11_9_emptyBoxRatio boxes X n ω) ^ 2) =
        fun ω : Ω =>
          (1 / b ^ 2) *
            ∑ i : Fin (boxes n),
              ∑ j : Fin (boxes n),
                (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
                    (fun _ : Ω => (1 : ℝ)) ω *
                  (prob_11_9_oneBoxEmptyEvent boxes k locations n j).indicator
                    (fun _ : Ω => (1 : ℝ)) ω := by
    funext ω
    have hcount :=
      congrFun (prob_11_9_emptyBoxCount_eq_sum_indicators boxes k locations n) ω
    let S : ℝ :=
      ∑ i : Fin (boxes n),
        (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
          (fun _ : Ω => (1 : ℝ)) ω
    have hsumprod :
        S * S =
          ∑ i : Fin (boxes n),
            ∑ j : Fin (boxes n),
              (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
                  (fun _ : Ω => (1 : ℝ)) ω *
                (prob_11_9_oneBoxEmptyEvent boxes k locations n j).indicator
                  (fun _ : Ω => (1 : ℝ)) ω := by
      dsimp [S]
      simpa using
        (Finset.sum_mul_sum (Finset.univ : Finset (Fin (boxes n)))
          (Finset.univ : Finset (Fin (boxes n)))
          (fun i : Fin (boxes n) =>
            (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
              (fun _ : Ω => (1 : ℝ)) ω)
          (fun j : Fin (boxes n) =>
            (prob_11_9_oneBoxEmptyEvent boxes k locations n j).indicator
              (fun _ : Ω => (1 : ℝ)) ω))
    have hratio :
        prob_11_9_emptyBoxRatio boxes X n ω = S / b := by
      calc
        prob_11_9_emptyBoxRatio boxes X n ω =
            X n ω / (boxes n : ℝ) := rfl
        _ =
            (prob_11_9_emptyBoxCountFromLocations boxes k locations n ω : ℝ) /
              (boxes n : ℝ) := by
              rw [hX n ω]
        _ = S / b := by
          dsimp [S, b]
          rw [hcount]
    calc
      (prob_11_9_emptyBoxRatio boxes X n ω) ^ 2 =
          (S / b) ^ 2 := by rw [hratio]
      _ = (1 / b ^ 2) * (S * S) := by
        field_simp [hbne]
      _ =
          (1 / b ^ 2) *
            ∑ i : Fin (boxes n),
              ∑ j : Fin (boxes n),
                (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
                    (fun _ : Ω => (1 : ℝ)) ω *
                  (prob_11_9_oneBoxEmptyEvent boxes k locations n j).indicator
                    (fun _ : Ω => (1 : ℝ)) ω := by
          rw [hsumprod]
  have hProdInt :
      ∀ i j : Fin (boxes n),
        Integrable
          (fun ω : Ω =>
            (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
                (fun _ : Ω => (1 : ℝ)) ω *
              (prob_11_9_oneBoxEmptyEvent boxes k locations n j).indicator
                (fun _ : Ω => (1 : ℝ)) ω) P := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [prob_11_9_oneBoxIndicator_mul_self boxes k locations i]
      exact prob_11_9_oneBoxIndicator_integrable P boxes k locations i
        (hOneMeas n i)
    · rw [prob_11_9_oneBoxIndicator_mul_pair boxes k locations i j]
      exact prob_11_9_twoBoxIndicator_integrable P boxes k locations i j
        (hTwoMeas n i j)
  have hInnerInt :
      ∀ i ∈ (Finset.univ : Finset (Fin (boxes n))),
        Integrable
          (fun ω : Ω =>
            ∑ j : Fin (boxes n),
              (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
                  (fun _ : Ω => (1 : ℝ)) ω *
                (prob_11_9_oneBoxEmptyEvent boxes k locations n j).indicator
                  (fun _ : Ω => (1 : ℝ)) ω) P := by
    intro i _hi
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun j _hj => hProdInt i j)
  have hEachIntegral :
      ∀ i j : Fin (boxes n),
        ∫ ω : Ω,
            (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
                (fun _ : Ω => (1 : ℝ)) ω *
              (prob_11_9_oneBoxEmptyEvent boxes k locations n j).indicator
                (fun _ : Ω => (1 : ℝ)) ω ∂P =
          if i = j then p1 else p2 := by
    intro i j
    simpa [p1, p2] using
      (prob_11_9_oneBoxIndicator_product_integral P boxes k locations i j
        (fun i => hOneMeas n i) (fun i j => hTwoMeas n i j)
        hOneProb hTwoProb)
  rw [hYsqeq, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finset_sum Finset.univ hInnerInt]
  have hInnerIntegral :
      (∑ i : Fin (boxes n),
        ∫ ω : Ω,
          ∑ j : Fin (boxes n),
            (prob_11_9_oneBoxEmptyEvent boxes k locations n i).indicator
                (fun _ : Ω => (1 : ℝ)) ω *
              (prob_11_9_oneBoxEmptyEvent boxes k locations n j).indicator
                (fun _ : Ω => (1 : ℝ)) ω ∂P) =
        ∑ i : Fin (boxes n), ∑ j : Fin (boxes n), (if i = j then p1 else p2) := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [MeasureTheory.integral_finset_sum Finset.univ
      (fun j _hj => hProdInt i j)]
    apply Finset.sum_congr rfl
    intro j _hj
    exact hEachIntegral i j
  rw [hInnerIntegral]
  rw [prob_11_9_fin_double_two_probability_sum]
  dsimp [b, p1, p2]
  field_simp [show (boxes n : ℝ) ≠ 0 by exact_mod_cast ne_of_gt hbox]

theorem prob_11_9_emptyBoxRatio_bounds {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (boxes k : ℕ → ℕ) (X : ℕ → Ω → ℝ) {n : ℕ}
    (hModel : prob_11_9_finiteIndependentUniformEmptyBoxModel P boxes k X)
    (hbox : 0 < boxes n) :
    ∀ ω : Ω,
      0 ≤ prob_11_9_emptyBoxRatio boxes X n ω ∧
        prob_11_9_emptyBoxRatio boxes X n ω ≤ 1 := by
  classical
  rcases hModel with
    ⟨locations, hX, _hOneMeas, _hTwoMeas, _hUniform⟩
  intro ω
  have hcard :
      prob_11_9_emptyBoxCountFromLocations boxes k locations n ω ≤ boxes n := by
    unfold prob_11_9_emptyBoxCountFromLocations
    have hle :
        (Finset.univ.filter
          (fun i : Fin (boxes n) => ∀ b : Fin (k n), locations n ω b ≠ i)).card ≤
          (Finset.univ : Finset (Fin (boxes n))).card :=
      Finset.card_filter_le _ _
    simpa [Fintype.card_fin] using hle
  have hbpos : 0 < (boxes n : ℝ) := by exact_mod_cast hbox
  rw [prob_11_9_emptyBoxRatio, hX n ω]
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hbpos)
  · rw [div_le_one hbpos]
    exact_mod_cast hcard

theorem prob_11_9_centered_square_integral_eq {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (boxes k : ℕ → ℕ) (X : ℕ → Ω → ℝ) {n : ℕ} (c : ℝ)
    (hModel : prob_11_9_finiteIndependentUniformEmptyBoxModel P boxes k X)
    (hbox : 0 < boxes n)
    (hYMeas : AEStronglyMeasurable
      ((prob_11_9_emptyBoxRatio boxes X) n) P) :
    ∫ ω : Ω,
        |prob_11_9_emptyBoxRatio boxes X n ω - c| ^ 2 ∂P =
      (((((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)) /
          (boxes n : ℝ) +
        ((((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) *
          ((((boxes n - 2 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)))) -
        (2 * c) *
          ((((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)) +
        c ^ 2 := by
  classical
  let Y : Ω → ℝ := (prob_11_9_emptyBoxRatio boxes X) n
  have hBounds := prob_11_9_emptyBoxRatio_bounds P boxes k X hModel hbox
  have hYInt : Integrable Y P := by
    refine Integrable.of_bound hYMeas 1 ?_
    filter_upwards with ω
    have hle := (hBounds ω).2
    have hnonneg := (hBounds ω).1
    dsimp [Y]
    rw [abs_of_nonneg hnonneg]
    exact hle
  have hY2Meas : AEStronglyMeasurable (fun ω : Ω => Y ω ^ 2) P := by
    simpa [Y] using hYMeas.pow 2
  have hY2Int : Integrable (fun ω : Ω => Y ω ^ 2) P := by
    refine Integrable.of_bound hY2Meas 1 ?_
    filter_upwards with ω
    have hle := (hBounds ω).2
    have hnonneg := (hBounds ω).1
    have hyabs : |Y ω| ≤ 1 := by
      dsimp [Y]
      rw [abs_of_nonneg hnonneg]
      exact hle
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Y ω))]
    nlinarith [hle, hnonneg]
  have hLinInt : Integrable (fun ω : Ω => (2 * c) * Y ω) P :=
    hYInt.const_mul (2 * c)
  have hSubInt :
      Integrable (fun ω : Ω => Y ω ^ 2 - (2 * c) * Y ω) P :=
    hY2Int.sub hLinInt
  calc
    ∫ ω : Ω, |prob_11_9_emptyBoxRatio boxes X n ω - c| ^ 2 ∂P =
        ∫ ω : Ω, Y ω ^ 2 - (2 * c) * Y ω + c ^ 2 ∂P := by
          congr 1
          funext ω
          dsimp [Y]
          rw [sq_abs]
          ring
    _ =
        (∫ ω : Ω, Y ω ^ 2 - (2 * c) * Y ω ∂P) +
          ∫ _ω : Ω, c ^ 2 ∂P := by
          rw [MeasureTheory.integral_add hSubInt (integrable_const (c ^ 2))]
    _ =
        (∫ ω : Ω, Y ω ^ 2 ∂P) -
          (∫ ω : Ω, (2 * c) * Y ω ∂P) +
          c ^ 2 := by
          rw [MeasureTheory.integral_sub hY2Int hLinInt]
          simp
    _ =
        (∫ ω : Ω, (prob_11_9_emptyBoxRatio boxes X n ω) ^ 2 ∂P) -
          (2 * c) *
            (∫ ω : Ω, prob_11_9_emptyBoxRatio boxes X n ω ∂P) +
          c ^ 2 := by
          dsimp [Y]
          rw [MeasureTheory.integral_const_mul]
    _ =
      (((((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)) /
          (boxes n : ℝ) +
        ((((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) *
          ((((boxes n - 2 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)))) -
        (2 * c) *
          ((((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)) +
        c ^ 2 := by
          rw [prob_11_9_emptyBoxRatio_sq_integral_eq P boxes k X hModel hbox,
            prob_11_9_emptyBoxRatio_integral_eq P boxes k X hModel hbox]

theorem prob_11_9_meanDeviationMoment_eq_formula {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (boxes k : ℕ → ℕ) (X : ℕ → Ω → ℝ) {n : ℕ} (c : ℝ)
    (hModel : prob_11_9_finiteIndependentUniformEmptyBoxModel P boxes k X)
    (hbox : 0 < boxes n)
    (hYMeas : AEStronglyMeasurable
      ((prob_11_9_emptyBoxRatio boxes X) n) P) :
    meanDeviationMoment P (prob_11_9_emptyBoxRatio boxes X)
        (fun _ : Ω => c) 2 n =
      ENNReal.ofReal
        ((((((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)) /
            (boxes n : ℝ) +
          ((((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) *
            ((((boxes n - 2 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)))) -
          (2 * c) *
            ((((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)) +
          c ^ 2) := by
  classical
  let Y : Ω → ℝ := (prob_11_9_emptyBoxRatio boxes X) n
  have hBounds := prob_11_9_emptyBoxRatio_bounds P boxes k X hModel hbox
  have hDevMeas :
      AEStronglyMeasurable
        (fun ω : Ω => |prob_11_9_emptyBoxRatio boxes X n ω - c| ^ 2) P := by
    have hbase : AEStronglyMeasurable (fun ω : Ω => ‖Y ω - c‖ ^ 2) P := by
      exact ((hYMeas.sub aestronglyMeasurable_const).norm.pow 2)
    simpa [Y, Real.norm_eq_abs] using hbase
  have hDevInt :
      Integrable
        (fun ω : Ω => |prob_11_9_emptyBoxRatio boxes X n ω - c| ^ 2) P := by
    refine Integrable.of_bound hDevMeas ((1 + |c|) ^ 2) ?_
    filter_upwards with ω
    have hle := (hBounds ω).2
    have hnonneg := (hBounds ω).1
    have hyabs :
        |prob_11_9_emptyBoxRatio boxes X n ω| ≤ 1 := by
      rw [abs_of_nonneg hnonneg]
      exact hle
    have hdevle :
        |prob_11_9_emptyBoxRatio boxes X n ω - c| ≤ 1 + |c| :=
      by
        have htri := abs_sub (prob_11_9_emptyBoxRatio boxes X n ω) c
        nlinarith [htri, hyabs, abs_nonneg c]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hdevle, abs_nonneg c,
      abs_nonneg (prob_11_9_emptyBoxRatio boxes X n ω - c)]
  have hNonneg :
      0 ≤ᵐ[P]
        fun ω : Ω => |prob_11_9_emptyBoxRatio boxes X n ω - c| ^ 2 :=
    Eventually.of_forall (fun _ω => sq_nonneg _)
  rw [meanDeviationMoment]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hDevInt hNonneg]
  rw [prob_11_9_centered_square_integral_eq P boxes k X c hModel hbox hYMeas]

/-- The asymptotic regime from Problem 11.9: the number of boxes diverges,
`k_n / n` tends to a positive constant `a`, and each experiment has at least
one box. -/
def prob_11_9_asymptoticRegime (boxes k : ℕ → ℕ) (a : ℝ) : Prop :=
  (∀ n : ℕ, 0 < boxes n) ∧
    Tendsto (fun n : ℕ => (boxes n : ℝ)) atTop atTop ∧
    0 < a ∧
    Tendsto (fun n : ℕ => (k n : ℝ) / (boxes n : ℝ)) atTop (nhds a)

/-- The textbook occupancy second-moment calculation for Problem 11.9. -/
theorem prob_11_9_occupancy_moment_calculation_internal
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (boxes k : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ)
    (hModel : prob_11_9_finiteIndependentUniformEmptyBoxModel P boxes k X)
    (hRegime : prob_11_9_asymptoticRegime boxes k a)
    (hX :
      ∀ n : ℕ, AEStronglyMeasurable ((prob_11_9_emptyBoxRatio boxes X) n) P) :
    Tendsto
      (fun n : ℕ =>
        meanDeviationMoment P (prob_11_9_emptyBoxRatio boxes X)
          (fun _ : Ω => Real.exp (-a)) 2 n)
      atTop (nhds 0) := by
  classical
  rcases hRegime with ⟨hboxpos, hboxes, _ha, hratio⟩
  let c0 : ℝ := Real.exp (-a)
  let p1 : ℕ → ℝ :=
    fun n : ℕ => (((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)
  let p2 : ℕ → ℝ :=
    fun n : ℕ => (((boxes n - 2 : ℕ) : ℝ) / (boxes n : ℝ)) ^ (k n)
  let second : ℕ → ℝ :=
    fun n : ℕ => p1 n / (boxes n : ℝ) +
      (((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)) * p2 n
  let centered : ℕ → ℝ :=
    fun n : ℕ => second n - (2 * c0) * p1 n + c0 ^ 2
  have hp1raw :
      Tendsto (fun n : ℕ => (1 - (1 : ℝ) / (boxes n : ℝ)) ^ k n)
        atTop (nhds c0) := by
    simpa [c0] using
      prob_11_9_tendsto_one_sub_const_div_pow
        (boxes := boxes) (k := k) (a := a) (c := (1 : ℝ))
        (by norm_num) hboxes hratio
  have hp1 : Tendsto p1 atTop (nhds c0) := by
    refine hp1raw.congr' ?_
    filter_upwards with n
    have hle : 1 ≤ boxes n := Nat.succ_le_of_lt (hboxpos n)
    have hbne : (boxes n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (hboxpos n)
    dsimp [p1]
    congr 1
    have hsub : ((boxes n - 1 : ℕ) : ℝ) = (boxes n : ℝ) - 1 := by
      rw [Nat.cast_sub hle]
      norm_num
    rw [hsub]
    field_simp [hbne]
  have hp2raw :
      Tendsto (fun n : ℕ => (1 - (2 : ℝ) / (boxes n : ℝ)) ^ k n)
        atTop (nhds (Real.exp (-(2 * a)))) := by
    simpa using
      prob_11_9_tendsto_one_sub_const_div_pow
        (boxes := boxes) (k := k) (a := a) (c := (2 : ℝ))
        (by norm_num) hboxes hratio
  have hp2 : Tendsto p2 atTop (nhds (Real.exp (-(2 * a)))) := by
    refine hp2raw.congr' ?_
    filter_upwards [hboxes.eventually_ge_atTop (2 : ℝ)] with n hge
    have hle : 2 ≤ boxes n := by exact_mod_cast hge
    have hposNat : 0 < boxes n := lt_of_lt_of_le (by norm_num : 0 < 2) hle
    have hbne : (boxes n : ℝ) ≠ 0 := by
      exact_mod_cast ne_of_gt hposNat
    dsimp [p2]
    congr 1
    have hsub : ((boxes n - 2 : ℕ) : ℝ) = (boxes n : ℝ) - 2 := by
      rw [Nat.cast_sub hle]
      norm_num
    rw [hsub]
    field_simp [hbne]
  have hInv :
      Tendsto (fun n : ℕ => (1 : ℝ) / (boxes n : ℝ)) atTop (nhds 0) := by
    simpa [one_div] using hboxes.inv_tendsto_atTop
  have hTerm1 :
      Tendsto (fun n : ℕ => p1 n / (boxes n : ℝ)) atTop (nhds 0) := by
    exact hp1.div_atTop hboxes
  have hCoefRaw :
      Tendsto (fun n : ℕ => 1 - (1 : ℝ) / (boxes n : ℝ))
        atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hInv
  have hCoef :
      Tendsto
        (fun n : ℕ => (((boxes n - 1 : ℕ) : ℝ) / (boxes n : ℝ)))
        atTop (nhds 1) := by
    refine hCoefRaw.congr' ?_
    filter_upwards with n
    have hle : 1 ≤ boxes n := Nat.succ_le_of_lt (hboxpos n)
    have hbne : (boxes n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (hboxpos n)
    have hsub : ((boxes n - 1 : ℕ) : ℝ) = (boxes n : ℝ) - 1 := by
      rw [Nat.cast_sub hle]
      norm_num
    rw [hsub]
    field_simp [hbne]
  have hsecond :
      Tendsto second atTop (nhds (Real.exp (-(2 * a)))) := by
    dsimp [second]
    simpa using hTerm1.add (hCoef.mul hp2)
  have hlinear :
      Tendsto (fun n : ℕ => (2 * c0) * p1 n)
        atTop (nhds ((2 * c0) * c0)) := by
    simpa using tendsto_const_nhds.mul hp1
  have hcentered :
      Tendsto centered atTop (nhds 0) := by
    have hlim :
        Tendsto centered atTop
          (nhds (Real.exp (-(2 * a)) - (2 * c0) * c0 + c0 ^ 2)) := by
      dsimp [centered]
      exact (hsecond.sub hlinear).add tendsto_const_nhds
    have hexp2 : Real.exp (-(2 * a)) = c0 ^ 2 := by
      dsimp [c0]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    convert hlim using 1
    rw [hexp2]
    ring
  have hMomentEq :
      ∀ n : ℕ,
        meanDeviationMoment P (prob_11_9_emptyBoxRatio boxes X)
            (fun _ : Ω => Real.exp (-a)) 2 n =
          ENNReal.ofReal (centered n) := by
    intro n
    simpa [centered, second, p1, p2, c0] using
      (prob_11_9_meanDeviationMoment_eq_formula P boxes k X
        (c := Real.exp (-a)) hModel (hboxpos n) (hX n))
  have hEnn : Tendsto (fun n : ℕ => ENNReal.ofReal (centered n))
      atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hcentered
  exact hEnn.congr' (Eventually.of_forall (fun n => (hMomentEq n).symm))

/-- Support for translating the concrete mean-square moment statement above to
the `eLpNorm` premise used by Theorem 10.5. -/
def prob_11_9_meanSquareELpNormSupport {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (boxes : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ) : Prop :=
  ConvergesInMeanSquare P (prob_11_9_emptyBoxRatio boxes X)
      (fun _ : Ω => Real.exp (-a)) →
    (∀ n : ℕ, AEStronglyMeasurable ((prob_11_9_emptyBoxRatio boxes X) n) P) ∧
      AEStronglyMeasurable (fun _ : Ω => Real.exp (-a)) P ∧
      Tendsto
        (fun n : ℕ =>
          eLpNorm
            (((prob_11_9_emptyBoxRatio boxes X) n) - fun _ : Ω => Real.exp (-a))
            (2 : ENNReal) P)
        atTop (nhds 0)

/-- The `ConvergesInMeanSquare` definition is exactly the square of the
`L^2` seminorm, so convergence in mean square gives the `eLpNorm` limit needed
by Theorem 10.5. -/
theorem prob_11_9_eLpNorm_tendsto_of_convergesInMeanSquare
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (boxes : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ)
    (hMS : ConvergesInMeanSquare P (prob_11_9_emptyBoxRatio boxes X)
      (fun _ : Ω => Real.exp (-a))) :
    Tendsto
      (fun n : ℕ =>
        eLpNorm
          (((prob_11_9_emptyBoxRatio boxes X) n) -
            fun _ : Ω => Real.exp (-a))
          (2 : ENNReal) P)
      atTop (nhds 0) := by
  rcases hMS with ⟨_hTwo, hTendsto⟩
  have hroot :
      Tendsto (fun y : ENNReal => y ^ (1 / (2 : ℝ))) (nhds 0) (nhds 0) := by
    simpa using
      (ENNReal.continuous_rpow_const (y := (1 / (2 : ℝ)))).tendsto 0
  have hcomp := hroot.comp hTendsto
  convert hcomp using 1
  ext n
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  congr 1
  congr with ω
  rw [Real.enorm_eq_ofReal_abs]
  norm_num
  rw [← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]

/-- The remaining bridge from quadratic mean to the Chapter 10 `L^2` interface
is measurable-data only; the analytic norm limit is proved above. -/
theorem prob_11_9_meanSquareELpNormSupport_of_measurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (boxes : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ)
    (hX :
      ∀ n : ℕ, AEStronglyMeasurable ((prob_11_9_emptyBoxRatio boxes X) n) P) :
    prob_11_9_meanSquareELpNormSupport P boxes X a := by
  intro hMS
  exact ⟨hX, aestronglyMeasurable_const,
    prob_11_9_eLpNorm_tendsto_of_convergesInMeanSquare P boxes X a hMS⟩

/-- Problem 11.9, quadratic-mean part: the empty-box proportion converges to
`e^{-a}` in mean square. -/
theorem prob_11_9_quadratic_mean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (boxes k : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ)
    (hModel : prob_11_9_finiteIndependentUniformEmptyBoxModel P boxes k X)
    (hRegime : prob_11_9_asymptoticRegime boxes k a)
    (hX :
      ∀ n : ℕ, AEStronglyMeasurable ((prob_11_9_emptyBoxRatio boxes X) n) P) :
    ConvergesInMeanSquare P (prob_11_9_emptyBoxRatio boxes X)
      (fun _ : Ω => Real.exp (-a)) := by
  refine ⟨by norm_num, ?_⟩
  exact
    prob_11_9_occupancy_moment_calculation_internal P boxes k X a hModel
      hRegime hX

/-- Problem 11.9, probability part: the mean-square convergence is passed to
convergence in probability through the Chapter 10 `L^r` result. -/
private theorem prob_11_9_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (boxes : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ)
    (hMS : ConvergesInMeanSquare P (prob_11_9_emptyBoxRatio boxes X)
      (fun _ : Ω => Real.exp (-a)))
    (hX :
      ∀ n : ℕ, AEStronglyMeasurable ((prob_11_9_emptyBoxRatio boxes X) n) P) :
    ConvergesInProbability P (prob_11_9_emptyBoxRatio boxes X)
      (fun _ : Ω => Real.exp (-a)) := by
  let hELp := prob_11_9_meanSquareELpNormSupport_of_measurable P boxes X a hX
  rcases hELp hMS with ⟨hX, hLimit, hLp⟩
  exact thm_10_5 P (prob_11_9_emptyBoxRatio boxes X)
    (fun _ : Ω => Real.exp (-a)) (p := (2 : ENNReal)) (by norm_num) hX hLimit hLp

/-- Problem 11.9: in the independent uniform occupancy experiment with
`k_n / n → a > 0`, the proportion of empty boxes converges to `e^{-a}` in
quadratic mean and hence in probability. -/
theorem prob_11_9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (boxes k : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ)
    (hModel : prob_11_9_finiteIndependentUniformEmptyBoxModel P boxes k X)
    (hRegime : prob_11_9_asymptoticRegime boxes k a)
    (hX :
      ∀ n : ℕ, AEStronglyMeasurable ((prob_11_9_emptyBoxRatio boxes X) n) P) :
    ConvergesInMeanSquare P (prob_11_9_emptyBoxRatio boxes X)
        (fun _ : Ω => Real.exp (-a)) ∧
      ConvergesInProbability P (prob_11_9_emptyBoxRatio boxes X)
        (fun _ : Ω => Real.exp (-a)) := by
  let hMS := prob_11_9_quadratic_mean P boxes k X a hModel hRegime hX
  exact ⟨hMS, prob_11_9_probability P boxes X a hMS hX⟩
