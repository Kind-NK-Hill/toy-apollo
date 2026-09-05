/-
TASK ID: prob_11_9_model_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_10.def_10_3
import ProbabilityTheory.chapter_10.thm_10_5
import ProbabilityTheory.chapter_11.thm_11_2

open Filter MeasureTheory ProbabilityTheory

noncomputable section

open scoped BigOperators

noncomputable def prob_11_9_emptyBoxRatio {Ω : Type*}
    (boxes : ℕ → ℕ) (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n ω => X n ω / (boxes n : ℝ)



def prob_11_9_oneBoxEmptyEvent {Ω : Type*} (boxes k : ℕ → ℕ)
    (locations : ∀ n : ℕ, Ω → Fin (k n) → Fin (boxes n))
    (n : ℕ) (i : Fin (boxes n)) : Set Ω :=
  {ω | ∀ b : Fin (k n), locations n ω b ≠ i}

 
def prob_11_9_twoBoxEmptyEvent {Ω : Type*} (boxes k : ℕ → ℕ)
    (locations : ∀ n : ℕ, Ω → Fin (k n) → Fin (boxes n))
    (n : ℕ) (i j : Fin (boxes n)) : Set Ω :=
  {ω | (∀ b : Fin (k n), locations n ω b ≠ i) ∧
      (∀ b : Fin (k n), locations n ω b ≠ j)}

 
noncomputable def prob_11_9_emptyBoxCountFromLocations {Ω : Type*}
    (boxes k : ℕ → ℕ)
    (locations : ∀ n : ℕ, Ω → Fin (k n) → Fin (boxes n))
    (n : ℕ) (ω : Ω) : ℕ := by
  classical
  exact (Finset.univ.filter
    (fun i : Fin (boxes n) => ∀ b : Fin (k n), locations n ω b ≠ i)).card



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
        (∑ x : α, A.indicator (1 : α → ℝ) x) =
          ((Finset.univ.filter (fun x : α => x ∈ A)).card : ℝ) := by
      calc
        (∑ x : α, A.indicator (1 : α → ℝ) x) =
            ∑ x : α, (if x ∈ A then (1 : ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro x _hx
              simp [Set.indicator_apply]
        _ = ((Finset.univ.filter (fun x : α => x ∈ A)).card : ℝ) := by
          rw [Finset.sum_boole]
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
