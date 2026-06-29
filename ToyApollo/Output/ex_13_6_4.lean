/-
TASK ID: ex_13_6_4
TYPE: Example_Proof
SOURCE PLAN: chapter13-martingale-stopping-time
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_13_8

-- WRITE FINAL LEAN CODE BELOW

noncomputable section

def ex_13_6_4_hitsBy {Ω : Type*}
    (X : ℕ → Ω → ℝ) (threshold : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∃ i : ℕ, i ≤ n ∧ threshold ≤ X i ω}

def ex_13_6_4_firstPassageTime {Ω : Type*}
    (X : ℕ → Ω → ℝ) (threshold : ℝ) : Ω → WithTop ℕ :=
  fun ω => by
    classical
    if h : ∃ n : ℕ, threshold ≤ X n ω then
      exact (Nat.find h : WithTop ℕ)
    else
      exact ⊤

theorem ex_13_6_4_firstPassageTime_le_iff {Ω : Type*}
    (X : ℕ → Ω → ℝ) (threshold : ℝ) (n : ℕ) (ω : Ω) :
    ex_13_6_4_firstPassageTime X threshold ω ≤ (n : WithTop ℕ) ↔
      ω ∈ ex_13_6_4_hitsBy X threshold n := by
  classical
  unfold ex_13_6_4_firstPassageTime ex_13_6_4_hitsBy
  by_cases h : ∃ m : ℕ, threshold ≤ X m ω
  · simp [h, Nat.find_le_iff]
  · simp [h]
    exact fun i _hi => lt_of_not_ge (fun hp => h ⟨i, hp⟩)

theorem ex_13_6_4_firstPassage_event {Ω : Type*}
    (X : ℕ → Ω → ℝ) (threshold : ℝ) (n : ℕ) :
    {ω | ex_13_6_4_firstPassageTime X threshold ω ≤ (n : WithTop ℕ)} =
      ex_13_6_4_hitsBy X threshold n := by
  ext ω
  exact ex_13_6_4_firstPassageTime_le_iff X threshold n ω

theorem ex_13_6_4_hitsBy_measurable_natural {Ω : Type*}
    (X : ℕ → Ω → ℝ) (threshold : ℝ) (n : ℕ) :
    @MeasurableSet Ω (def_13_8_naturalFiltration X n)
      (ex_13_6_4_hitsBy X threshold n) := by
  have hhist :
      @Measurable Ω (Fin (n + 1) → ℝ) (def_13_8_naturalFiltration X n)
        _ (def_13_8_history X n) :=
    Measurable.of_comap_le le_rfl
  have hcoord :
      ∀ i : Fin (n + 1),
        @MeasurableSet Ω (def_13_8_naturalFiltration X n)
          {ω : Ω | threshold ≤ X i.1 ω} := by
    intro i
    have hi :
        @Measurable Ω ℝ (def_13_8_naturalFiltration X n) _
          (fun ω : Ω => X i.1 ω) := by
      simpa [def_13_8_history] using (measurable_pi_apply i).comp hhist
    exact measurableSet_Ici.preimage hi
  have hset :
      ex_13_6_4_hitsBy X threshold n =
        ⋃ i : Fin (n + 1), {ω : Ω | threshold ≤ X i.1 ω} := by
    ext ω
    constructor
    · intro hω
      rcases hω with ⟨i, hin, hi⟩
      exact Set.mem_iUnion.2 ⟨⟨i, Nat.lt_succ_of_le hin⟩, hi⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨i, hi⟩
      exact ⟨i.1, Nat.le_of_lt_succ i.2, hi⟩
  rw [hset]
  exact MeasurableSet.iUnion hcoord

theorem ex_13_6_4_isStoppingTime {Ω : Type*}
    (𝓕n : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ) (threshold : ℝ)
    (h_hits :
      ∀ n : ℕ, @MeasurableSet Ω (𝓕n n) (ex_13_6_4_hitsBy X threshold n)) :
    def_13_8 𝓕n (ex_13_6_4_firstPassageTime X threshold) := by
  intro n
  rw [ex_13_6_4_firstPassage_event X threshold n]
  exact h_hits n

theorem ex_13_6_4_isStoppingTime_natural {Ω : Type*}
    (X : ℕ → Ω → ℝ) (threshold : ℝ) :
    def_13_8 (def_13_8_naturalFiltration X)
      (ex_13_6_4_firstPassageTime X threshold) := by
  intro n
  rw [ex_13_6_4_firstPassage_event X threshold n]
  exact ex_13_6_4_hitsBy_measurable_natural X threshold n

def ex_13_6_4 {Ω : Type*}
    (𝓕n : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ) : Prop :=
  def_13_8 𝓕n (ex_13_6_4_firstPassageTime X 100)

theorem ex_13_6_4_holds {Ω : Type*} (X : ℕ → Ω → ℝ) :
    ex_13_6_4 (def_13_8_naturalFiltration X) X := by
  exact ex_13_6_4_isStoppingTime_natural X 100
