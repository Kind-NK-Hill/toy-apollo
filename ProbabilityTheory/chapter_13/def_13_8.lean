/-
TASK ID: def_13_8
TYPE: Definition
SOURCE PLAN: chapter13-martingale-stopping-time
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_13.def_13_7




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

noncomputable section



def def_13_8_isStoppingTime {Ω : Type*}
    (𝓕n : ℕ → MeasurableSpace Ω) (T : Ω → WithTop ℕ) : Prop :=
  ∀ n : ℕ, @MeasurableSet Ω (𝓕n n) {ω | T ω ≤ (n : WithTop ℕ)}



def def_13_8 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (𝓕n : ℕ → MeasurableSpace Ω) (T : Ω → WithTop ℕ) : Prop :=
  def_13_6_isFiltration (𝓕 := 𝓕) 𝓕n ∧
    def_13_8_isStoppingTime 𝓕n T

theorem def_13_8_isFiltration {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {𝓕n : ℕ → MeasurableSpace Ω} {T : Ω → WithTop ℕ}
    (hT : def_13_8 𝓕n T) :
    def_13_6_isFiltration (𝓕 := 𝓕) 𝓕n :=
  hT.1

theorem def_13_8_isStoppingTime_raw {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {𝓕n : ℕ → MeasurableSpace Ω} {T : Ω → WithTop ℕ}
    (hT : def_13_8 𝓕n T) :
    def_13_8_isStoppingTime 𝓕n T :=
  hT.2

theorem def_13_8_event_le_measurable {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {𝓕n : ℕ → MeasurableSpace Ω} {T : Ω → WithTop ℕ}
    (hT : def_13_8 𝓕n T) (n : ℕ) :
    @MeasurableSet Ω (𝓕n n) {ω | T ω ≤ (n : WithTop ℕ)} :=
  hT.2 n



def def_13_8_mathlibFiltration {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (𝓕n : ℕ → MeasurableSpace Ω)
    (h𝓕n : def_13_6_isFiltration (𝓕 := 𝓕) 𝓕n) :
    MeasureTheory.Filtration ℕ 𝓕 where
  seq := 𝓕n
  mono' := fun _ _ hnm => def_13_6_mono h𝓕n hnm
  le' := h𝓕n.1



theorem def_13_8_toMathlibIsStoppingTime {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {𝓕n : ℕ → MeasurableSpace Ω}
    {T : Ω → WithTop ℕ} (hT : def_13_8 𝓕n T) :
    MeasureTheory.IsStoppingTime
      (def_13_8_mathlibFiltration 𝓕n hT.1) T :=
  hT.2

 
theorem def_13_8_measurable {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {𝓕n : ℕ → MeasurableSpace Ω} {T : Ω → WithTop ℕ}
    (hT : def_13_8 𝓕n T) : Measurable T :=
  (def_13_8_toMathlibIsStoppingTime hT).measurable'



def def_13_8_history {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) :
    Ω → Fin (n + 1) → ℝ :=
  fun ω k => X k.1 ω

 
def def_13_8_historyProjection {n m : ℕ} (hnm : n ≤ m) :
    (Fin (m + 1) → ℝ) → (Fin (n + 1) → ℝ) :=
  fun v k => v (Fin.castLE (Nat.add_le_add_right hnm 1) k)

theorem def_13_8_historyProjection_measurable {n m : ℕ} (hnm : n ≤ m) :
    Measurable (def_13_8_historyProjection hnm) := by
  exact measurable_pi_lambda _ fun k =>
    measurable_pi_apply (Fin.castLE (Nat.add_le_add_right hnm 1) k)

theorem def_13_8_historyProjection_comp {Ω : Type*}
    (X : ℕ → Ω → ℝ) {n m : ℕ} (hnm : n ≤ m) :
    def_13_8_history X n =
      def_13_8_historyProjection hnm ∘ def_13_8_history X m := by
  funext ω k
  simp [def_13_8_history, def_13_8_historyProjection]

 
@[reducible]
def def_13_8_historySigma {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) :
    MeasurableSpace Ω :=
  (inferInstance : MeasurableSpace (Fin (n + 1) → ℝ)).comap
    (def_13_8_history X n)

 
@[reducible]
def def_13_8_naturalFiltration {Ω : Type*}
    (X : ℕ → Ω → ℝ) : ℕ → MeasurableSpace Ω :=
  fun n => def_13_8_historySigma X n

theorem def_13_8_history_measurable_self {Ω : Type*}
    (X : ℕ → Ω → ℝ) (n : ℕ) :
    @Measurable Ω (Fin (n + 1) → ℝ)
      (def_13_8_naturalFiltration X n) _ (def_13_8_history X n) :=
  Measurable.of_comap_le le_rfl

theorem def_13_8_history_measurable_of_le {Ω : Type*}
    (X : ℕ → Ω → ℝ) {n m : ℕ} (hnm : n ≤ m) :
    @Measurable Ω (Fin (n + 1) → ℝ)
      (def_13_8_naturalFiltration X m) _ (def_13_8_history X n) := by
  have hcomp :=
    (def_13_8_historyProjection_measurable hnm).comp
      (def_13_8_history_measurable_self X m)
  simpa [def_13_8_historyProjection_comp X hnm] using hcomp



theorem def_13_8_naturalFiltration_mono {Ω : Type*}
    (X : ℕ → Ω → ℝ) : Monotone (def_13_8_naturalFiltration X) := by
  intro n m hnm
  exact (def_13_8_history_measurable_of_le X hnm).comap_le

theorem def_13_8_history_measurable {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hX : ∀ n : ℕ, @Measurable Ω ℝ 𝓕 _ (X n)) (n : ℕ) :
    @Measurable Ω (Fin (n + 1) → ℝ) 𝓕 _
      (def_13_8_history X n) := by
  exact measurable_pi_lambda _ fun k => hX k.1



theorem def_13_8_naturalFiltration_sub_ambient {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hX : ∀ n : ℕ, @Measurable Ω ℝ 𝓕 _ (X n)) (n : ℕ) :
    def_13_8_naturalFiltration X n ≤ 𝓕 :=
  (def_13_8_history_measurable X hX n).comap_le



theorem def_13_8_naturalFiltration_isFiltration {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hX : ∀ n : ℕ, @Measurable Ω ℝ 𝓕 _ (X n)) :
    def_13_6_isFiltration (𝓕 := 𝓕) (def_13_8_naturalFiltration X) := by
  refine ⟨?_, ?_⟩
  · exact def_13_8_naturalFiltration_sub_ambient X hX
  · intro n m hnm
    exact def_13_8_naturalFiltration_mono X hnm



def def_13_8_stoppingTimeForSequence {Ω : Type*}
    [𝓕 : MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (T : Ω → WithTop ℕ) : Prop :=
  def_13_8 (def_13_8_naturalFiltration X) T

theorem def_13_8_sequence_event_le_measurable {Ω : Type*}
    [𝓕 : MeasurableSpace Ω]
    {X : ℕ → Ω → ℝ} {T : Ω → WithTop ℕ}
    (hT : def_13_8_stoppingTimeForSequence X T) (n : ℕ) :
    @MeasurableSet Ω (def_13_8_historySigma X n)
      {ω | T ω ≤ (n : WithTop ℕ)} :=
  hT.2 n

theorem def_13_8_stoppingTimeForSequence_of_events {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (T : Ω → WithTop ℕ)
    (hX : ∀ n : ℕ, @Measurable Ω ℝ 𝓕 _ (X n))
    (hT : def_13_8_isStoppingTime (def_13_8_naturalFiltration X) T) :
    def_13_8_stoppingTimeForSequence X T :=
  ⟨def_13_8_naturalFiltration_isFiltration X hX, hT⟩



def def_13_8_stoppedValue {Ω S : Type*}
    (X : ℕ → Ω → S) (T : Ω → WithTop ℕ) : Ω → Option S :=
  fun ω =>
    match T ω with
    | none => none
    | some n => some (X n ω)

theorem def_13_8_stoppedValue_finite {Ω S : Type*}
    (X : ℕ → Ω → S) (T : Ω → WithTop ℕ) (ω : Ω) (n : ℕ)
    (hT : T ω = (n : WithTop ℕ)) :
    def_13_8_stoppedValue X T ω = some (X n ω) := by
  simp [def_13_8_stoppedValue, hT]

theorem def_13_8_stoppedValue_top {Ω S : Type*}
    (X : ℕ → Ω → S) (T : Ω → WithTop ℕ) (ω : Ω)
    (hT : T ω = ⊤) :
    def_13_8_stoppedValue X T ω = none := by
  simp [def_13_8_stoppedValue, hT]



def def_13_8_optionToSum {S : Type*} : Option S → PUnit.{1} ⊕ S
  | none => Sum.inl PUnit.unit
  | some x => Sum.inr x



@[reducible]
def def_13_8_optionMeasurableSpace (S : Type*) [MeasurableSpace S] :
    MeasurableSpace (Option S) :=
  (inferInstance : MeasurableSpace (PUnit ⊕ S)).comap
    def_13_8_optionToSum



theorem def_13_8_stoppedValue_measurable_of_measurable
    {Ω S : Type*} [𝓕 : MeasurableSpace Ω] [MeasurableSpace S]
    (X : ℕ → Ω → S) (T : Ω → WithTop ℕ)
    (hX : ∀ n : ℕ, Measurable (X n)) (hT : Measurable T) :
    @Measurable Ω (Option S) 𝓕 (def_13_8_optionMeasurableSpace S)
      (def_13_8_stoppedValue X T) := by
  classical
  rw [def_13_8_optionMeasurableSpace, measurable_comap_iff]
  intro s hs
  let topEvent : Set Ω := {ω | T ω = ⊤}
  let finiteEvent : ℕ → Set Ω := fun n =>
    {ω | T ω = (n : WithTop ℕ)} ∩ (X n) ⁻¹' (Sum.inr ⁻¹' s)
  have htop : MeasurableSet topEvent := by
    exact (measurableSet_singleton (⊤ : WithTop ℕ)).preimage hT
  have hfinite : ∀ n : ℕ, MeasurableSet (finiteEvent n) := by
    intro n
    exact ((measurableSet_singleton (n : WithTop ℕ)).preimage hT).inter
      ((hX n) (measurable_inr hs))
  have hpreimage :
      (def_13_8_optionToSum ∘ def_13_8_stoppedValue X T) ⁻¹' s =
        (if Sum.inl PUnit.unit ∈ s then topEvent else ∅) ∪
          ⋃ n : ℕ, finiteEvent n := by
    ext ω
    cases hTω : T ω with
    | top =>
        simp [def_13_8_stoppedValue, def_13_8_optionToSum,
          topEvent, finiteEvent, hTω]
    | coe n =>
        simp [def_13_8_stoppedValue, def_13_8_optionToSum,
          topEvent, finiteEvent, hTω]
  rw [hpreimage]
  have htopBranch :
      MeasurableSet (if Sum.inl PUnit.unit ∈ s then topEvent else ∅) := by
    by_cases hmem : Sum.inl PUnit.unit ∈ s
    · simpa [hmem] using htop
    · simp [hmem]
  exact htopBranch.union (MeasurableSet.iUnion hfinite)



theorem def_13_8_stoppedValue_measurable
    {Ω S : Type*} [𝓕 : MeasurableSpace Ω] [MeasurableSpace S]
    {𝓕n : ℕ → MeasurableSpace Ω} (X : ℕ → Ω → S)
    (T : Ω → WithTop ℕ) (hX : ∀ n : ℕ, Measurable (X n))
    (hT : def_13_8 𝓕n T) :
    @Measurable Ω (Option S) 𝓕 (def_13_8_optionMeasurableSpace S)
      (def_13_8_stoppedValue X T) :=
  def_13_8_stoppedValue_measurable_of_measurable X T hX
    (def_13_8_measurable hT)
