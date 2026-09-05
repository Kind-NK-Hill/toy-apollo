/-
TASK ID: ex_13_6_5_waiting_time_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_13.ex_13_6_5_base_support
import ProbabilityTheory.chapter_13.thm_13_18

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

 
def ex_13_6_5_patternOccursAt (pattern : List ex_13_6_5_Key)
    (ω : ex_13_6_5_TypingPath) (t : ℕ) : Prop :=
  pattern.length ≤ t ∧
    ∀ i : Fin pattern.length,
      ω (t - pattern.length + i.1) = pattern.get i

 
def ex_13_6_5_patternOccursBy (pattern : List ex_13_6_5_Key)
    (ω : ex_13_6_5_TypingPath) (n : ℕ) : Prop :=
  ∃ t : ℕ, t ≤ n ∧ ex_13_6_5_patternOccursAt pattern ω t



noncomputable def ex_13_6_5_firstOccurrence
    (pattern : List ex_13_6_5_Key) :
    ex_13_6_5_TypingPath → WithTop ℕ := by
  classical
  exact fun ω =>
    if h : ∃ t : ℕ, ex_13_6_5_patternOccursAt pattern ω t then
      (Nat.find h : WithTop ℕ)
    else
      ⊤

theorem ex_13_6_5_firstOccurrence_le_iff_occursBy
    (pattern : List ex_13_6_5_Key)
    (ω : ex_13_6_5_TypingPath) (n : ℕ) :
    ex_13_6_5_firstOccurrence pattern ω ≤ (n : WithTop ℕ) ↔
      ex_13_6_5_patternOccursBy pattern ω n := by
  classical
  unfold ex_13_6_5_firstOccurrence ex_13_6_5_patternOccursBy
  by_cases h : ∃ t : ℕ, ex_13_6_5_patternOccursAt pattern ω t
  · simp only [h, ↓reduceDIte]
    constructor
    · intro hle
      refine ⟨Nat.find h, ?_, Nat.find_spec h⟩
      exact WithTop.coe_le_coe.mp hle
    · rintro ⟨t, htn, ht⟩
      have hfind : Nat.find h ≤ t := Nat.find_min' h ht
      exact_mod_cast hfind.trans htn
  · simp only [h, ↓reduceDIte]
    constructor
    · intro htop
      have hfalse : False := by
        simpa using htop
      exact False.elim hfalse
    · rintro ⟨t, _htn, ht⟩
      exact False.elim (h ⟨t, ht⟩)

theorem ex_13_6_5_patternOccursAt_of_history_eq
    {pattern : List ex_13_6_5_Key}
    {ω ω' : ex_13_6_5_TypingPath} {t n : ℕ}
    (htn : t ≤ n)
    (hHist :
      ex_13_6_5_keyHistory n ω = ex_13_6_5_keyHistory n ω')
    (hOcc : ex_13_6_5_patternOccursAt pattern ω t) :
    ex_13_6_5_patternOccursAt pattern ω' t := by
  rcases hOcc with ⟨hlen, hletters⟩
  refine ⟨hlen, ?_⟩
  intro i
  let idx : ℕ := t - pattern.length + i.1
  have hidx_lt_t : idx < t := by
    have hi : i.1 < pattern.length := i.2
    omega
  have hidx_lt_n : idx < n + 1 := by
    omega
  have hAt :=
    congrFun hHist ⟨idx, hidx_lt_n⟩
  have hPath : ω idx = ω' idx := by
    simpa [ex_13_6_5_keyHistory] using hAt
  exact hPath.symm.trans (hletters i)

theorem ex_13_6_5_patternOccursBy_of_history_eq
    {pattern : List ex_13_6_5_Key}
    {ω ω' : ex_13_6_5_TypingPath} {n : ℕ}
    (hHist :
      ex_13_6_5_keyHistory n ω = ex_13_6_5_keyHistory n ω')
    (hOcc : ex_13_6_5_patternOccursBy pattern ω n) :
    ex_13_6_5_patternOccursBy pattern ω' n := by
  rcases hOcc with ⟨t, htn, ht⟩
  exact
    ⟨t, htn,
      ex_13_6_5_patternOccursAt_of_history_eq htn hHist ht⟩

theorem ex_13_6_5_firstOccurrence_le_of_history_eq
    {pattern : List ex_13_6_5_Key}
    {ω ω' : ex_13_6_5_TypingPath} {n : ℕ}
    (hHist :
      ex_13_6_5_keyHistory n ω = ex_13_6_5_keyHistory n ω')
    (hLe : ex_13_6_5_firstOccurrence pattern ω ≤ (n : WithTop ℕ)) :
    ex_13_6_5_firstOccurrence pattern ω' ≤ (n : WithTop ℕ) := by
  rw [ex_13_6_5_firstOccurrence_le_iff_occursBy] at hLe ⊢
  exact ex_13_6_5_patternOccursBy_of_history_eq hHist hLe

theorem ex_13_6_5_typingNaturalFiltration_isFiltration_ambient :
    @def_13_6_isFiltration ex_13_6_5_TypingPath
      (inferInstanceAs (MeasurableSpace ex_13_6_5_TypingPath))
      ex_13_6_5_typingNaturalFiltration := by
  refine ⟨ex_13_6_5_typingNaturalFiltration_le, ?_⟩
  exact ex_13_6_5_typingNaturalFiltration_isFiltration.2

theorem ex_13_6_5_firstOccurrence_stoppingTime
    (pattern : List ex_13_6_5_Key) :
    def_13_8 ex_13_6_5_typingNaturalFiltration
      (ex_13_6_5_firstOccurrence pattern) := by
  refine ⟨ex_13_6_5_typingNaturalFiltration_isFiltration_ambient, ?_⟩
  intro n
  rw [ex_13_6_5_typingNaturalFiltration,
    ex_13_6_5_keyHistorySigma,
    MeasurableSpace.measurableSet_comap]
  let eventHist : Set (Fin (n + 1) → ex_13_6_5_Key) :=
    {hist | ∃ ω : ex_13_6_5_TypingPath,
      ex_13_6_5_keyHistory n ω = hist ∧
        ex_13_6_5_firstOccurrence pattern ω ≤ (n : WithTop ℕ)}
  refine ⟨eventHist, by trivial, ?_⟩
  ext ω
  constructor
  · rintro ⟨ω', hHist, hω'⟩
    exact ex_13_6_5_firstOccurrence_le_of_history_eq hHist hω'
  · intro hω
    exact ⟨ω, rfl, hω⟩

theorem ex_13_6_5_patternOccursAt_of_historyBefore_eq
    {pattern : List ex_13_6_5_Key}
    {ω ω' : ex_13_6_5_TypingPath} {t n : ℕ}
    (htn : t ≤ n)
    (hHist :
      ex_13_6_5_keyHistoryBefore n ω =
        ex_13_6_5_keyHistoryBefore n ω')
    (hOcc : ex_13_6_5_patternOccursAt pattern ω t) :
    ex_13_6_5_patternOccursAt pattern ω' t := by
  rcases hOcc with ⟨hlen, hletters⟩
  refine ⟨hlen, ?_⟩
  intro i
  let idx : ℕ := t - pattern.length + i.1
  have hidx_lt_t : idx < t := by
    have hi : i.1 < pattern.length := i.2
    omega
  have hidx_lt_n : idx < n := by
    omega
  have hAt := congrFun hHist ⟨idx, hidx_lt_n⟩
  have hPath : ω idx = ω' idx := by
    simpa [ex_13_6_5_keyHistoryBefore] using hAt
  exact hPath.symm.trans (hletters i)

theorem ex_13_6_5_patternOccursBy_of_historyBefore_eq
    {pattern : List ex_13_6_5_Key}
    {ω ω' : ex_13_6_5_TypingPath} {n : ℕ}
    (hHist :
      ex_13_6_5_keyHistoryBefore n ω =
        ex_13_6_5_keyHistoryBefore n ω')
    (hOcc : ex_13_6_5_patternOccursBy pattern ω n) :
    ex_13_6_5_patternOccursBy pattern ω' n := by
  rcases hOcc with ⟨t, htn, ht⟩
  exact
    ⟨t, htn,
      ex_13_6_5_patternOccursAt_of_historyBefore_eq htn hHist ht⟩

theorem ex_13_6_5_firstOccurrence_le_of_historyBefore_eq
    {pattern : List ex_13_6_5_Key}
    {ω ω' : ex_13_6_5_TypingPath} {n : ℕ}
    (hHist :
      ex_13_6_5_keyHistoryBefore n ω =
        ex_13_6_5_keyHistoryBefore n ω')
    (hLe : ex_13_6_5_firstOccurrence pattern ω ≤ (n : WithTop ℕ)) :
    ex_13_6_5_firstOccurrence pattern ω' ≤ (n : WithTop ℕ) := by
  rw [ex_13_6_5_firstOccurrence_le_iff_occursBy] at hLe ⊢
  exact ex_13_6_5_patternOccursBy_of_historyBefore_eq hHist hLe

theorem ex_13_6_5_firstOccurrence_stoppingTimeBefore
    (pattern : List ex_13_6_5_Key) :
    def_13_8 ex_13_6_5_typingNaturalFiltrationBefore
      (ex_13_6_5_firstOccurrence pattern) := by
  refine ⟨ex_13_6_5_typingNaturalFiltrationBefore_isFiltration_ambient, ?_⟩
  intro n
  rw [ex_13_6_5_typingNaturalFiltrationBefore,
    ex_13_6_5_keyHistoryBeforeSigma,
    MeasurableSpace.measurableSet_comap]
  let eventHist : Set (Fin n → ex_13_6_5_Key) :=
    {hist | ∃ ω : ex_13_6_5_TypingPath,
      ex_13_6_5_keyHistoryBefore n ω = hist ∧
        ex_13_6_5_firstOccurrence pattern ω ≤ (n : WithTop ℕ)}
  refine ⟨eventHist, by trivial, ?_⟩
  ext ω
  constructor
  · rintro ⟨ω', hHist, hω'⟩
    exact ex_13_6_5_firstOccurrence_le_of_historyBefore_eq hHist hω'
  · intro hω
    exact ⟨ω, rfl, hω⟩

def ex_13_6_5_ababFirstOccurrence :
    ex_13_6_5_TypingPath → WithTop ℕ :=
  ex_13_6_5_firstOccurrence ex_13_6_5_pattern_abab

def ex_13_6_5_aabbFirstOccurrence :
    ex_13_6_5_TypingPath → WithTop ℕ :=
  ex_13_6_5_firstOccurrence ex_13_6_5_pattern_aabb



def ex_13_6_5_waitingTimeOf
    (T : ex_13_6_5_TypingPath → WithTop ℕ) :
    ex_13_6_5_TypingPath → ℕ :=
  fun ω =>
    match T ω with
    | none => 0
    | some n => n

def ex_13_6_5_ababWaitingTime :
    ex_13_6_5_TypingPath → ℕ :=
  ex_13_6_5_waitingTimeOf ex_13_6_5_ababFirstOccurrence

def ex_13_6_5_aabbWaitingTime :
    ex_13_6_5_TypingPath → ℕ :=
  ex_13_6_5_waitingTimeOf ex_13_6_5_aabbFirstOccurrence

theorem ex_13_6_5_waitingTimeOf_eq_of_firstOccurrence_eq
    {T : ex_13_6_5_TypingPath → WithTop ℕ}
    {ω : ex_13_6_5_TypingPath} {t : ℕ}
    (hT : T ω = (t : WithTop ℕ)) :
    ex_13_6_5_waitingTimeOf T ω = t := by
  simp [ex_13_6_5_waitingTimeOf, hT]

theorem ex_13_6_5_firstOccurrence_eq_waitingTimeOf_of_finite
    {T : ex_13_6_5_TypingPath → WithTop ℕ}
    {ω : ex_13_6_5_TypingPath} (hFinite : T ω ≠ ⊤) :
    T ω = (ex_13_6_5_waitingTimeOf T ω : WithTop ℕ) := by
  cases hT : T ω with
  | top =>
      exact False.elim (hFinite (by simpa [hT]))
  | coe n =>
      simp [ex_13_6_5_waitingTimeOf, hT]

theorem ex_13_6_5_ababFirstOccurrence_stoppingTime :
    def_13_8 ex_13_6_5_typingNaturalFiltration
      ex_13_6_5_ababFirstOccurrence :=
  ex_13_6_5_firstOccurrence_stoppingTime ex_13_6_5_pattern_abab

theorem ex_13_6_5_ababFirstOccurrence_stoppingTimeBefore :
    def_13_8 ex_13_6_5_typingNaturalFiltrationBefore
      ex_13_6_5_ababFirstOccurrence :=
  ex_13_6_5_firstOccurrence_stoppingTimeBefore ex_13_6_5_pattern_abab

theorem ex_13_6_5_aabbFirstOccurrence_stoppingTime :
    def_13_8 ex_13_6_5_typingNaturalFiltration
      ex_13_6_5_aabbFirstOccurrence :=
  ex_13_6_5_firstOccurrence_stoppingTime ex_13_6_5_pattern_aabb

theorem ex_13_6_5_aabbFirstOccurrence_stoppingTimeBefore :
    def_13_8 ex_13_6_5_typingNaturalFiltrationBefore
      ex_13_6_5_aabbFirstOccurrence :=
  ex_13_6_5_firstOccurrence_stoppingTimeBefore ex_13_6_5_pattern_aabb

theorem ex_13_6_5_concrete_firstOccurrence_stoppingTimes :
    def_13_8 ex_13_6_5_typingNaturalFiltration
        ex_13_6_5_ababFirstOccurrence ∧
      def_13_8 ex_13_6_5_typingNaturalFiltration
        ex_13_6_5_aabbFirstOccurrence :=
  ⟨ex_13_6_5_ababFirstOccurrence_stoppingTime,
    ex_13_6_5_aabbFirstOccurrence_stoppingTime⟩

theorem ex_13_6_5_abab_patternOccursAt_of_wordEvent
    {ω : ex_13_6_5_TypingPath} {k : ℕ}
    (h :
      ω ∈ wordEvent (α := ex_13_6_5_Key) 4
        ex_13_6_5_ababWordFin k) :
    ex_13_6_5_patternOccursAt ex_13_6_5_pattern_abab ω
      (k * 4 + 4) := by
  have hBlock :
      blockMap (α := ex_13_6_5_Key) 4 k ω =
        ex_13_6_5_ababWordFin := by
    simpa [wordEvent] using h
  constructor
  · simp [ex_13_6_5_pattern_abab]
  · intro i
    fin_cases i
    · simpa [blockMap, ex_13_6_5_ababWordFin,
        ex_13_6_5_pattern_abab] using congrFun hBlock (0 : Fin 4)
    · simpa [blockMap, ex_13_6_5_ababWordFin,
        ex_13_6_5_pattern_abab] using congrFun hBlock (1 : Fin 4)
    · simpa [blockMap, ex_13_6_5_ababWordFin,
        ex_13_6_5_pattern_abab] using congrFun hBlock (2 : Fin 4)
    · simpa [blockMap, ex_13_6_5_ababWordFin,
        ex_13_6_5_pattern_abab] using congrFun hBlock (3 : Fin 4)

theorem ex_13_6_5_aabb_patternOccursAt_of_wordEvent
    {ω : ex_13_6_5_TypingPath} {k : ℕ}
    (h :
      ω ∈ wordEvent (α := ex_13_6_5_Key) 4
        ex_13_6_5_aabbWordFin k) :
    ex_13_6_5_patternOccursAt ex_13_6_5_pattern_aabb ω
      (k * 4 + 4) := by
  have hBlock :
      blockMap (α := ex_13_6_5_Key) 4 k ω =
        ex_13_6_5_aabbWordFin := by
    simpa [wordEvent] using h
  constructor
  · simp [ex_13_6_5_pattern_aabb]
  · intro i
    fin_cases i
    · simpa [blockMap, ex_13_6_5_aabbWordFin,
        ex_13_6_5_pattern_aabb] using congrFun hBlock (0 : Fin 4)
    · simpa [blockMap, ex_13_6_5_aabbWordFin,
        ex_13_6_5_pattern_aabb] using congrFun hBlock (1 : Fin 4)
    · simpa [blockMap, ex_13_6_5_aabbWordFin,
        ex_13_6_5_pattern_aabb] using congrFun hBlock (2 : Fin 4)
    · simpa [blockMap, ex_13_6_5_aabbWordFin,
        ex_13_6_5_pattern_aabb] using congrFun hBlock (3 : Fin 4)

theorem ex_13_6_5_ababFirstOccurrence_finite_of_wordEvent
    {ω : ex_13_6_5_TypingPath} {k : ℕ}
    (h :
      ω ∈ wordEvent (α := ex_13_6_5_Key) 4
        ex_13_6_5_ababWordFin k) :
    ex_13_6_5_ababFirstOccurrence ω < ⊤ := by
  have hOccursAt :
      ex_13_6_5_patternOccursAt ex_13_6_5_pattern_abab ω
        (k * 4 + 4) :=
    ex_13_6_5_abab_patternOccursAt_of_wordEvent h
  have hOccursBy :
      ex_13_6_5_patternOccursBy ex_13_6_5_pattern_abab ω
        (k * 4 + 4) :=
    ⟨k * 4 + 4, le_rfl, hOccursAt⟩
  have hLe :
      ex_13_6_5_ababFirstOccurrence ω ≤
        ((k * 4 + 4 : ℕ) : WithTop ℕ) := by
    simpa [ex_13_6_5_ababFirstOccurrence] using
      (ex_13_6_5_firstOccurrence_le_iff_occursBy
        ex_13_6_5_pattern_abab ω (k * 4 + 4)).2 hOccursBy
  exact lt_of_le_of_lt hLe (WithTop.coe_lt_top (k * 4 + 4))

theorem ex_13_6_5_aabbFirstOccurrence_finite_of_wordEvent
    {ω : ex_13_6_5_TypingPath} {k : ℕ}
    (h :
      ω ∈ wordEvent (α := ex_13_6_5_Key) 4
        ex_13_6_5_aabbWordFin k) :
    ex_13_6_5_aabbFirstOccurrence ω < ⊤ := by
  have hOccursAt :
      ex_13_6_5_patternOccursAt ex_13_6_5_pattern_aabb ω
        (k * 4 + 4) :=
    ex_13_6_5_aabb_patternOccursAt_of_wordEvent h
  have hOccursBy :
      ex_13_6_5_patternOccursBy ex_13_6_5_pattern_aabb ω
        (k * 4 + 4) :=
    ⟨k * 4 + 4, le_rfl, hOccursAt⟩
  have hLe :
      ex_13_6_5_aabbFirstOccurrence ω ≤
        ((k * 4 + 4 : ℕ) : WithTop ℕ) := by
    simpa [ex_13_6_5_aabbFirstOccurrence] using
      (ex_13_6_5_firstOccurrence_le_iff_occursBy
        ex_13_6_5_pattern_aabb ω (k * 4 + 4)).2 hOccursBy
  exact lt_of_le_of_lt hLe (WithTop.coe_lt_top (k * 4 + 4))

theorem ex_13_6_5_ababFirstOccurrence_finite_ae :
    ∀ᵐ ω ∂ex_13_6_5_typingMeasure,
      ex_13_6_5_ababFirstOccurrence ω < ⊤ := by
  let s : ℕ → Set ex_13_6_5_TypingPath :=
    wordEvent (α := ex_13_6_5_Key) 4 ex_13_6_5_ababWordFin
  have hBC :
      ex_13_6_5_typingMeasure (limsup s atTop) = 1 := by
    simpa [s, ex_13_6_5_typingMeasure, ex_13_6_5_keyMeasure,
      typingMeasure, alphabetMeasure] using
      (typingMeasure_limsup_wordEvent_eq_one (α := ex_13_6_5_Key) (n := 4)
        ex_13_6_5_ababWordFin)
  have hMeas : MeasurableSet (limsup s atTop) := by
    exact MeasurableSet.measurableSet_limsup
      (fun k => measurableSet_wordEvent
        (α := ex_13_6_5_Key) (n := 4)
        ex_13_6_5_ababWordFin k)
  have hAELimsup : limsup s atTop ∈ ae ex_13_6_5_typingMeasure :=
    (mem_ae_iff_prob_eq_one hMeas).2 hBC
  filter_upwards [hAELimsup] with ω hω
  rcases (mem_limsup_iff_frequently_mem.mp hω).exists with ⟨k, hk⟩
  exact ex_13_6_5_ababFirstOccurrence_finite_of_wordEvent
    (ω := ω) (k := k) hk

theorem ex_13_6_5_aabbFirstOccurrence_finite_ae :
    ∀ᵐ ω ∂ex_13_6_5_typingMeasure,
      ex_13_6_5_aabbFirstOccurrence ω < ⊤ := by
  let s : ℕ → Set ex_13_6_5_TypingPath :=
    wordEvent (α := ex_13_6_5_Key) 4 ex_13_6_5_aabbWordFin
  have hBC :
      ex_13_6_5_typingMeasure (limsup s atTop) = 1 := by
    simpa [s, ex_13_6_5_typingMeasure, ex_13_6_5_keyMeasure,
      typingMeasure, alphabetMeasure] using
      (typingMeasure_limsup_wordEvent_eq_one (α := ex_13_6_5_Key) (n := 4)
        ex_13_6_5_aabbWordFin)
  have hMeas : MeasurableSet (limsup s atTop) := by
    exact MeasurableSet.measurableSet_limsup
      (fun k => measurableSet_wordEvent
        (α := ex_13_6_5_Key) (n := 4)
        ex_13_6_5_aabbWordFin k)
  have hAELimsup : limsup s atTop ∈ ae ex_13_6_5_typingMeasure :=
    (mem_ae_iff_prob_eq_one hMeas).2 hBC
  filter_upwards [hAELimsup] with ω hω
  rcases (mem_limsup_iff_frequently_mem.mp hω).exists with ⟨k, hk⟩
  exact ex_13_6_5_aabbFirstOccurrence_finite_of_wordEvent
    (ω := ω) (k := k) hk

theorem ex_13_6_5_iidWord_block_miss_prefix_measure
    {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {n : ℕ} [NeZero n]
    (w : Fin n → α) (m : ℕ) :
    typingMeasure (α := α)
        (⋂ k ∈ Finset.range m, (wordEvent (α := α) n w k)ᶜ) =
      (1 - ((Fintype.card α : ℝ≥0∞)⁻¹) ^ n) ^ m := by
  have hEq :=
    (iIndepFun_blockMap (α := α) (n := n)).meas_biInter
      (S := Finset.range m)
      (s := fun k => (wordEvent (α := α) n w k)ᶜ)
      (m := fun _ : ℕ => inferInstance)
      (f := blockMap (α := α) n)
      (μ := typingMeasure (α := α))
      ?_
  · rw [hEq]
    calc
      ∏ i ∈ Finset.range m,
          typingMeasure (α := α) ((wordEvent (α := α) n w i)ᶜ) =
          ∏ _i ∈ Finset.range m,
            (1 - ((Fintype.card α : ℝ≥0∞)⁻¹) ^ n) := by
            apply Finset.prod_congr rfl
            intro i _hi
            rw [prob_compl_eq_one_sub
              (measurableSet_wordEvent (α := α) (n := n) w i)]
            rw [typingMeasure_wordEvent]
      _ = (1 - ((Fintype.card α : ℝ≥0∞)⁻¹) ^ n) ^ m := by
        simp
  · intro k _hk
    change
      @MeasurableSet (ℕ → α)
        (MeasurableSpace.comap (blockMap (α := α) n k) inferInstance)
        (((blockMap (α := α) n k) ⁻¹'
          ({w} : Set (Fin n → α)))ᶜ)
    exact MeasurableSet.compl
      (MeasurableSpace.measurableSet_comap.mpr
        ⟨{w}, measurableSet_singleton w, rfl⟩)

theorem ex_13_6_5_abab_block_miss_prefix_measure (m : ℕ) :
    ex_13_6_5_typingMeasure
        (⋂ k ∈ Finset.range m,
          (wordEvent (α := ex_13_6_5_Key) 4
            ex_13_6_5_ababWordFin k)ᶜ) =
      (1 - (3 : ℝ≥0∞)⁻¹ ^ (4 : ℕ)) ^ m := by
  have hcard : Fintype.card ex_13_6_5_Key = 3 := by
    decide
  simpa [ex_13_6_5_typingMeasure, ex_13_6_5_keyMeasure,
    typingMeasure, alphabetMeasure, hcard] using
    (ex_13_6_5_iidWord_block_miss_prefix_measure
      (α := ex_13_6_5_Key) (n := 4)
      ex_13_6_5_ababWordFin m)

theorem ex_13_6_5_aabb_block_miss_prefix_measure (m : ℕ) :
    ex_13_6_5_typingMeasure
        (⋂ k ∈ Finset.range m,
          (wordEvent (α := ex_13_6_5_Key) 4
            ex_13_6_5_aabbWordFin k)ᶜ) =
      (1 - (3 : ℝ≥0∞)⁻¹ ^ (4 : ℕ)) ^ m := by
  have hcard : Fintype.card ex_13_6_5_Key = 3 := by
    decide
  simpa [ex_13_6_5_typingMeasure, ex_13_6_5_keyMeasure,
    typingMeasure, alphabetMeasure, hcard] using
    (ex_13_6_5_iidWord_block_miss_prefix_measure
      (α := ex_13_6_5_Key) (n := 4)
      ex_13_6_5_aabbWordFin m)

theorem ex_13_6_5_ababFirstOccurrence_le_of_wordEvent
    {ω : ex_13_6_5_TypingPath} {k : ℕ}
    (h :
      ω ∈ wordEvent (α := ex_13_6_5_Key) 4
        ex_13_6_5_ababWordFin k) :
    ex_13_6_5_ababFirstOccurrence ω ≤
      ((k * 4 + 4 : ℕ) : WithTop ℕ) := by
  have hOccursAt :
      ex_13_6_5_patternOccursAt ex_13_6_5_pattern_abab ω
        (k * 4 + 4) :=
    ex_13_6_5_abab_patternOccursAt_of_wordEvent h
  have hOccursBy :
      ex_13_6_5_patternOccursBy ex_13_6_5_pattern_abab ω
        (k * 4 + 4) :=
    ⟨k * 4 + 4, le_rfl, hOccursAt⟩
  simpa [ex_13_6_5_ababFirstOccurrence] using
    (ex_13_6_5_firstOccurrence_le_iff_occursBy
      ex_13_6_5_pattern_abab ω (k * 4 + 4)).2 hOccursBy

theorem ex_13_6_5_aabbFirstOccurrence_le_of_wordEvent
    {ω : ex_13_6_5_TypingPath} {k : ℕ}
    (h :
      ω ∈ wordEvent (α := ex_13_6_5_Key) 4
        ex_13_6_5_aabbWordFin k) :
    ex_13_6_5_aabbFirstOccurrence ω ≤
      ((k * 4 + 4 : ℕ) : WithTop ℕ) := by
  have hOccursAt :
      ex_13_6_5_patternOccursAt ex_13_6_5_pattern_aabb ω
        (k * 4 + 4) :=
    ex_13_6_5_aabb_patternOccursAt_of_wordEvent h
  have hOccursBy :
      ex_13_6_5_patternOccursBy ex_13_6_5_pattern_aabb ω
        (k * 4 + 4) :=
    ⟨k * 4 + 4, le_rfl, hOccursAt⟩
  simpa [ex_13_6_5_aabbFirstOccurrence] using
    (ex_13_6_5_firstOccurrence_le_iff_occursBy
      ex_13_6_5_pattern_aabb ω (k * 4 + 4)).2 hOccursBy

theorem ex_13_6_5_ababWaitingTime_tail_subset_block_miss
    (m : ℕ) :
    {ω : ex_13_6_5_TypingPath |
      4 * m < ex_13_6_5_ababWaitingTime ω} ⊆
      ⋂ k ∈ Finset.range m,
        (wordEvent (α := ex_13_6_5_Key) 4
          ex_13_6_5_ababWordFin k)ᶜ := by
  intro ω hTail
  simp only [Set.mem_iInter, Set.mem_compl_iff]
  intro k hk hBlock
  have hFinite :
      ex_13_6_5_ababFirstOccurrence ω ≠ ⊤ :=
    ne_of_lt (ex_13_6_5_ababFirstOccurrence_finite_of_wordEvent hBlock)
  have hT_eq :
      ex_13_6_5_ababFirstOccurrence ω =
        (ex_13_6_5_ababWaitingTime ω : WithTop ℕ) :=
    ex_13_6_5_firstOccurrence_eq_waitingTimeOf_of_finite
      (T := ex_13_6_5_ababFirstOccurrence) hFinite
  have hLe :
      (ex_13_6_5_ababWaitingTime ω : WithTop ℕ) ≤
        ((k * 4 + 4 : ℕ) : WithTop ℕ) := by
    rw [← hT_eq]
    exact ex_13_6_5_ababFirstOccurrence_le_of_wordEvent hBlock
  have hLeNat :
      ex_13_6_5_ababWaitingTime ω ≤ k * 4 + 4 :=
    WithTop.coe_le_coe.mp hLe
  have hk_lt : k < m := Finset.mem_range.mp hk
  have hBound : k * 4 + 4 ≤ 4 * m := by
    omega
  exact (not_lt_of_ge (hLeNat.trans hBound)) hTail

theorem ex_13_6_5_aabbWaitingTime_tail_subset_block_miss
    (m : ℕ) :
    {ω : ex_13_6_5_TypingPath |
      4 * m < ex_13_6_5_aabbWaitingTime ω} ⊆
      ⋂ k ∈ Finset.range m,
        (wordEvent (α := ex_13_6_5_Key) 4
          ex_13_6_5_aabbWordFin k)ᶜ := by
  intro ω hTail
  simp only [Set.mem_iInter, Set.mem_compl_iff]
  intro k hk hBlock
  have hFinite :
      ex_13_6_5_aabbFirstOccurrence ω ≠ ⊤ :=
    ne_of_lt (ex_13_6_5_aabbFirstOccurrence_finite_of_wordEvent hBlock)
  have hT_eq :
      ex_13_6_5_aabbFirstOccurrence ω =
        (ex_13_6_5_aabbWaitingTime ω : WithTop ℕ) :=
    ex_13_6_5_firstOccurrence_eq_waitingTimeOf_of_finite
      (T := ex_13_6_5_aabbFirstOccurrence) hFinite
  have hLe :
      (ex_13_6_5_aabbWaitingTime ω : WithTop ℕ) ≤
        ((k * 4 + 4 : ℕ) : WithTop ℕ) := by
    rw [← hT_eq]
    exact ex_13_6_5_aabbFirstOccurrence_le_of_wordEvent hBlock
  have hLeNat :
      ex_13_6_5_aabbWaitingTime ω ≤ k * 4 + 4 :=
    WithTop.coe_le_coe.mp hLe
  have hk_lt : k < m := Finset.mem_range.mp hk
  have hBound : k * 4 + 4 ≤ 4 * m := by
    omega
  exact (not_lt_of_ge (hLeNat.trans hBound)) hTail

theorem ex_13_6_5_ababWaitingTime_tail_measure_le
    (m : ℕ) :
    ex_13_6_5_typingMeasure
        {ω : ex_13_6_5_TypingPath |
          4 * m < ex_13_6_5_ababWaitingTime ω} ≤
      (1 - (3 : ℝ≥0∞)⁻¹ ^ (4 : ℕ)) ^ m := by
  calc
    ex_13_6_5_typingMeasure
        {ω : ex_13_6_5_TypingPath |
          4 * m < ex_13_6_5_ababWaitingTime ω} ≤
        ex_13_6_5_typingMeasure
          (⋂ k ∈ Finset.range m,
            (wordEvent (α := ex_13_6_5_Key) 4
              ex_13_6_5_ababWordFin k)ᶜ) :=
          measure_mono
            (ex_13_6_5_ababWaitingTime_tail_subset_block_miss m)
    _ = (1 - (3 : ℝ≥0∞)⁻¹ ^ (4 : ℕ)) ^ m :=
          ex_13_6_5_abab_block_miss_prefix_measure m

theorem ex_13_6_5_aabbWaitingTime_tail_measure_le
    (m : ℕ) :
    ex_13_6_5_typingMeasure
        {ω : ex_13_6_5_TypingPath |
          4 * m < ex_13_6_5_aabbWaitingTime ω} ≤
      (1 - (3 : ℝ≥0∞)⁻¹ ^ (4 : ℕ)) ^ m := by
  calc
    ex_13_6_5_typingMeasure
        {ω : ex_13_6_5_TypingPath |
          4 * m < ex_13_6_5_aabbWaitingTime ω} ≤
        ex_13_6_5_typingMeasure
          (⋂ k ∈ Finset.range m,
            (wordEvent (α := ex_13_6_5_Key) 4
              ex_13_6_5_aabbWordFin k)ᶜ) :=
          measure_mono
            (ex_13_6_5_aabbWaitingTime_tail_subset_block_miss m)
    _ = (1 - (3 : ℝ≥0∞)⁻¹ ^ (4 : ℕ)) ^ m :=
          ex_13_6_5_aabb_block_miss_prefix_measure m



def ex_13_6_5_blockMissRatio : ℝ≥0∞ :=
  1 - (3 : ℝ≥0∞)⁻¹ ^ (4 : ℕ)

theorem ex_13_6_5_blockMissRatio_lt_one :
    ex_13_6_5_blockMissRatio < 1 := by
  unfold ex_13_6_5_blockMissRatio
  apply ENNReal.sub_lt_self
  · simp
  · simp
  · exact pow_ne_zero 4 (by simp : ((3 : ℝ≥0∞)⁻¹) ≠ 0)

theorem ex_13_6_5_nat_geometric_block_tail_integrable
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℕ} {q : ℝ≥0∞}
    (hTailMeas : ∀ n : ℕ, MeasurableSet {ω : α | n < f ω})
    (hq : q < 1)
    (hTail : ∀ m : ℕ, μ {ω : α | 4 * m < f ω} ≤ q ^ m) :
    Integrable (fun ω => (f ω : ℝ)) μ := by
  have hNatTail :
      ∀ N : ℕ, (N : ℝ≥0∞) =
        ∑' n : ℕ, if n < N then (1 : ℝ≥0∞) else 0 := by
    intro N
    symm
    rw [tsum_eq_sum (s := Finset.range N)]
    · calc
        (∑ b ∈ Finset.range N,
            if b < N then (1 : ℝ≥0∞) else 0) =
            ∑ b ∈ Finset.range N, (1 : ℝ≥0∞) := by
              apply Finset.sum_congr rfl
              intro b hb
              simp [Finset.mem_range.mp hb]
        _ = (N : ℝ≥0∞) := by simp
    · intro n hn
      have hnle : N ≤ n := by
        simpa [Finset.mem_range] using hn
      simp [not_lt_of_ge hnle]
  have hPoint :
      (fun ω : α => ENNReal.ofReal (f ω : ℝ)) =
        fun ω : α =>
          ∑' n : ℕ,
            Set.indicator {ω : α | n < f ω}
              (fun _ => (1 : ℝ≥0∞)) ω := by
    funext ω
    calc
      ENNReal.ofReal (f ω : ℝ) = (f ω : ℝ≥0∞) := by
        exact ENNReal.ofReal_natCast (f ω)
      _ = ∑' n : ℕ, if n < f ω then (1 : ℝ≥0∞) else 0 :=
        hNatTail (f ω)
      _ = ∑' n : ℕ,
            Set.indicator {ω : α | n < f ω}
              (fun _ => (1 : ℝ≥0∞)) ω := by
        apply tsum_congr
        intro n
        by_cases hn : n < f ω <;> simp [Set.indicator, hn]
  have hIntegral_le :
      ∫⁻ ω, ENNReal.ofReal (f ω : ℝ) ∂μ ≤
        ∑' n : ℕ, q ^ (n / 4) := by
    calc
      ∫⁻ ω, ENNReal.ofReal (f ω : ℝ) ∂μ =
          ∫⁻ ω, ∑' n : ℕ,
            Set.indicator {ω : α | n < f ω}
              (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
            rw [hPoint]
      _ = ∑' n : ℕ,
            ∫⁻ ω, Set.indicator {ω : α | n < f ω}
              (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
            rw [lintegral_tsum]
            intro n
            exact (measurable_const.indicator (hTailMeas n)).aemeasurable
      _ = ∑' n : ℕ, μ {ω : α | n < f ω} := by
            apply tsum_congr
            intro n
            simp [lintegral_indicator_const (hTailMeas n)]
      _ ≤ ∑' n : ℕ, q ^ (n / 4) := by
            apply ENNReal.tsum_le_tsum
            intro n
            have hsubset :
                {ω : α | n < f ω} ⊆ {ω : α | 4 * (n / 4) < f ω} := by
              intro ω hω
              have hle : 4 * (n / 4) ≤ n := by
                rw [mul_comm]
                exact Nat.div_mul_le_self n 4
              exact lt_of_le_of_lt hle hω
            exact (measure_mono hsubset).trans (hTail (n / 4))
  have hGeomFinite : (∑' n : ℕ, q ^ (n / 4)) < ⊤ := by
    have hsub_pos : 0 < (1 - q) := tsub_pos_iff_lt.mpr hq
    have hgeom : (∑' n : ℕ, q ^ n) < ⊤ := by
      rw [ENNReal.tsum_geometric]
      rw [lt_top_iff_ne_top]
      simp [ne_of_gt hsub_pos]
    have hdiv :
        (∑' n : ℕ, q ^ (n / 4)) =
          ∑' p : ℕ × Fin 4, q ^ p.1 := by
      simpa using
        ((Nat.divModEquiv 4).tsum_eq
          (fun p : ℕ × Fin 4 => q ^ p.1))
    rw [hdiv, ENNReal.tsum_prod']
    calc
      (∑' (a : ℕ), ∑' (b : Fin 4), q ^ a) =
          ∑' a : ℕ, (4 : ℝ≥0∞) * q ^ a := by
            apply tsum_congr
            intro a
            simp [tsum_fintype, Finset.sum_const, nsmul_eq_mul]
      _ = (4 : ℝ≥0∞) * ∑' a : ℕ, q ^ a := by
            rw [ENNReal.tsum_mul_left]
      _ < ⊤ := by
            exact ENNReal.mul_lt_top (by simp) hgeom
  have hlin_ne_top :
      ∫⁻ ω, ENNReal.ofReal (f ω : ℝ) ∂μ ≠ ∞ :=
    ne_top_of_le_ne_top hGeomFinite.ne hIntegral_le
  have hLevel : ∀ n : ℕ, MeasurableSet {ω : α | f ω = n} := by
    intro n
    cases n with
    | zero =>
        have hEq : {ω : α | f ω = 0} = {ω : α | ¬ 0 < f ω} := by
          ext ω
          constructor
          · intro hω
            have hval : f ω = 0 := by
              simpa using hω
            simpa [hval]
          · intro hω
            have hpos : ¬ 0 < f ω := by
              simpa using hω
            exact Nat.eq_zero_of_not_pos hpos
        rw [hEq]
        exact (hTailMeas 0).compl
    | succ k =>
        have hEq :
            {ω : α | f ω = Nat.succ k} =
              {ω : α | k < f ω} ∩ {ω : α | ¬ Nat.succ k < f ω} := by
          ext ω
          constructor
          · intro hω
            have hval : f ω = Nat.succ k := by
              simpa using hω
            constructor
            · simpa [hval] using Nat.lt_succ_self k
            · simpa [hval] using Nat.not_succ_lt_self k
          · rintro ⟨hk, hnot⟩
            have hk' : k < f ω := by
              simpa using hk
            have hnot' : ¬ Nat.succ k < f ω := by
              simpa using hnot
            exact le_antisymm (le_of_not_gt hnot') (Nat.succ_le_of_lt hk')
        rw [hEq]
        exact (hTailMeas k).inter (hTailMeas (Nat.succ k)).compl
  have hf_meas : Measurable f := by
    apply measurable_to_nat
    intro y
    simpa [Set.preimage, Set.mem_setOf_eq] using hLevel (f y)
  have hf_aesm_nat : AEStronglyMeasurable f μ :=
    hf_meas.aestronglyMeasurable
  have hf_aesm_real : AEStronglyMeasurable (fun ω => (f ω : ℝ)) μ :=
    Nat.cast_continuous.comp_aestronglyMeasurable hf_aesm_nat
  exact
    (lintegral_ofReal_ne_top_iff_integrable
      hf_aesm_real
      (Eventually.of_forall fun ω => Nat.cast_nonneg (f ω))).1
      hlin_ne_top

theorem ex_13_6_5_waitingTimeOf_tail_measurable
    {T : ex_13_6_5_TypingPath → WithTop ℕ}
    (hT : def_13_8 ex_13_6_5_typingNaturalFiltration T)
    (n : ℕ) :
    MeasurableSet
      {ω : ex_13_6_5_TypingPath |
        n < ex_13_6_5_waitingTimeOf T ω} := by
  have hLe :
      ∀ n : ℕ,
        MeasurableSet
          {ω : ex_13_6_5_TypingPath | T ω ≤ (n : WithTop ℕ)} := by
    intro n
    exact
      (MeasurableSpace.le_def.mp
        (ex_13_6_5_typingNaturalFiltration_le n))
        {ω : ex_13_6_5_TypingPath | T ω ≤ (n : WithTop ℕ)}
        (def_13_8_event_le_measurable hT n)
  have hFinite :
      MeasurableSet
        (⋃ m : ℕ,
          {ω : ex_13_6_5_TypingPath | T ω ≤ (m : WithTop ℕ)}) :=
    MeasurableSet.iUnion hLe
  have hEq :
      {ω : ex_13_6_5_TypingPath |
        n < ex_13_6_5_waitingTimeOf T ω} =
        (⋃ m : ℕ,
          {ω : ex_13_6_5_TypingPath | T ω ≤ (m : WithTop ℕ)}) ∩
          {ω : ex_13_6_5_TypingPath | ¬ T ω ≤ (n : WithTop ℕ)} := by
    ext ω
    cases hTω : T ω with
    | top =>
        simp [ex_13_6_5_waitingTimeOf, hTω]
    | coe k =>
        have hwait : ex_13_6_5_waitingTimeOf T ω = k := by
          rw [ex_13_6_5_waitingTimeOf, hTω]
        simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff,
          hwait, hTω]
        constructor
        · intro hnk
          constructor
          · exact ⟨k, by exact_mod_cast le_rfl⟩
          · intro hle
            have hleNat : k ≤ n := WithTop.coe_le_coe.mp hle
            omega
        · rintro ⟨_hfin, hnot⟩
          by_contra hle
          have hleNat : k ≤ n := le_of_not_gt hle
          exact hnot (WithTop.coe_le_coe.mpr hleNat)
  rw [hEq]
  exact hFinite.inter (hLe n).compl

theorem ex_13_6_5_ababWaitingTime_tail_measurable (n : ℕ) :
    MeasurableSet
      {ω : ex_13_6_5_TypingPath |
        n < ex_13_6_5_ababWaitingTime ω} := by
  simpa [ex_13_6_5_ababWaitingTime] using
    ex_13_6_5_waitingTimeOf_tail_measurable
      ex_13_6_5_ababFirstOccurrence_stoppingTime n

theorem ex_13_6_5_aabbWaitingTime_tail_measurable (n : ℕ) :
    MeasurableSet
      {ω : ex_13_6_5_TypingPath |
        n < ex_13_6_5_aabbWaitingTime ω} := by
  simpa [ex_13_6_5_aabbWaitingTime] using
    ex_13_6_5_waitingTimeOf_tail_measurable
      ex_13_6_5_aabbFirstOccurrence_stoppingTime n

theorem ex_13_6_5_ababWaitingTime_integrable :
    Integrable (fun ω : ex_13_6_5_TypingPath =>
      (ex_13_6_5_ababWaitingTime ω : ℝ))
      ex_13_6_5_typingMeasure := by
  refine
    ex_13_6_5_nat_geometric_block_tail_integrable
      (μ := ex_13_6_5_typingMeasure)
      (f := ex_13_6_5_ababWaitingTime)
      (q := ex_13_6_5_blockMissRatio)
      ex_13_6_5_ababWaitingTime_tail_measurable
      ex_13_6_5_blockMissRatio_lt_one ?_
  intro m
  simpa [ex_13_6_5_blockMissRatio] using
    ex_13_6_5_ababWaitingTime_tail_measure_le m

theorem ex_13_6_5_aabbWaitingTime_integrable :
    Integrable (fun ω : ex_13_6_5_TypingPath =>
      (ex_13_6_5_aabbWaitingTime ω : ℝ))
      ex_13_6_5_typingMeasure := by
  refine
    ex_13_6_5_nat_geometric_block_tail_integrable
      (μ := ex_13_6_5_typingMeasure)
      (f := ex_13_6_5_aabbWaitingTime)
      (q := ex_13_6_5_blockMissRatio)
      ex_13_6_5_aabbWaitingTime_tail_measurable
      ex_13_6_5_blockMissRatio_lt_one ?_
  intro m
  simpa [ex_13_6_5_blockMissRatio] using
    ex_13_6_5_aabbWaitingTime_tail_measure_le m

theorem ex_13_6_5_firstOccurrence_occursAt_of_eq
    {pattern : List ex_13_6_5_Key}
    {ω : ex_13_6_5_TypingPath} {t : ℕ}
    (hT : ex_13_6_5_firstOccurrence pattern ω = (t : WithTop ℕ)) :
    ex_13_6_5_patternOccursAt pattern ω t := by
  classical
  unfold ex_13_6_5_firstOccurrence at hT
  by_cases h : ∃ t : ℕ, ex_13_6_5_patternOccursAt pattern ω t
  · simp only [h, ↓reduceDIte] at hT
    have ht : Nat.find h = t := WithTop.coe_eq_coe.mp hT
    rw [← ht]
    exact Nat.find_spec h
  · simp only [h, ↓reduceDIte] at hT
    have hne : (⊤ : WithTop ℕ) ≠ (t : WithTop ℕ) := by simp
    exact False.elim (hne hT)

theorem ex_13_6_5_firstOccurrence_min_of_eq
    {pattern : List ex_13_6_5_Key}
    {ω : ex_13_6_5_TypingPath} {t u : ℕ}
    (hT : ex_13_6_5_firstOccurrence pattern ω = (t : WithTop ℕ))
    (hOcc : ex_13_6_5_patternOccursAt pattern ω u) :
    t ≤ u := by
  classical
  unfold ex_13_6_5_firstOccurrence at hT
  by_cases h : ∃ n : ℕ, ex_13_6_5_patternOccursAt pattern ω n
  · simp only [h, ↓reduceDIte] at hT
    have ht : Nat.find h = t := WithTop.coe_eq_coe.mp hT
    have hmin : Nat.find h ≤ u := Nat.find_min' h hOcc
    omega
  · exact False.elim (h ⟨u, hOcc⟩)



def ex_13_6_5_actualEntrantBankroll
    (pattern : List ex_13_6_5_Key) :
    ℕ → ex_13_6_5_TypingPath → ℝ := by
  classical
  exact fun n ω =>
    if ex_13_6_5_patternOccursAt pattern ω n then
      ex_13_6_5_entrantTerminalTeamGain (n : ℝ)
        (ex_13_6_5_terminalSurvivorWinLengthsFromPattern pattern)
    else
      0

theorem ex_13_6_5_abab_actual_stoppedBankroll_eq_terminalTeamGain
    (ω : ex_13_6_5_TypingPath) {t : ℕ}
    (hT : ex_13_6_5_ababFirstOccurrence ω = (t : WithTop ℕ)) :
    thm_13_18_stoppedValueReal
        (ex_13_6_5_actualEntrantBankroll ex_13_6_5_pattern_abab)
        ex_13_6_5_ababFirstOccurrence ω =
      ex_13_6_5_ababTerminalTeamGain (t : ℝ) := by
  have hOcc :
      ex_13_6_5_patternOccursAt ex_13_6_5_pattern_abab ω t :=
    ex_13_6_5_firstOccurrence_occursAt_of_eq hT
  change
    (match ex_13_6_5_ababFirstOccurrence ω with
      | none => 0
      | some n =>
          ex_13_6_5_actualEntrantBankroll
            ex_13_6_5_pattern_abab n ω) =
        ex_13_6_5_ababTerminalTeamGain (t : ℝ)
  rw [hT]
  simp [ex_13_6_5_actualEntrantBankroll, hOcc,
    ex_13_6_5_abab_concrete_stoppedValue_eq_terminalTeamGain]

theorem ex_13_6_5_aabb_actual_stoppedBankroll_eq_terminalTeamGain
    (ω : ex_13_6_5_TypingPath) {t : ℕ}
    (hT : ex_13_6_5_aabbFirstOccurrence ω = (t : WithTop ℕ)) :
    thm_13_18_stoppedValueReal
        (ex_13_6_5_actualEntrantBankroll ex_13_6_5_pattern_aabb)
        ex_13_6_5_aabbFirstOccurrence ω =
      ex_13_6_5_aabbTerminalTeamGain (t : ℝ) := by
  have hOcc :
      ex_13_6_5_patternOccursAt ex_13_6_5_pattern_aabb ω t :=
    ex_13_6_5_firstOccurrence_occursAt_of_eq hT
  change
    (match ex_13_6_5_aabbFirstOccurrence ω with
      | none => 0
      | some n =>
          ex_13_6_5_actualEntrantBankroll
            ex_13_6_5_pattern_aabb n ω) =
        ex_13_6_5_aabbTerminalTeamGain (t : ℝ)
  rw [hT]
  simp [ex_13_6_5_actualEntrantBankroll, hOcc,
    ex_13_6_5_aabb_concrete_stoppedValue_eq_terminalTeamGain]



def ex_13_6_5_ababActualActiveEntrantWinLengths
    (ω : ex_13_6_5_TypingPath) (t : ℕ) : List ℕ :=
  (if ω (t - 2) = ex_13_6_5_Key.a ∧
        ω (t - 1) = ex_13_6_5_Key.b then
      [2]
    else
      []) ++
    (if ω (t - 4) = ex_13_6_5_Key.a ∧
          ω (t - 3) = ex_13_6_5_Key.b ∧
          ω (t - 2) = ex_13_6_5_Key.a ∧
          ω (t - 1) = ex_13_6_5_Key.b then
        [4]
      else
        [])

theorem ex_13_6_5_ababActualActiveEntrantWinLengths_of_occursAt
    {ω : ex_13_6_5_TypingPath} {t : ℕ}
    (hOcc :
      ex_13_6_5_patternOccursAt ex_13_6_5_pattern_abab ω t) :
    ex_13_6_5_ababActualActiveEntrantWinLengths ω t = [2, 4] := by
  rcases hOcc with ⟨hlen, hletters⟩
  have ht : 4 ≤ t := by
    simpa [ex_13_6_5_pattern_abab] using hlen
  have h0 : ω (t - 4) = ex_13_6_5_Key.a := by
    have h := hletters ⟨0, by simp [ex_13_6_5_pattern_abab]⟩
    simpa [ex_13_6_5_pattern_abab] using h
  have h1 : ω (t - 3) = ex_13_6_5_Key.b := by
    have h := hletters ⟨1, by simp [ex_13_6_5_pattern_abab]⟩
    have hidx : t - 4 + 1 = t - 3 := by omega
    simpa [ex_13_6_5_pattern_abab, hidx] using h
  have h2 : ω (t - 2) = ex_13_6_5_Key.a := by
    have h := hletters ⟨2, by simp [ex_13_6_5_pattern_abab]⟩
    have hidx : t - 4 + 2 = t - 2 := by omega
    simpa [ex_13_6_5_pattern_abab, hidx] using h
  have h3 : ω (t - 1) = ex_13_6_5_Key.b := by
    have h := hletters ⟨3, by simp [ex_13_6_5_pattern_abab]⟩
    have hidx : t - 4 + 3 = t - 1 := by omega
    simpa [ex_13_6_5_pattern_abab, hidx] using h
  simp [ex_13_6_5_ababActualActiveEntrantWinLengths,
    h0, h1, h2, h3]

theorem ex_13_6_5_ababActualActiveEntrant_bankroll_eq_terminalGain
    (t : ℝ) :
    ex_13_6_5_entrantTerminalTeamGain t [2, 4] =
      ex_13_6_5_ababTerminalTeamGain t := by
  simp [ex_13_6_5_entrantTerminalTeamGain,
    ex_13_6_5_ababTerminalTeamGain,
    ex_13_6_5_ababSurvivorWinLengths,
    ex_13_6_5_losingEntrantsContribution,
    ex_13_6_5_gamblerNetAfterWins]
  ring



def ex_13_6_5_ababActualEntrantBankrollProcess :
    ℕ → ex_13_6_5_TypingPath → ℝ :=
  fun n ω =>
    ex_13_6_5_entrantTerminalTeamGain (n : ℝ)
      (ex_13_6_5_ababActualActiveEntrantWinLengths ω n)

theorem ex_13_6_5_abab_actual_entrant_bankroll_process_eq_terminal_gain
    (ω : ex_13_6_5_TypingPath) {t : ℕ}
    (hT : ex_13_6_5_ababFirstOccurrence ω = (t : WithTop ℕ)) :
    thm_13_18_stoppedValueReal
        ex_13_6_5_ababActualEntrantBankrollProcess
        ex_13_6_5_ababFirstOccurrence ω =
      ex_13_6_5_ababTerminalTeamGain (t : ℝ) := by
  have hOcc :
      ex_13_6_5_patternOccursAt ex_13_6_5_pattern_abab ω t :=
    ex_13_6_5_firstOccurrence_occursAt_of_eq hT
  have hSurvivors :
      ex_13_6_5_ababActualActiveEntrantWinLengths ω t = [2, 4] :=
    ex_13_6_5_ababActualActiveEntrantWinLengths_of_occursAt hOcc
  change
    (match ex_13_6_5_ababFirstOccurrence ω with
      | none => 0
      | some n => ex_13_6_5_ababActualEntrantBankrollProcess n ω) =
        ex_13_6_5_ababTerminalTeamGain (t : ℝ)
  rw [hT]
  simp [ex_13_6_5_ababActualEntrantBankrollProcess,
    hSurvivors,
    ex_13_6_5_ababActualActiveEntrant_bankroll_eq_terminalGain]



def ex_13_6_5_aabbActualActiveEntrantWinLengths
    (ω : ex_13_6_5_TypingPath) (t : ℕ) : List ℕ :=
  if ω (t - 4) = ex_13_6_5_Key.a ∧
      ω (t - 3) = ex_13_6_5_Key.a ∧
      ω (t - 2) = ex_13_6_5_Key.b ∧
      ω (t - 1) = ex_13_6_5_Key.b then
    [4]
  else
    []

theorem ex_13_6_5_aabbActualActiveEntrantWinLengths_of_occursAt
    {ω : ex_13_6_5_TypingPath} {t : ℕ}
    (hOcc :
      ex_13_6_5_patternOccursAt ex_13_6_5_pattern_aabb ω t) :
    ex_13_6_5_aabbActualActiveEntrantWinLengths ω t = [4] := by
  rcases hOcc with ⟨hlen, hletters⟩
  have ht : 4 ≤ t := by
    simpa [ex_13_6_5_pattern_aabb] using hlen
  have h0 : ω (t - 4) = ex_13_6_5_Key.a := by
    have h := hletters ⟨0, by simp [ex_13_6_5_pattern_aabb]⟩
    simpa [ex_13_6_5_pattern_aabb] using h
  have h1 : ω (t - 3) = ex_13_6_5_Key.a := by
    have h := hletters ⟨1, by simp [ex_13_6_5_pattern_aabb]⟩
    have hidx : t - 4 + 1 = t - 3 := by omega
    simpa [ex_13_6_5_pattern_aabb, hidx] using h
  have h2 : ω (t - 2) = ex_13_6_5_Key.b := by
    have h := hletters ⟨2, by simp [ex_13_6_5_pattern_aabb]⟩
    have hidx : t - 4 + 2 = t - 2 := by omega
    simpa [ex_13_6_5_pattern_aabb, hidx] using h
  have h3 : ω (t - 1) = ex_13_6_5_Key.b := by
    have h := hletters ⟨3, by simp [ex_13_6_5_pattern_aabb]⟩
    have hidx : t - 4 + 3 = t - 1 := by omega
    simpa [ex_13_6_5_pattern_aabb, hidx] using h
  simp [ex_13_6_5_aabbActualActiveEntrantWinLengths,
    h0, h1, h2, h3]

theorem ex_13_6_5_aabbActualActiveEntrant_bankroll_eq_terminalGain
    (t : ℝ) :
    ex_13_6_5_entrantTerminalTeamGain t [4] =
      ex_13_6_5_aabbTerminalTeamGain t := by
  simp [ex_13_6_5_entrantTerminalTeamGain,
    ex_13_6_5_aabbTerminalTeamGain,
    ex_13_6_5_aabbSurvivorWinLengths,
    ex_13_6_5_losingEntrantsContribution,
    ex_13_6_5_gamblerNetAfterWins]



def ex_13_6_5_aabbActualEntrantBankrollProcess :
    ℕ → ex_13_6_5_TypingPath → ℝ :=
  fun n ω =>
    ex_13_6_5_entrantTerminalTeamGain (n : ℝ)
      (ex_13_6_5_aabbActualActiveEntrantWinLengths ω n)

theorem ex_13_6_5_aabb_actual_entrant_bankroll_process_eq_terminal_gain
    (ω : ex_13_6_5_TypingPath) {t : ℕ}
    (hT : ex_13_6_5_aabbFirstOccurrence ω = (t : WithTop ℕ)) :
    thm_13_18_stoppedValueReal
        ex_13_6_5_aabbActualEntrantBankrollProcess
        ex_13_6_5_aabbFirstOccurrence ω =
      ex_13_6_5_aabbTerminalTeamGain (t : ℝ) := by
  have hOcc :
      ex_13_6_5_patternOccursAt ex_13_6_5_pattern_aabb ω t :=
    ex_13_6_5_firstOccurrence_occursAt_of_eq hT
  have hSurvivors :
      ex_13_6_5_aabbActualActiveEntrantWinLengths ω t = [4] :=
    ex_13_6_5_aabbActualActiveEntrantWinLengths_of_occursAt hOcc
  change
    (match ex_13_6_5_aabbFirstOccurrence ω with
      | none => 0
      | some n => ex_13_6_5_aabbActualEntrantBankrollProcess n ω) =
        ex_13_6_5_aabbTerminalTeamGain (t : ℝ)
  rw [hT]
  simp [ex_13_6_5_aabbActualEntrantBankrollProcess,
    hSurvivors,
    ex_13_6_5_aabbActualActiveEntrant_bankroll_eq_terminalGain]
