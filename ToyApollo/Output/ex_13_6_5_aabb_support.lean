/-
TASK ID: ex_13_6_5_aabb_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.ex_13_6_5_word_pattern_support

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

def ex_13_6_5_aabbPrefixMatches
    (ω : ex_13_6_5_TypingPath) (start wins : ℕ) : Prop :=
  wins ≤ ex_13_6_5_pattern_aabb.length ∧
    ex_13_6_5_lettersFromStart ω start wins =
      ex_13_6_5_pattern_aabb.take wins

theorem ex_13_6_5_aabbPrefixMatches_iff_wordFin
    {ω : ex_13_6_5_TypingPath} {start wins : ℕ} (hwins : wins ≤ 4) :
    ex_13_6_5_aabbPrefixMatches ω start wins ↔
      ex_13_6_5_wordFinPrefixMatches
        ex_13_6_5_aabbWordFin ω start wins := by
  interval_cases wins <;>
    simp [ex_13_6_5_aabbPrefixMatches,
      ex_13_6_5_wordFinPrefixMatches,
      ex_13_6_5_lettersFromStart,
      ex_13_6_5_pattern_aabb,
      ex_13_6_5_aabbWordFin]
  · constructor
    · intro h i hi
      fin_cases i <;> simp at hi ⊢
      · exact h.1
      · exact h.2
    · intro h
      exact ⟨h ⟨0, by norm_num⟩ (by norm_num),
        h ⟨1, by norm_num⟩ (by norm_num)⟩
  · constructor
    · intro h i hi
      fin_cases i <;> simp at hi ⊢
      · exact h.1
      · exact h.2.1
      · exact h.2.2
    · intro h
      exact ⟨h ⟨0, by norm_num⟩ (by norm_num),
        h ⟨1, by norm_num⟩ (by norm_num),
        h ⟨2, by norm_num⟩ (by norm_num)⟩
  · constructor
    · intro h i
      fin_cases i <;> simp [h.1, h.2.1, h.2.2.1, h.2.2.2]
    · intro h
      exact ⟨h ⟨0, by norm_num⟩,
        h ⟨1, by norm_num⟩,
        h ⟨2, by norm_num⟩,
        h ⟨3, by norm_num⟩⟩

theorem ex_13_6_5_aabbPrefixMatches_measurableSet
    (start wins : ℕ) (hwins : wins ≤ 4) :
    MeasurableSet
      {ω : ex_13_6_5_TypingPath |
        ex_13_6_5_aabbPrefixMatches ω start wins} := by
  rw [show
      {ω : ex_13_6_5_TypingPath |
        ex_13_6_5_aabbPrefixMatches ω start wins} =
      {ω : ex_13_6_5_TypingPath |
        ex_13_6_5_wordFinPrefixMatches
          ex_13_6_5_aabbWordFin ω start wins} by
    ext ω
    exact ex_13_6_5_aabbPrefixMatches_iff_wordFin
      (ω := ω) (start := start) (wins := wins) hwins]
  exact ex_13_6_5_wordFinPrefixMatches_measurableSet
    ex_13_6_5_aabbWordFin start wins hwins

theorem ex_13_6_5_aabbPrefixMatches_mem_naturalFiltration
    (n start wins : ℕ) (hwins : wins ≤ 4)
    (hidx : ∀ i : ℕ, i < wins → start + i ≤ n) :
    @MeasurableSet ex_13_6_5_TypingPath
      (ex_13_6_5_typingNaturalFiltration n)
      {ω : ex_13_6_5_TypingPath |
        ex_13_6_5_aabbPrefixMatches ω start wins} := by
  rw [show
      {ω : ex_13_6_5_TypingPath |
        ex_13_6_5_aabbPrefixMatches ω start wins} =
      {ω : ex_13_6_5_TypingPath |
        ex_13_6_5_wordFinPrefixMatches
          ex_13_6_5_aabbWordFin ω start wins} by
    ext ω
    exact ex_13_6_5_aabbPrefixMatches_iff_wordFin
      (ω := ω) (start := start) (wins := wins) hwins]
  exact ex_13_6_5_wordFinPrefixMatches_mem_naturalFiltration
    ex_13_6_5_aabbWordFin n start wins hwins hidx

def ex_13_6_5_aabbConcreteEntrantTerminalNet
    (ω : ex_13_6_5_TypingPath) (t start : ℕ) : ℝ := by
  classical
  exact
    if start < t then
      if start + 4 ≤ t then
        if ex_13_6_5_aabbPrefixMatches ω start 4 then
          ex_13_6_5_gamblerNetAfterWins 4
        else
          -1
      else
        let wins := t - start
        if ex_13_6_5_aabbPrefixMatches ω start wins then
          ex_13_6_5_gamblerNetAfterWins wins
        else
          -1
    else
      0

def ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess :
    ℕ → ex_13_6_5_TypingPath → ℝ :=
  fun n ω =>
    ∑ start ∈ Finset.range n,
      ex_13_6_5_aabbConcreteEntrantTerminalNet ω n start

theorem ex_13_6_5_aabbConcreteEntrantTerminalNet_stable_after_four
    {ω : ex_13_6_5_TypingPath} {n start : ℕ}
    (hDone : start + 4 ≤ n) :
    ex_13_6_5_aabbConcreteEntrantTerminalNet ω (n + 1) start =
      ex_13_6_5_aabbConcreteEntrantTerminalNet ω n start := by
  have hlt_n : start < n := by omega
  have hlt_succ : start < n + 1 := by omega
  have hDone_succ : start + 4 ≤ n + 1 := by omega
  by_cases hPrefix : ex_13_6_5_aabbPrefixMatches ω start 4
  · simp [ex_13_6_5_aabbConcreteEntrantTerminalNet,
      hlt_n, hlt_succ, hDone, hDone_succ, hPrefix]
  · simp [ex_13_6_5_aabbConcreteEntrantTerminalNet,
      hlt_n, hlt_succ, hDone, hDone_succ, hPrefix]

theorem ex_13_6_5_aabbConcreteEntrantTerminalNet_old_change_zero
    {ω : ex_13_6_5_TypingPath} {n start : ℕ}
    (hDone : start + 4 ≤ n) :
    ex_13_6_5_aabbConcreteEntrantTerminalNet ω (n + 1) start -
      ex_13_6_5_aabbConcreteEntrantTerminalNet ω n start = 0 := by
  rw [ex_13_6_5_aabbConcreteEntrantTerminalNet_stable_after_four hDone]
  ring

theorem ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_zero :
    ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess 0 =
      fun _ : ex_13_6_5_TypingPath => (0 : ℝ) := by
  funext ω
  simp [ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess]

theorem ex_13_6_5_aabbConcreteEntrantTerminalNet_abs_le
    (ω : ex_13_6_5_TypingPath) (t start : ℕ) :
    |ex_13_6_5_aabbConcreteEntrantTerminalNet ω t start| ≤ 80 := by
  classical
  by_cases hlt : start < t
  · by_cases hDone : start + 4 ≤ t
    · by_cases hPrefix : ex_13_6_5_aabbPrefixMatches ω start 4
      · simpa [ex_13_6_5_aabbConcreteEntrantTerminalNet, hlt, hDone,
          hPrefix] using
          (ex_13_6_5_gamblerNetAfterWins_abs_le_four
            (wins := 4) (by norm_num))
      · norm_num [ex_13_6_5_aabbConcreteEntrantTerminalNet, hlt, hDone,
          hPrefix]
    · by_cases hPrefix :
        ex_13_6_5_aabbPrefixMatches ω start (t - start)
      · have hwins : t - start ≤ 4 := by omega
        simpa [ex_13_6_5_aabbConcreteEntrantTerminalNet, hlt, hDone,
          hPrefix] using
          (ex_13_6_5_gamblerNetAfterWins_abs_le_four
            (wins := t - start) hwins)
      · norm_num [ex_13_6_5_aabbConcreteEntrantTerminalNet, hlt, hDone,
          hPrefix]
  · norm_num [ex_13_6_5_aabbConcreteEntrantTerminalNet, hlt]

theorem ex_13_6_5_aabbConcreteEntrantTerminalNet_measurable
    (t start : ℕ) :
    Measurable fun ω : ex_13_6_5_TypingPath =>
      ex_13_6_5_aabbConcreteEntrantTerminalNet ω t start := by
  classical
  by_cases hlt : start < t
  · by_cases hDone : start + 4 ≤ t
    · simp [ex_13_6_5_aabbConcreteEntrantTerminalNet, hlt, hDone]
      exact Measurable.ite
        (ex_13_6_5_aabbPrefixMatches_measurableSet start 4 (by norm_num))
        measurable_const measurable_const
    · have hwins : t - start ≤ 4 := by omega
      simp [ex_13_6_5_aabbConcreteEntrantTerminalNet, hlt, hDone]
      exact Measurable.ite
        (ex_13_6_5_aabbPrefixMatches_measurableSet start (t - start) hwins)
        measurable_const measurable_const
  · simp [ex_13_6_5_aabbConcreteEntrantTerminalNet, hlt]

theorem ex_13_6_5_aabbConcreteEntrantTerminalNet_measurable_naturalFiltration
    (t start : ℕ) :
    Measurable[ex_13_6_5_typingNaturalFiltration t]
      (fun ω : ex_13_6_5_TypingPath =>
        ex_13_6_5_aabbConcreteEntrantTerminalNet ω t start) := by
  classical
  by_cases hlt : start < t
  · by_cases hDone : start + 4 ≤ t
    · have hcoords : ∀ i : ℕ, i < 4 → start + i ≤ t := by
        intro i hi
        omega
      simp [ex_13_6_5_aabbConcreteEntrantTerminalNet, hlt, hDone]
      exact Measurable.ite
        (ex_13_6_5_aabbPrefixMatches_mem_naturalFiltration
          t start 4 (by norm_num) hcoords)
        measurable_const measurable_const
    · have hwins : t - start ≤ 4 := by omega
      have hcoords : ∀ i : ℕ, i < t - start → start + i ≤ t := by
        intro i hi
        omega
      simp [ex_13_6_5_aabbConcreteEntrantTerminalNet, hlt, hDone]
      exact Measurable.ite
        (ex_13_6_5_aabbPrefixMatches_mem_naturalFiltration
          t start (t - start) hwins hcoords)
        measurable_const measurable_const
  · simp [ex_13_6_5_aabbConcreteEntrantTerminalNet, hlt]

theorem ex_13_6_5_aabbConcreteEntrantTerminalNet_measurable_naturalFiltrationBefore
    (t start : ℕ) :
    Measurable[ex_13_6_5_typingNaturalFiltrationBefore t]
      (fun ω : ex_13_6_5_TypingPath =>
        ex_13_6_5_aabbConcreteEntrantTerminalNet ω t start) := by
  classical
  cases t with
  | zero =>
      simp [ex_13_6_5_aabbConcreteEntrantTerminalNet]
  | succ k =>
      rw [ex_13_6_5_typingNaturalFiltrationBefore_succ_eq_old]
      by_cases hlt : start < k + 1
      · by_cases hDone : start + 4 ≤ k + 1
        · have hcoords : ∀ i : ℕ, i < 4 → start + i ≤ k := by
            intro i hi
            omega
          simp [ex_13_6_5_aabbConcreteEntrantTerminalNet, hlt, hDone]
          exact Measurable.ite
            (ex_13_6_5_aabbPrefixMatches_mem_naturalFiltration
              k start 4 (by norm_num) hcoords)
            measurable_const measurable_const
        · have hwins : k + 1 - start ≤ 4 := by omega
          have hcoords :
              ∀ i : ℕ, i < k + 1 - start → start + i ≤ k := by
            intro i hi
            omega
          simp [ex_13_6_5_aabbConcreteEntrantTerminalNet, hlt, hDone]
          exact Measurable.ite
            (ex_13_6_5_aabbPrefixMatches_mem_naturalFiltration
              k start (k + 1 - start) hwins hcoords)
            measurable_const measurable_const
      · simp [ex_13_6_5_aabbConcreteEntrantTerminalNet, hlt]

theorem ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_measurable
    (n : ℕ) :
    Measurable (ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess n) := by
  unfold ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess
  exact Finset.measurable_sum (Finset.range n) fun start _ =>
    ex_13_6_5_aabbConcreteEntrantTerminalNet_measurable n start

theorem ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_adapted :
    def_13_6_adapted ex_13_6_5_typingNaturalFiltration
      ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess := by
  intro n
  unfold ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess
  exact Finset.measurable_sum (Finset.range n) fun start _ =>
    ex_13_6_5_aabbConcreteEntrantTerminalNet_measurable_naturalFiltration n start

theorem ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_adaptedBefore :
    def_13_6_adapted ex_13_6_5_typingNaturalFiltrationBefore
      ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess := by
  intro n
  unfold ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess
  exact Finset.measurable_sum (Finset.range n) fun start _ =>
    ex_13_6_5_aabbConcreteEntrantTerminalNet_measurable_naturalFiltrationBefore n start

theorem ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_abs_le
    (n : ℕ) (ω : ex_13_6_5_TypingPath) :
    |ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess n ω| ≤
      (80 : ℝ) * n := by
  unfold ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess
  have hsum_abs :
      |∑ start ∈ Finset.range n,
          ex_13_6_5_aabbConcreteEntrantTerminalNet ω n start| ≤
        ∑ start ∈ Finset.range n,
          |ex_13_6_5_aabbConcreteEntrantTerminalNet ω n start| :=
    Finset.abs_sum_le_sum_abs
      (fun start => ex_13_6_5_aabbConcreteEntrantTerminalNet ω n start)
      (Finset.range n)
  have hsum_le :
      (∑ start ∈ Finset.range n,
          |ex_13_6_5_aabbConcreteEntrantTerminalNet ω n start|) ≤
        ∑ _start ∈ Finset.range n, (80 : ℝ) := by
    apply Finset.sum_le_sum
    intro start _hstart
    exact ex_13_6_5_aabbConcreteEntrantTerminalNet_abs_le ω n start
  calc
    |∑ start ∈ Finset.range n,
        ex_13_6_5_aabbConcreteEntrantTerminalNet ω n start| ≤
        ∑ start ∈ Finset.range n,
          |ex_13_6_5_aabbConcreteEntrantTerminalNet ω n start| := hsum_abs
    _ ≤ ∑ _start ∈ Finset.range n, (80 : ℝ) := hsum_le
    _ = (80 : ℝ) * n := by
      rw [Finset.sum_const]
      simp [nsmul_eq_mul, mul_comm]

theorem ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_integrable
    (n : ℕ) :
    Integrable (ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess n)
      ex_13_6_5_typingMeasure := by
  refine Integrable.of_bound
    (ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_measurable n).aestronglyMeasurable
    ((80 : ℝ) * n) ?_
  exact Filter.Eventually.of_forall fun ω => by
    simpa [Real.norm_eq_abs] using
      ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_abs_le n ω

theorem ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_condExp_self
    (n : ℕ) :
    ex_13_6_5_typingMeasure[
      ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess n |
      ex_13_6_5_typingNaturalFiltration n] =
        ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess n := by
  haveI :
      SigmaFinite
        (ex_13_6_5_typingMeasure.trim
          (ex_13_6_5_typingNaturalFiltration_le n)) :=
    ex_13_6_5_typingNaturalFiltration_sigmaFinite n
  exact
    condExp_of_stronglyMeasurable
      (ex_13_6_5_typingNaturalFiltration_le n)
      ((ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_adapted n).stronglyMeasurable)
      (ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_integrable n)

theorem ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_condExp_selfBefore
    (n : ℕ) :
    ex_13_6_5_typingMeasure[
      ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess n |
      ex_13_6_5_typingNaturalFiltrationBefore n] =
        ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess n := by
  haveI :
      SigmaFinite
        (ex_13_6_5_typingMeasure.trim
          (ex_13_6_5_typingNaturalFiltrationBefore_le n)) :=
    ex_13_6_5_typingNaturalFiltrationBefore_sigmaFinite n
  exact
    condExp_of_stronglyMeasurable
      (ex_13_6_5_typingNaturalFiltrationBefore_le n)
      ((ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_adaptedBefore n).stronglyMeasurable)
      (ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_integrable n)

theorem ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_bounded_increments :
    ∃ c : ℝ,
      0 ≤ c ∧
        ∀ n : ℕ, ∀ᵐ ω ∂ex_13_6_5_typingMeasure,
          |ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess (n + 1) ω -
            ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess n ω| ≤ c := by
  refine ⟨640, by norm_num, ?_⟩
  intro n
  refine Filter.Eventually.of_forall ?_
  intro ω
  simpa [ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess] using
    (ex_13_6_5_bankroll_increment_abs_le
      (net := fun ω t start => ex_13_6_5_aabbConcreteEntrantTerminalNet ω t start)
      (hStable := fun ω n start hDone =>
        ex_13_6_5_aabbConcreteEntrantTerminalNet_stable_after_four
          (ω := ω) (n := n) (start := start) hDone)
      (hBound := fun ω t start =>
        ex_13_6_5_aabbConcreteEntrantTerminalNet_abs_le ω t start)
      n ω)

def ex_13_6_5_aabbConcreteIIDTeamRoundGain
    (n : ℕ) (ω : ex_13_6_5_TypingPath) : ℝ :=
  ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess (n + 1) ω -
    ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess n ω

theorem ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_startsWithNoActiveBankroll :
    ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess 0
      =ᵐ[ex_13_6_5_typingMeasure]
        fun _ : ex_13_6_5_TypingPath => (0 : ℝ) := by
  exact Filter.Eventually.of_forall fun ω => by
    simp [ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess]

theorem ex_13_6_5_aabbFirstOccurrence_stopsAtWaitingTime :
    ∀ᵐ ω ∂ex_13_6_5_typingMeasure,
      ex_13_6_5_aabbFirstOccurrence ω =
        (ex_13_6_5_aabbWaitingTime ω : WithTop ℕ) := by
  filter_upwards [ex_13_6_5_aabbFirstOccurrence_finite_ae] with ω hFinite
  exact
    ex_13_6_5_firstOccurrence_eq_waitingTimeOf_of_finite
      (T := ex_13_6_5_aabbFirstOccurrence) (ne_of_lt hFinite)

theorem ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_bankrollUpdate :
    ∀ n : ℕ,
      (fun ω =>
        ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess (n + 1) ω -
          ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess n ω)
        =ᵐ[ex_13_6_5_typingMeasure]
          ex_13_6_5_aabbConcreteIIDTeamRoundGain n := by
  intro n
  exact Filter.Eventually.of_forall fun ω => rfl

theorem ex_13_6_5_aabbConcreteIIDTeamRoundGain_uniformBounded :
    ∃ c : ℝ,
      0 ≤ c ∧
        ∀ n : ℕ, ∀ᵐ ω ∂ex_13_6_5_typingMeasure,
          |ex_13_6_5_aabbConcreteIIDTeamRoundGain n ω| ≤ c := by
  simpa [ex_13_6_5_aabbConcreteIIDTeamRoundGain] using
    ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_bounded_increments

def ex_13_6_5_aabbTargetAfterWins (wins : ℕ) : ex_13_6_5_Key :=
  if h : wins < 4 then ex_13_6_5_aabbWordFin ⟨wins, h⟩
  else ex_13_6_5_Key.a

theorem ex_13_6_5_aabbPrefixMatches_succ_iff
    {ω : ex_13_6_5_TypingPath} {start wins : ℕ}
    (hwins : wins < 4) :
    ex_13_6_5_aabbPrefixMatches ω start (wins + 1) ↔
      ex_13_6_5_aabbPrefixMatches ω start wins ∧
        ω (start + wins) =
          ex_13_6_5_aabbTargetAfterWins wins := by
  interval_cases wins <;>
    simp [ex_13_6_5_aabbPrefixMatches,
      ex_13_6_5_lettersFromStart,
      ex_13_6_5_pattern_aabb,
      ex_13_6_5_aabbTargetAfterWins,
      ex_13_6_5_aabbWordFin] <;>
    tauto

def ex_13_6_5_aabbEntrantActiveBefore
    (n start : ℕ) (ω : ex_13_6_5_TypingPath) : Prop :=
  start ≤ n ∧ n < start + 4 ∧
    ex_13_6_5_aabbPrefixMatches ω start (n - start)

theorem ex_13_6_5_aabbEntrantActiveBefore_measurableSet
    (n start : ℕ) :
    @MeasurableSet ex_13_6_5_TypingPath
      (ex_13_6_5_typingNaturalFiltrationBefore n)
      {ω : ex_13_6_5_TypingPath |
        ex_13_6_5_aabbEntrantActiveBefore n start ω} := by
  classical
  by_cases hstart : start ≤ n
  · by_cases hactive : n < start + 4
    · have hwins : n - start ≤ 4 := by omega
      cases n with
      | zero =>
          have hstart0 : start = 0 := by omega
          subst start
          rw [show
              {ω : ex_13_6_5_TypingPath |
                ex_13_6_5_aabbEntrantActiveBefore 0 0 ω} =
                  Set.univ by
                ext ω
                simp [ex_13_6_5_aabbEntrantActiveBefore,
                  ex_13_6_5_aabbPrefixMatches,
                  ex_13_6_5_lettersFromStart,
                  ex_13_6_5_pattern_aabb]]
          exact MeasurableSet.univ
      | succ k =>
          rw [ex_13_6_5_typingNaturalFiltrationBefore_succ_eq_old]
          have hcoords :
              ∀ i : ℕ, i < k + 1 - start → start + i ≤ k := by
            intro i hi
            omega
          have hpref :=
            ex_13_6_5_aabbPrefixMatches_mem_naturalFiltration
              k start (k + 1 - start) hwins hcoords
          simpa [ex_13_6_5_aabbEntrantActiveBefore, hstart,
            hactive] using hpref
    · rw [show
          {ω : ex_13_6_5_TypingPath |
            ex_13_6_5_aabbEntrantActiveBefore n start ω} =
              ∅ by
          ext ω
          simp [ex_13_6_5_aabbEntrantActiveBefore, hstart, hactive]]
      exact
        @MeasurableSet.empty ex_13_6_5_TypingPath
          (ex_13_6_5_typingNaturalFiltrationBefore n)
  · rw [show
        {ω : ex_13_6_5_TypingPath |
          ex_13_6_5_aabbEntrantActiveBefore n start ω} =
            ∅ by
        ext ω
        simp [ex_13_6_5_aabbEntrantActiveBefore, hstart]]
    exact
      @MeasurableSet.empty ex_13_6_5_TypingPath
        (ex_13_6_5_typingNaturalFiltrationBefore n)

def ex_13_6_5_aabbEntrantStepGain
    (n start : ℕ) : ex_13_6_5_TypingPath → ℝ :=
  {ω : ex_13_6_5_TypingPath |
    ex_13_6_5_aabbEntrantActiveBefore n start ω}.indicator
      (fun ω : ex_13_6_5_TypingPath =>
        ex_13_6_5_keyFairBetNet ((3 : ℝ) ^ (n - start))
          (ex_13_6_5_aabbTargetAfterWins (n - start)) (ω n))

theorem ex_13_6_5_aabbEntrantStepGain_condExp_before_zero
    (n start : ℕ) :
    ex_13_6_5_typingMeasure[
      ex_13_6_5_aabbEntrantStepGain n start |
      ex_13_6_5_typingNaturalFiltrationBefore n] =ᵐ[ex_13_6_5_typingMeasure]
        (0 : ex_13_6_5_TypingPath → ℝ) := by
  simpa [ex_13_6_5_aabbEntrantStepGain] using
    ex_13_6_5_keyFairBetNet_indicator_condExp_before_zero
      n ((3 : ℝ) ^ (n - start))
      (ex_13_6_5_aabbTargetAfterWins (n - start))
      (hA := ex_13_6_5_aabbEntrantActiveBefore_measurableSet n start)

theorem ex_13_6_5_aabbConcreteEntrantTerminalNet_active_increment
    {ω : ex_13_6_5_TypingPath} {n start : ℕ}
    (hActive :
      ex_13_6_5_aabbEntrantActiveBefore n start ω) :
    ex_13_6_5_aabbConcreteEntrantTerminalNet ω (n + 1) start -
        ex_13_6_5_aabbConcreteEntrantTerminalNet ω n start =
      ex_13_6_5_keyFairBetNet ((3 : ℝ) ^ (n - start))
        (ex_13_6_5_aabbTargetAfterWins (n - start)) (ω n) := by
  classical
  rcases hActive with ⟨hstart, hwindow, hprefix⟩
  have hwins_lt : n - start < 4 := by omega
  have hwins_cases :
      n - start = 0 ∨ n - start = 1 ∨
        n - start = 2 ∨ n - start = 3 := by omega
  rcases hwins_cases with hwin | hwin | hwin | hwin
  · have hn : n = start := by omega
    subst n
    by_cases hobs : ω start = ex_13_6_5_Key.a
    · simp [ex_13_6_5_aabbConcreteEntrantTerminalNet,
        ex_13_6_5_aabbPrefixMatches,
        ex_13_6_5_lettersFromStart,
        ex_13_6_5_pattern_aabb,
        ex_13_6_5_aabbTargetAfterWins,
        ex_13_6_5_aabbWordFin,
        ex_13_6_5_keyFairBetNet,
        ex_13_6_5_fairBetNetGain,
        ex_13_6_5_gamblerNetAfterWins,
        hobs]
    · simp [ex_13_6_5_aabbConcreteEntrantTerminalNet,
        ex_13_6_5_aabbPrefixMatches,
        ex_13_6_5_lettersFromStart,
        ex_13_6_5_pattern_aabb,
        ex_13_6_5_aabbTargetAfterWins,
        ex_13_6_5_aabbWordFin,
        ex_13_6_5_keyFairBetNet,
        ex_13_6_5_fairBetNetGain,
        ex_13_6_5_gamblerNetAfterWins,
        hobs]
  · have hn : n = start + 1 := by omega
    subst n
    have hp1 : ω start = ex_13_6_5_Key.a := by
      simpa [ex_13_6_5_aabbPrefixMatches,
        ex_13_6_5_lettersFromStart,
        ex_13_6_5_pattern_aabb, hwin] using hprefix
    have hnextWins : start + 1 + 1 - start = 2 := by omega
    have hnextWindow : start + 1 < 4 + start := by omega
    have hnotDoneNext : ¬ start + 4 ≤ start + 1 + 1 := by omega
    by_cases hobs : ω (start + 1) = ex_13_6_5_Key.a
    · norm_num [ex_13_6_5_aabbConcreteEntrantTerminalNet,
        ex_13_6_5_aabbPrefixMatches,
        ex_13_6_5_lettersFromStart,
        ex_13_6_5_pattern_aabb,
        ex_13_6_5_aabbTargetAfterWins,
        ex_13_6_5_aabbWordFin,
        ex_13_6_5_keyFairBetNet,
        ex_13_6_5_fairBetNetGain,
        ex_13_6_5_gamblerNetAfterWins,
        hwin, hnextWins, hnextWindow, hnotDoneNext, hp1, hobs]
    · norm_num [ex_13_6_5_aabbConcreteEntrantTerminalNet,
        ex_13_6_5_aabbPrefixMatches,
        ex_13_6_5_lettersFromStart,
        ex_13_6_5_pattern_aabb,
        ex_13_6_5_aabbTargetAfterWins,
        ex_13_6_5_aabbWordFin,
        ex_13_6_5_keyFairBetNet,
        ex_13_6_5_fairBetNetGain,
        ex_13_6_5_gamblerNetAfterWins,
        hwin, hnextWins, hnextWindow, hnotDoneNext, hp1, hobs]
  · have hn : n = start + 2 := by omega
    subst n
    have hp2 :
        ω start = ex_13_6_5_Key.a ∧
          ω (start + 1) = ex_13_6_5_Key.a := by
      simpa [ex_13_6_5_aabbPrefixMatches,
        ex_13_6_5_lettersFromStart,
        ex_13_6_5_pattern_aabb, hwin] using hprefix
    have hp0 : ω start = ex_13_6_5_Key.a := hp2.1
    have hp1 : ω (start + 1) = ex_13_6_5_Key.a := hp2.2
    have hnextWins : start + 2 + 1 - start = 3 := by omega
    have hnextWindow : start + 2 < 4 + start := by omega
    have hnotDoneNext : ¬ start + 4 ≤ start + 2 + 1 := by omega
    by_cases hobs : ω (start + 2) = ex_13_6_5_Key.b
    · norm_num [ex_13_6_5_aabbConcreteEntrantTerminalNet,
        ex_13_6_5_aabbPrefixMatches,
        ex_13_6_5_lettersFromStart,
        ex_13_6_5_pattern_aabb,
        ex_13_6_5_aabbTargetAfterWins,
        ex_13_6_5_aabbWordFin,
        ex_13_6_5_keyFairBetNet,
        ex_13_6_5_fairBetNetGain,
        ex_13_6_5_gamblerNetAfterWins,
        hwin, hnextWins, hnextWindow, hnotDoneNext, hp0, hp1, hobs]
    · norm_num [ex_13_6_5_aabbConcreteEntrantTerminalNet,
        ex_13_6_5_aabbPrefixMatches,
        ex_13_6_5_lettersFromStart,
        ex_13_6_5_pattern_aabb,
        ex_13_6_5_aabbTargetAfterWins,
        ex_13_6_5_aabbWordFin,
        ex_13_6_5_keyFairBetNet,
        ex_13_6_5_fairBetNetGain,
        ex_13_6_5_gamblerNetAfterWins,
        hwin, hnextWins, hnextWindow, hnotDoneNext, hp0, hp1, hobs]
  · have hn : n = start + 3 := by omega
    subst n
    have hp3 :
        ω start = ex_13_6_5_Key.a ∧
          ω (start + 1) = ex_13_6_5_Key.a ∧
            ω (start + 2) = ex_13_6_5_Key.b := by
      simpa [ex_13_6_5_aabbPrefixMatches,
        ex_13_6_5_lettersFromStart,
        ex_13_6_5_pattern_aabb, hwin] using hprefix
    have hp0 : ω start = ex_13_6_5_Key.a := hp3.1
    have hp1 : ω (start + 1) = ex_13_6_5_Key.a := hp3.2.1
    have hp2 : ω (start + 2) = ex_13_6_5_Key.b := hp3.2.2
    by_cases hobs : ω (start + 3) = ex_13_6_5_Key.b
    · norm_num [ex_13_6_5_aabbConcreteEntrantTerminalNet,
        ex_13_6_5_aabbPrefixMatches,
        ex_13_6_5_lettersFromStart,
        ex_13_6_5_pattern_aabb,
        ex_13_6_5_aabbTargetAfterWins,
        ex_13_6_5_aabbWordFin,
        ex_13_6_5_keyFairBetNet,
        ex_13_6_5_fairBetNetGain,
        ex_13_6_5_gamblerNetAfterWins,
        hwin, hp0, hp1, hp2, hobs]
    · norm_num [ex_13_6_5_aabbConcreteEntrantTerminalNet,
        ex_13_6_5_aabbPrefixMatches,
        ex_13_6_5_lettersFromStart,
        ex_13_6_5_pattern_aabb,
        ex_13_6_5_aabbTargetAfterWins,
        ex_13_6_5_aabbWordFin,
        ex_13_6_5_keyFairBetNet,
        ex_13_6_5_fairBetNetGain,
        ex_13_6_5_gamblerNetAfterWins,
        hwin, hp0, hp1, hp2, hobs]

theorem ex_13_6_5_aabbConcreteEntrantTerminalNet_inactive_increment_zero
    {ω : ex_13_6_5_TypingPath} {n start : ℕ}
    (hInactive :
      ¬ ex_13_6_5_aabbEntrantActiveBefore n start ω) :
    ex_13_6_5_aabbConcreteEntrantTerminalNet ω (n + 1) start -
        ex_13_6_5_aabbConcreteEntrantTerminalNet ω n start = 0 := by
  classical
  by_cases hstart : start ≤ n
  · by_cases hwindow : n < start + 4
    · have hprefix_false :
          ¬ ex_13_6_5_aabbPrefixMatches ω start (n - start) := by
        intro hprefix
        exact hInactive ⟨hstart, hwindow, hprefix⟩
      have hwins_lt : n - start < 4 := by omega
      have hnextWins : n + 1 - start = n - start + 1 := by omega
      have hnotPrefixNext :
          ¬ ex_13_6_5_aabbPrefixMatches ω start (n + 1 - start) := by
        intro hpnext
        have hpnext' :
            ex_13_6_5_aabbPrefixMatches ω start (n - start + 1) := by
          simpa [hnextWins] using hpnext
        exact hprefix_false
          ((ex_13_6_5_aabbPrefixMatches_succ_iff
            (ω := ω) (start := start) (wins := n - start)
            hwins_lt).1 hpnext').1
      have hwins_cases :
          n - start = 0 ∨ n - start = 1 ∨
            n - start = 2 ∨ n - start = 3 := by omega
      rcases hwins_cases with hwin | hwin | hwin | hwin
      · exfalso
        apply hprefix_false
        simpa [ex_13_6_5_aabbPrefixMatches,
          ex_13_6_5_lettersFromStart,
          ex_13_6_5_pattern_aabb, hwin]
      · have hn : n = start + 1 := by omega
        subst n
        have hnotDone : ¬ start + 4 ≤ start + 1 := by omega
        have hnotDoneNext : ¬ start + 4 ≤ start + 1 + 1 := by omega
        have hnext : start + 1 + 1 - start = 2 := by omega
        have hprefixOld :
            ¬ ex_13_6_5_aabbPrefixMatches ω start 1 := by
          simpa [hwin] using hprefix_false
        have hprefixNew :
            ¬ ex_13_6_5_aabbPrefixMatches ω start 2 := by
          simpa [hnext] using hnotPrefixNext
        simp [ex_13_6_5_aabbConcreteEntrantTerminalNet,
          hnotDone, hnotDoneNext, hnext, hprefixOld, hprefixNew]
      · have hn : n = start + 2 := by omega
        subst n
        have hnotDone : ¬ start + 4 ≤ start + 2 := by omega
        have hnotDoneNext : ¬ start + 4 ≤ start + 2 + 1 := by omega
        have hnext : start + 2 + 1 - start = 3 := by omega
        have hprefixOld :
            ¬ ex_13_6_5_aabbPrefixMatches ω start 2 := by
          simpa [hwin] using hprefix_false
        have hprefixNew :
            ¬ ex_13_6_5_aabbPrefixMatches ω start 3 := by
          simpa [hnext] using hnotPrefixNext
        simp [ex_13_6_5_aabbConcreteEntrantTerminalNet,
          hnotDone, hnotDoneNext, hnext, hprefixOld, hprefixNew]
      · have hn : n = start + 3 := by omega
        subst n
        have hnotDone : ¬ start + 4 ≤ start + 3 := by omega
        have hdoneNext : start + 4 ≤ start + 3 + 1 := by omega
        have hnext : start + 3 + 1 - start = 4 := by omega
        have hprefixOld :
            ¬ ex_13_6_5_aabbPrefixMatches ω start 3 := by
          simpa [hwin] using hprefix_false
        have hprefixNew :
            ¬ ex_13_6_5_aabbPrefixMatches ω start 4 := by
          simpa [hnext] using hnotPrefixNext
        simp [ex_13_6_5_aabbConcreteEntrantTerminalNet,
          hnotDone, hdoneNext, hnext, hprefixOld, hprefixNew]
    · have hDone : start + 4 ≤ n := by omega
      exact
        ex_13_6_5_aabbConcreteEntrantTerminalNet_old_change_zero
          (ω := ω) (n := n) (start := start) hDone
  · have hnotlt : ¬ start < n := by omega
    have hnotlt_succ : ¬ start < n + 1 := by omega
    simp [ex_13_6_5_aabbConcreteEntrantTerminalNet,
      hnotlt, hnotlt_succ]

theorem ex_13_6_5_aabbConcreteEntrantTerminalNet_increment_eq_stepGain
    (n start : ℕ) (ω : ex_13_6_5_TypingPath) :
    ex_13_6_5_aabbConcreteEntrantTerminalNet ω (n + 1) start -
        ex_13_6_5_aabbConcreteEntrantTerminalNet ω n start =
      ex_13_6_5_aabbEntrantStepGain n start ω := by
  classical
  by_cases hActive :
      ex_13_6_5_aabbEntrantActiveBefore n start ω
  · simpa [ex_13_6_5_aabbEntrantStepGain, hActive] using
      ex_13_6_5_aabbConcreteEntrantTerminalNet_active_increment
        (ω := ω) (n := n) (start := start) hActive
  · simpa [ex_13_6_5_aabbEntrantStepGain, hActive] using
      ex_13_6_5_aabbConcreteEntrantTerminalNet_inactive_increment_zero
        (ω := ω) (n := n) (start := start) hActive

theorem ex_13_6_5_aabbConcreteIIDTeamRoundGain_eq_sum_stepGain
    (n : ℕ) (ω : ex_13_6_5_TypingPath) :
    ex_13_6_5_aabbConcreteIIDTeamRoundGain n ω =
      ∑ start ∈ Finset.range (n + 1),
        ex_13_6_5_aabbEntrantStepGain n start ω := by
  unfold ex_13_6_5_aabbConcreteIIDTeamRoundGain
  unfold ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess
  have hOldExtend :
      (∑ start ∈ Finset.range n,
          ex_13_6_5_aabbConcreteEntrantTerminalNet ω n start) =
        ∑ start ∈ Finset.range (n + 1),
          ex_13_6_5_aabbConcreteEntrantTerminalNet ω n start := by
    rw [Finset.sum_range_succ]
    simp [ex_13_6_5_aabbConcreteEntrantTerminalNet]
  rw [hOldExtend]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun start _hstart =>
    ex_13_6_5_aabbConcreteEntrantTerminalNet_increment_eq_stepGain
      n start ω

theorem ex_13_6_5_aabbEntrantStepGain_integrable
    (n start : ℕ) :
    Integrable (ex_13_6_5_aabbEntrantStepGain n start)
      ex_13_6_5_typingMeasure := by
  unfold ex_13_6_5_aabbEntrantStepGain
  exact
    (ex_13_6_5_keyFairBetNet_coord_integrable
      n ((3 : ℝ) ^ (n - start))
      (ex_13_6_5_aabbTargetAfterWins (n - start))).indicator
        ((ex_13_6_5_typingNaturalFiltrationBefore_le n)
          {ω : ex_13_6_5_TypingPath |
            ex_13_6_5_aabbEntrantActiveBefore n start ω}
          (ex_13_6_5_aabbEntrantActiveBefore_measurableSet n start))

theorem ex_13_6_5_aabbStepGain_sum_condExp_before_zero
    (n : ℕ) :
    ex_13_6_5_typingMeasure[
      (∑ start ∈ Finset.range (n + 1),
        fun ω : ex_13_6_5_TypingPath =>
          ex_13_6_5_aabbEntrantStepGain n start ω) |
      ex_13_6_5_typingNaturalFiltrationBefore n] =ᵐ[ex_13_6_5_typingMeasure]
        (0 : ex_13_6_5_TypingPath → ℝ) := by
  have hsum :
      ex_13_6_5_typingMeasure[
        (∑ start ∈ Finset.range (n + 1),
          fun ω : ex_13_6_5_TypingPath =>
            ex_13_6_5_aabbEntrantStepGain n start ω) |
        ex_13_6_5_typingNaturalFiltrationBefore n] =ᵐ[ex_13_6_5_typingMeasure]
          ∑ start ∈ Finset.range (n + 1),
            ex_13_6_5_typingMeasure[
              ex_13_6_5_aabbEntrantStepGain n start |
              ex_13_6_5_typingNaturalFiltrationBefore n] := by
    exact
      condExp_finset_sum
        (s := Finset.range (n + 1))
        (f := fun start ω =>
          ex_13_6_5_aabbEntrantStepGain n start ω)
        (fun start _hstart =>
          ex_13_6_5_aabbEntrantStepGain_integrable n start)
        (ex_13_6_5_typingNaturalFiltrationBefore n)
  refine hsum.trans ?_
  have hzero_sum :
      (∑ start ∈ Finset.range (n + 1),
          ex_13_6_5_typingMeasure[
            ex_13_6_5_aabbEntrantStepGain n start |
            ex_13_6_5_typingNaturalFiltrationBefore n]) =ᵐ[ex_13_6_5_typingMeasure]
        ∑ start ∈ Finset.range (n + 1),
          (0 : ex_13_6_5_TypingPath → ℝ) :=
    eventuallyEq_sum
      (s := Finset.range (n + 1))
      (f := fun start =>
        ex_13_6_5_typingMeasure[
          ex_13_6_5_aabbEntrantStepGain n start |
          ex_13_6_5_typingNaturalFiltrationBefore n])
      (g := fun _start => (0 : ex_13_6_5_TypingPath → ℝ))
      (fun start _hstart =>
        ex_13_6_5_aabbEntrantStepGain_condExp_before_zero n start)
  simpa using hzero_sum

theorem ex_13_6_5_aabbStepGain_sum_integrable
    (n : ℕ) :
    Integrable
      (∑ start ∈ Finset.range (n + 1),
        fun ω : ex_13_6_5_TypingPath =>
          ex_13_6_5_aabbEntrantStepGain n start ω)
      ex_13_6_5_typingMeasure :=
  MeasureTheory.integrable_finset_sum'
    (Finset.range (n + 1))
    (fun start _hstart =>
      ex_13_6_5_aabbEntrantStepGain_integrable n start)

theorem ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_succ_eq_add_stepSum
    (n : ℕ) :
    ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess (n + 1)
      =ᵐ[ex_13_6_5_typingMeasure]
        fun ω : ex_13_6_5_TypingPath =>
          ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess n ω +
            (∑ start ∈ Finset.range (n + 1),
              fun ω : ex_13_6_5_TypingPath =>
                ex_13_6_5_aabbEntrantStepGain n start ω) ω := by
  exact Filter.Eventually.of_forall fun ω => by
    have hround :=
      ex_13_6_5_aabbConcreteIIDTeamRoundGain_eq_sum_stepGain n ω
    unfold ex_13_6_5_aabbConcreteIIDTeamRoundGain at hround
    change
      ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess (n + 1) ω =
        ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess n ω +
          (∑ start ∈ Finset.range (n + 1),
            fun ω : ex_13_6_5_TypingPath =>
              ex_13_6_5_aabbEntrantStepGain n start ω) ω
    have hsum_apply :
        (∑ start ∈ Finset.range (n + 1),
          fun ω : ex_13_6_5_TypingPath =>
            ex_13_6_5_aabbEntrantStepGain n start ω) ω =
          ∑ start ∈ Finset.range (n + 1),
            ex_13_6_5_aabbEntrantStepGain n start ω := by
      simp
    rw [hsum_apply]
    linarith

theorem ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_oneStepConditionBefore :
    def_13_7_oneStepCondition ex_13_6_5_typingMeasure
      ex_13_6_5_typingNaturalFiltrationBefore
      ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess := by
  intro n
  have hdecomp :=
    ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_succ_eq_add_stepSum n
  have hcond_decomp :
      ex_13_6_5_typingMeasure[
        ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess (n + 1) |
        ex_13_6_5_typingNaturalFiltrationBefore n] =ᵐ[ex_13_6_5_typingMeasure]
        ex_13_6_5_typingMeasure[
          (fun ω : ex_13_6_5_TypingPath =>
            ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess n ω +
              (∑ start ∈ Finset.range (n + 1),
                fun ω : ex_13_6_5_TypingPath =>
                  ex_13_6_5_aabbEntrantStepGain n start ω) ω) |
          ex_13_6_5_typingNaturalFiltrationBefore n] :=
    condExp_congr_ae hdecomp
  refine hcond_decomp.trans ?_
  have hadd :
      ex_13_6_5_typingMeasure[
        (fun ω : ex_13_6_5_TypingPath =>
          ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess n ω +
            (∑ start ∈ Finset.range (n + 1),
              fun ω : ex_13_6_5_TypingPath =>
                ex_13_6_5_aabbEntrantStepGain n start ω) ω) |
        ex_13_6_5_typingNaturalFiltrationBefore n] =ᵐ[ex_13_6_5_typingMeasure]
          ex_13_6_5_typingMeasure[
            ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess n |
            ex_13_6_5_typingNaturalFiltrationBefore n] +
          ex_13_6_5_typingMeasure[
            (∑ start ∈ Finset.range (n + 1),
              fun ω : ex_13_6_5_TypingPath =>
                ex_13_6_5_aabbEntrantStepGain n start ω) |
            ex_13_6_5_typingNaturalFiltrationBefore n] :=
    condExp_add
      (ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_integrable n)
      (ex_13_6_5_aabbStepGain_sum_integrable n)
      (ex_13_6_5_typingNaturalFiltrationBefore n)
  refine hadd.trans ?_
  have hself :=
    ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_condExp_selfBefore n
  filter_upwards
    [ex_13_6_5_aabbStepGain_sum_condExp_before_zero n] with ω hzero
  simp [hself, hzero]

theorem ex_13_6_5_patternOccursAt_aabb_of_prefixMatches_four
    {ω : ex_13_6_5_TypingPath} {start : ℕ}
    (hPrefix : ex_13_6_5_aabbPrefixMatches ω start 4) :
    ex_13_6_5_patternOccursAt ex_13_6_5_pattern_aabb ω
      (start + 4) := by
  rcases hPrefix with ⟨_, hmatch⟩
  simp [ex_13_6_5_pattern_aabb,
    ex_13_6_5_lettersFromStart] at hmatch
  rcases hmatch with ⟨h0, h1, h2, h3⟩
  refine ⟨by simp [ex_13_6_5_pattern_aabb], ?_⟩
  intro i
  fin_cases i <;>
    simp [ex_13_6_5_pattern_aabb, h0, h1, h2, h3]

theorem ex_13_6_5_aabb_four_win_start_eq_terminal_start
    {ω : ex_13_6_5_TypingPath} {t start : ℕ}
    (hT : ex_13_6_5_aabbFirstOccurrence ω = (t : WithTop ℕ))
    (hBeforeTerminal : start + 4 ≤ t)
    (hPrefix : ex_13_6_5_aabbPrefixMatches ω start 4) :
    start = t - 4 := by
  have hOccStart :
      ex_13_6_5_patternOccursAt ex_13_6_5_pattern_aabb ω
        (start + 4) :=
    ex_13_6_5_patternOccursAt_aabb_of_prefixMatches_four hPrefix
  have hmin : t ≤ start + 4 :=
    ex_13_6_5_firstOccurrence_min_of_eq
      (pattern := ex_13_6_5_pattern_aabb) hT hOccStart
  omega

theorem ex_13_6_5_aabbPrefixMatches_not_three_from_terminal
    {ω : ex_13_6_5_TypingPath} {t : ℕ}
    (hT : ex_13_6_5_aabbFirstOccurrence ω = (t : WithTop ℕ)) :
    ¬ ex_13_6_5_aabbPrefixMatches ω (t - 3) 3 := by
  have hOcc :
      ex_13_6_5_patternOccursAt ex_13_6_5_pattern_aabb ω t :=
    ex_13_6_5_firstOccurrence_occursAt_of_eq hT
  rcases hOcc with ⟨hlen, hletters⟩
  have ht : 4 ≤ t := by
    simpa [ex_13_6_5_pattern_aabb] using hlen
  have h2 : ω (t - 2) = ex_13_6_5_Key.b := by
    have h := hletters ⟨2, by simp [ex_13_6_5_pattern_aabb]⟩
    have hidx : t - 4 + 2 = t - 2 := by omega
    simpa [ex_13_6_5_pattern_aabb, hidx] using h
  intro hPrefix
  rcases hPrefix with ⟨_, hmatch⟩
  simp [ex_13_6_5_lettersFromStart,
    ex_13_6_5_pattern_aabb] at hmatch
  rcases hmatch with ⟨_, hsecond, _⟩
  have hidx : t - 3 + 1 = t - 2 := by omega
  rw [hidx] at hsecond
  rw [h2] at hsecond
  cases hsecond

theorem ex_13_6_5_aabbPrefixMatches_not_two_from_terminal
    {ω : ex_13_6_5_TypingPath} {t : ℕ}
    (hT : ex_13_6_5_aabbFirstOccurrence ω = (t : WithTop ℕ)) :
    ¬ ex_13_6_5_aabbPrefixMatches ω (t - 2) 2 := by
  have hOcc :
      ex_13_6_5_patternOccursAt ex_13_6_5_pattern_aabb ω t :=
    ex_13_6_5_firstOccurrence_occursAt_of_eq hT
  rcases hOcc with ⟨hlen, hletters⟩
  have ht : 4 ≤ t := by
    simpa [ex_13_6_5_pattern_aabb] using hlen
  have h2 : ω (t - 2) = ex_13_6_5_Key.b := by
    have h := hletters ⟨2, by simp [ex_13_6_5_pattern_aabb]⟩
    have hidx : t - 4 + 2 = t - 2 := by omega
    simpa [ex_13_6_5_pattern_aabb, hidx] using h
  intro hPrefix
  rcases hPrefix with ⟨_, hmatch⟩
  simp [ex_13_6_5_lettersFromStart,
    ex_13_6_5_pattern_aabb] at hmatch
  rcases hmatch with ⟨hfirst, _⟩
  rw [h2] at hfirst
  cases hfirst

theorem ex_13_6_5_aabbPrefixMatches_not_one_from_terminal
    {ω : ex_13_6_5_TypingPath} {t : ℕ}
    (hT : ex_13_6_5_aabbFirstOccurrence ω = (t : WithTop ℕ)) :
    ¬ ex_13_6_5_aabbPrefixMatches ω (t - 1) 1 := by
  have hOcc :
      ex_13_6_5_patternOccursAt ex_13_6_5_pattern_aabb ω t :=
    ex_13_6_5_firstOccurrence_occursAt_of_eq hT
  rcases hOcc with ⟨hlen, hletters⟩
  have ht : 4 ≤ t := by
    simpa [ex_13_6_5_pattern_aabb] using hlen
  have h3 : ω (t - 1) = ex_13_6_5_Key.b := by
    have h := hletters ⟨3, by simp [ex_13_6_5_pattern_aabb]⟩
    have hidx : t - 4 + 3 = t - 1 := by omega
    simpa [ex_13_6_5_pattern_aabb, hidx] using h
  intro hPrefix
  rcases hPrefix with ⟨_, hmatch⟩
  simp [ex_13_6_5_lettersFromStart,
    ex_13_6_5_pattern_aabb] at hmatch
  rw [h3] at hmatch
  cases hmatch

theorem ex_13_6_5_aabbConcreteEntrantTerminalNet_four_win_of_occursAt
    {ω : ex_13_6_5_TypingPath} {t : ℕ}
    (hT : ex_13_6_5_aabbFirstOccurrence ω = (t : WithTop ℕ)) :
    ex_13_6_5_aabbConcreteEntrantTerminalNet ω t (t - 4) = 80 := by
  have hOcc :
      ex_13_6_5_patternOccursAt ex_13_6_5_pattern_aabb ω t :=
    ex_13_6_5_firstOccurrence_occursAt_of_eq hT
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
  have hPrefix4_terminal :
      ex_13_6_5_aabbPrefixMatches ω (t - 4) 4 := by
    refine ⟨by simp [ex_13_6_5_pattern_aabb], ?_⟩
    have hidx0 : t - 4 + 0 = t - 4 := by omega
    have hidx1 : t - 4 + 1 = t - 3 := by omega
    have hidx2 : t - 4 + 2 = t - 2 := by omega
    have hidx3 : t - 4 + 3 = t - 1 := by omega
    simp [ex_13_6_5_lettersFromStart, ex_13_6_5_pattern_aabb,
      hidx0, hidx1, hidx2, hidx3, h0, h1, h2, h3]
  have hlt : t - 4 < t := by omega
  have hEnough : t - 4 + 4 ≤ t := by omega
  simp [ex_13_6_5_aabbConcreteEntrantTerminalNet,
    hlt, hEnough, hPrefix4_terminal,
    ex_13_6_5_gamblerNetAfterWins]
  norm_num

theorem ex_13_6_5_aabbConcreteEntrantTerminalNet_other_loses
    {ω : ex_13_6_5_TypingPath} {t start : ℕ}
    (hT : ex_13_6_5_aabbFirstOccurrence ω = (t : WithTop ℕ))
    (hstart_mem : start ∈ Finset.range t)
    (hnot_four : start ≠ t - 4) :
    ex_13_6_5_aabbConcreteEntrantTerminalNet ω t start = -1 := by
  have hOcc :
      ex_13_6_5_patternOccursAt ex_13_6_5_pattern_aabb ω t :=
    ex_13_6_5_firstOccurrence_occursAt_of_eq hT
  rcases hOcc with ⟨hlen, _hletters⟩
  have ht : 4 ≤ t := by
    simpa [ex_13_6_5_pattern_aabb] using hlen
  have hstart_lt : start < t := by
    simpa using hstart_mem
  by_cases hEnough : start + 4 ≤ t
  · have hPrefixFalse :
        ¬ ex_13_6_5_aabbPrefixMatches ω start 4 := by
      intro hPrefix
      have hstart_eq :
          start = t - 4 :=
        ex_13_6_5_aabb_four_win_start_eq_terminal_start
          hT hEnough hPrefix
      exact hnot_four hstart_eq
    simp [ex_13_6_5_aabbConcreteEntrantTerminalNet,
      hstart_lt, hEnough, hPrefixFalse]
  · have hcases :
        start = t - 3 ∨ start = t - 2 ∨ start = t - 1 := by
      omega
    have hPrefixFalse :
        ¬ ex_13_6_5_aabbPrefixMatches ω start (t - start) := by
      intro hPrefix
      rcases hcases with hstart_three | hstart_two | hstart_one
      · have hwins_three : t - (t - 3) = 3 := by omega
        rw [hstart_three, hwins_three] at hPrefix
        exact
          (ex_13_6_5_aabbPrefixMatches_not_three_from_terminal hT)
            hPrefix
      · have hwins_two : t - (t - 2) = 2 := by omega
        rw [hstart_two, hwins_two] at hPrefix
        exact
          (ex_13_6_5_aabbPrefixMatches_not_two_from_terminal hT)
            hPrefix
      · have hwins_one : t - (t - 1) = 1 := by omega
        rw [hstart_one, hwins_one] at hPrefix
        exact
          (ex_13_6_5_aabbPrefixMatches_not_one_from_terminal hT)
            hPrefix
    simp [ex_13_6_5_aabbConcreteEntrantTerminalNet,
      hstart_lt, hEnough, hPrefixFalse]

theorem ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_eq_of_occursAt
    {ω : ex_13_6_5_TypingPath} {t : ℕ}
    (hT : ex_13_6_5_aabbFirstOccurrence ω = (t : WithTop ℕ)) :
    ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess t ω =
      81 - (t : ℝ) := by
  have hOcc :
      ex_13_6_5_patternOccursAt ex_13_6_5_pattern_aabb ω t :=
    ex_13_6_5_firstOccurrence_occursAt_of_eq hT
  rcases hOcc with ⟨hlen, _hletters⟩
  have ht : 4 ≤ t := by
    simpa [ex_13_6_5_pattern_aabb] using hlen
  have hPoint :
      ∀ start ∈ Finset.range t,
        ex_13_6_5_aabbConcreteEntrantTerminalNet ω t start =
          (-1 : ℝ) +
            (if start = t - 4 then (81 : ℝ) else 0) := by
    intro start hstart_mem
    by_cases hfour : start = t - 4
    · subst start
      rw [ex_13_6_5_aabbConcreteEntrantTerminalNet_four_win_of_occursAt hT]
      norm_num
    · rw [ex_13_6_5_aabbConcreteEntrantTerminalNet_other_loses
        hT hstart_mem hfour]
      simp [hfour]
  calc
    ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess t ω =
        ∑ start ∈ Finset.range t,
          ((-1 : ℝ) +
            (if start = t - 4 then (81 : ℝ) else 0)) := by
          unfold ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess
          exact Finset.sum_congr rfl hPoint
    _ = 81 - (t : ℝ) := by
      exact ex_13_6_5_sum_range_single_terminal_bonus ht

theorem ex_13_6_5_aabb_concrete_iid_entrant_bankroll_process
    (ω : ex_13_6_5_TypingPath) {t : ℕ}
    (hT : ex_13_6_5_aabbFirstOccurrence ω = (t : WithTop ℕ)) :
    thm_13_18_stoppedValueReal
        ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess
        ex_13_6_5_aabbFirstOccurrence ω =
      ex_13_6_5_aabbTerminalTeamGain (t : ℝ) := by
  have hOcc :
      ex_13_6_5_patternOccursAt ex_13_6_5_pattern_aabb ω t :=
    ex_13_6_5_firstOccurrence_occursAt_of_eq hT
  have hBankroll :
      ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess t ω =
        81 - (t : ℝ) :=
    ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_eq_of_occursAt hT
  have hValue :
      ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess t ω =
        ex_13_6_5_aabbTerminalTeamGain (t : ℝ) := by
    rw [hBankroll, ex_13_6_5_aabbTerminalTeamGain_eq]
  exact ex_13_6_5_stoppedValueReal_eq_of_firstOccurrence hT hValue
