/-
TASK ID: ex_13_6_5_word_pattern_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.ex_13_6_5_process_common_support

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

def ex_13_6_5_wordFinPrefixMatches
    (word : Fin 4 -> ex_13_6_5_Key)
    (omega : ex_13_6_5_TypingPath) (start wins : Nat) : Prop :=
  wins <= 4 ∧
    ∀ i : Fin 4, i.val < wins -> omega (start + i.val) = word i

theorem ex_13_6_5_wordFinPrefixMatches_measurableSet
    (word : Fin 4 -> ex_13_6_5_Key)
    (start wins : Nat) (hwins : wins <= 4) :
    MeasurableSet
      {omega : ex_13_6_5_TypingPath |
        ex_13_6_5_wordFinPrefixMatches word omega start wins} := by
  have hcoord : ∀ i : Fin 4,
      MeasurableSet
        {omega : ex_13_6_5_TypingPath |
          i.val < wins -> omega (start + i.val) = word i} := by
    intro i
    by_cases hi : i.val < wins
    · simpa [hi] using
        ex_13_6_5_coord_eq_measurableSet (start + i.val) (word i)
    · simp [hi]
  have hAll : MeasurableSet
      {omega : ex_13_6_5_TypingPath |
        ∀ i : Fin 4, i.val < wins -> omega (start + i.val) = word i} := by
    simpa [Set.setOf_forall] using MeasurableSet.iInter hcoord
  have hEq :
      {omega : ex_13_6_5_TypingPath |
        ex_13_6_5_wordFinPrefixMatches word omega start wins} =
      {omega : ex_13_6_5_TypingPath |
        ∀ i : Fin 4, i.val < wins -> omega (start + i.val) = word i} := by
    ext omega
    simp [ex_13_6_5_wordFinPrefixMatches, hwins]
  rw [hEq]
  exact hAll

theorem ex_13_6_5_wordFinPrefixMatches_mem_naturalFiltration
    (word : Fin 4 -> ex_13_6_5_Key)
    (n start wins : Nat) (hwins : wins <= 4)
    (hidx : ∀ i : Nat, i < wins -> start + i <= n) :
    @MeasurableSet ex_13_6_5_TypingPath
      (ex_13_6_5_typingNaturalFiltration n)
      {omega : ex_13_6_5_TypingPath |
        ex_13_6_5_wordFinPrefixMatches word omega start wins} := by
  have hcoord : ∀ i : Fin 4,
      @MeasurableSet ex_13_6_5_TypingPath
        (ex_13_6_5_typingNaturalFiltration n)
        {omega : ex_13_6_5_TypingPath |
          i.val < wins -> omega (start + i.val) = word i} := by
    intro i
    by_cases hi : i.val < wins
    · simpa [hi] using
        ex_13_6_5_coord_eq_mem_naturalFiltration
          (hidx i.val hi) (word i)
    · simp [hi]
  have hAll : @MeasurableSet ex_13_6_5_TypingPath
      (ex_13_6_5_typingNaturalFiltration n)
      {omega : ex_13_6_5_TypingPath |
        ∀ i : Fin 4, i.val < wins -> omega (start + i.val) = word i} := by
    simpa [Set.setOf_forall] using MeasurableSet.iInter hcoord
  have hEq :
      {omega : ex_13_6_5_TypingPath |
        ex_13_6_5_wordFinPrefixMatches word omega start wins} =
      {omega : ex_13_6_5_TypingPath |
        ∀ i : Fin 4, i.val < wins -> omega (start + i.val) = word i} := by
    ext omega
    simp [ex_13_6_5_wordFinPrefixMatches, hwins]
  rw [hEq]
  exact hAll

def ex_13_6_5_wordConcreteEntrantTerminalNet
    (word : Fin 4 -> ex_13_6_5_Key)
    (omega : ex_13_6_5_TypingPath) (t start : Nat) : Real := by
  classical
  exact
    if start < t then
      if start + 4 <= t then
        if ex_13_6_5_wordFinPrefixMatches word omega start 4 then
          ex_13_6_5_gamblerNetAfterWins 4
        else
          -1
      else
        let wins := t - start
        if ex_13_6_5_wordFinPrefixMatches word omega start wins then
          ex_13_6_5_gamblerNetAfterWins wins
        else
          -1
    else
      0

def ex_13_6_5_wordConcreteIIDEntrantBankrollProcess
    (word : Fin 4 -> ex_13_6_5_Key) :
    Nat -> ex_13_6_5_TypingPath -> Real :=
  fun n omega =>
    ∑ start ∈ Finset.range n,
      ex_13_6_5_wordConcreteEntrantTerminalNet word omega n start

theorem ex_13_6_5_wordConcreteEntrantTerminalNet_stable_after_four
    {word : Fin 4 -> ex_13_6_5_Key}
    {omega : ex_13_6_5_TypingPath} {n start : Nat}
    (hDone : start + 4 <= n) :
    ex_13_6_5_wordConcreteEntrantTerminalNet word omega (n + 1) start =
      ex_13_6_5_wordConcreteEntrantTerminalNet word omega n start := by
  have hlt_n : start < n := by omega
  have hlt_succ : start < n + 1 := by omega
  have hDone_succ : start + 4 <= n + 1 := by omega
  by_cases hPrefix : ex_13_6_5_wordFinPrefixMatches word omega start 4
  · simp [ex_13_6_5_wordConcreteEntrantTerminalNet,
      hlt_n, hlt_succ, hDone, hDone_succ, hPrefix]
  · simp [ex_13_6_5_wordConcreteEntrantTerminalNet,
      hlt_n, hlt_succ, hDone, hDone_succ, hPrefix]

theorem ex_13_6_5_wordConcreteEntrantTerminalNet_old_change_zero
    {word : Fin 4 -> ex_13_6_5_Key}
    {omega : ex_13_6_5_TypingPath} {n start : Nat}
    (hDone : start + 4 <= n) :
    ex_13_6_5_wordConcreteEntrantTerminalNet word omega (n + 1) start -
      ex_13_6_5_wordConcreteEntrantTerminalNet word omega n start = 0 := by
  rw [ex_13_6_5_wordConcreteEntrantTerminalNet_stable_after_four hDone]
  ring

theorem ex_13_6_5_wordConcreteIIDEntrantBankrollProcess_zero
    (word : Fin 4 -> ex_13_6_5_Key) :
    ex_13_6_5_wordConcreteIIDEntrantBankrollProcess word 0 =
      fun _ : ex_13_6_5_TypingPath => (0 : Real) := by
  funext omega
  simp [ex_13_6_5_wordConcreteIIDEntrantBankrollProcess]

theorem ex_13_6_5_wordConcreteEntrantTerminalNet_abs_le
    (word : Fin 4 -> ex_13_6_5_Key)
    (omega : ex_13_6_5_TypingPath) (t start : Nat) :
    |ex_13_6_5_wordConcreteEntrantTerminalNet word omega t start| <= 80 := by
  classical
  by_cases hlt : start < t
  · by_cases hDone : start + 4 <= t
    · by_cases hPrefix :
        ex_13_6_5_wordFinPrefixMatches word omega start 4
      · simpa [ex_13_6_5_wordConcreteEntrantTerminalNet, hlt, hDone,
          hPrefix] using
          (ex_13_6_5_gamblerNetAfterWins_abs_le_four
            (wins := 4) (by norm_num))
      · norm_num [ex_13_6_5_wordConcreteEntrantTerminalNet, hlt, hDone,
          hPrefix]
    · by_cases hPrefix :
        ex_13_6_5_wordFinPrefixMatches word omega start (t - start)
      · have hwins : t - start <= 4 := by omega
        simpa [ex_13_6_5_wordConcreteEntrantTerminalNet, hlt, hDone,
          hPrefix] using
          (ex_13_6_5_gamblerNetAfterWins_abs_le_four
            (wins := t - start) hwins)
      · norm_num [ex_13_6_5_wordConcreteEntrantTerminalNet, hlt, hDone,
          hPrefix]
  · norm_num [ex_13_6_5_wordConcreteEntrantTerminalNet, hlt]
