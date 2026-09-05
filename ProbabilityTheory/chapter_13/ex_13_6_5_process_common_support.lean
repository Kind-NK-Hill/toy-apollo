/-
TASK ID: ex_13_6_5_process_common_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_13.ex_13_6_5_waiting_time_support

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section



def ex_13_6_5_lettersFromStart
    (ω : ex_13_6_5_TypingPath) (start wins : ℕ) :
    List ex_13_6_5_Key :=
  List.ofFn (fun i : Fin wins => ω (start + i.1))

theorem ex_13_6_5_gamblerNet_increment_eq_keyFairBetNet
    (wins : ℕ) (target observed : ex_13_6_5_Key) :
    (if observed = target then
        ex_13_6_5_gamblerNetAfterWins (wins + 1)
      else
        (-1 : ℝ)) -
        ex_13_6_5_gamblerNetAfterWins wins =
      ex_13_6_5_keyFairBetNet ((3 : ℝ) ^ wins) target observed := by
  by_cases hobs : observed = target
  · simp [hobs, ex_13_6_5_gamblerNetAfterWins,
      ex_13_6_5_keyFairBetNet, ex_13_6_5_fairBetNetGain]
    ring
  · simp [hobs, ex_13_6_5_gamblerNetAfterWins,
      ex_13_6_5_keyFairBetNet, ex_13_6_5_fairBetNetGain]
    ring

theorem ex_13_6_5_sum_range_single_terminal_bonus
    {t : ℕ} (ht : 4 ≤ t) :
    (∑ i ∈ Finset.range t,
      ((-1 : ℝ) + if i = t - 4 then (81 : ℝ) else 0)) =
      81 - (t : ℝ) := by
  rw [Finset.sum_add_distrib]
  have hFour :
      (∑ i ∈ Finset.range t,
          (if i = t - 4 then (81 : ℝ) else 0)) = 81 := by
    rw [Finset.sum_ite_eq']
    simp
    omega
  simp [hFour]
  ring

theorem ex_13_6_5_sum_range_double_terminal_bonus
    {t : ℕ} (ht : 4 ≤ t) :
    (∑ i ∈ Finset.range t,
      ((-1 : ℝ) +
        (if i = t - 4 then (81 : ℝ) else 0) +
          (if i = t - 2 then (9 : ℝ) else 0))) =
      90 - (t : ℝ) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hFour :
      (∑ i ∈ Finset.range t,
          (if i = t - 4 then (81 : ℝ) else 0)) = 81 := by
    rw [Finset.sum_ite_eq']
    simp
    omega
  have hTwo :
      (∑ i ∈ Finset.range t,
        (if i = t - 2 then (9 : ℝ) else 0)) = 9 := by
    rw [Finset.sum_ite_eq']
    simp
    omega
  simp [hFour, hTwo]
  ring

theorem ex_13_6_5_stoppedValueReal_eq_of_firstOccurrence
    {τ : ex_13_6_5_TypingPath → WithTop ℕ}
    {B : ℕ → ex_13_6_5_TypingPath → ℝ}
    {ω : ex_13_6_5_TypingPath} {t : ℕ} {v : ℝ}
    (hT : τ ω = (t : WithTop ℕ))
    (hB : B t ω = v) :
    thm_13_18_stoppedValueReal B τ ω = v := by
  change
    (match τ ω with
      | none => 0
      | some n => B n ω) = v
  rw [hT]
  simpa using hB
