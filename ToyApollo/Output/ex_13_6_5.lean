import ToyApollo.Output.ex_13_6_5_optional_stopping_support

/-
TASK ID: ex_13_6_5
TYPE: Example_Proof
SOURCE PLAN: chapter13-martingale-stopping-time
TASK CONTENT:
\textbf{Example 13.6.5 (Martingale Patterns and Gambling Team)} \\

Suppose a monkey type randomly on a keyboard with only three keys: a, b, and c. Two players

bet on whether the pattern "abab" or "aabb" will appear first in the resulting random string. We

analyze who will win this game by computing the expected waiting time until we see each pattern.

We solve the prolem by introducing a casino. At each round, a random letter is drawn. A person

can bet m on the random outcome. He/she will receive 3 m if the guess is correct, but will lose all

of the bet otherwise. This makes it a fair game.

We first consider the pattern "abab"We introduce a team of gamblers, who enter the game

one at a time. Gambler i bets $1 at time i that the i -th letter is the
character "a"This gambler will

receive $3 if the letter "a" is drawn at time i but will leave otherwise. Then he will bet $3 to bet

the next drawn letter is "b"He will receive $9 if the letter at time i+ 1 is
indeed "b" but will leave

otherwise. The gambler will then bet $27 at time i+ 2 for the letter "a" and $81 at time i+ 3 for

t h el e t t e r" b " H ew i l ll e a v e t h eg a m ew h e n e v e rh el o s e s .

Assume that there are infinitely many potential gamblers waiting outside, and at each time, a

new gambler enters the game. We stop the game when a gambler has just won four times in a row.

This forms a stopped martingale satisfying the third condition in Theorem 13.18. Suppose the game

is stopped at time T At this time, exactly two gamblers are still in the game. The gambler who

entered at timeT- 1 wins $9. - $1 = $8, and the one who entered at time T- 3 wins $81. - $1=$80.

All other gamblers lose $1. By Theorem 13.18, the expected gain of the whole gambling team is 0,

0= E [X0]= E[XT ]= E[(T- 2 )(- $1)+ ( $81- $1 )+ ( $9- $1 )]= $90- $ E[T] .

Therefore, the expected waiting time for the string "abab" is 90.

If we change the pattern to "aabb", only one gambler is in the game when we first see the

pattern. A similar calculation shows that the expected waiting time is 81.

0= E [X0]= E[XT ]= E[(T- 1 )(- $1)+ $81 - $1 ]= $81- $ E[T] .

We simulate this experiment by the following Python program.

from random import choice

A = ['a','b','c'] # alphabet = {a,b,c}

def monkey(alphabet,pattern):

random_string = "" # initialize to empty string

while True:

random_string += choice(alphabet) # randomly draw a character

if random_string[-len(pattern):] == pattern:

break # break if we see the pattern at the end

return len(random_string) # return the length of the random string

n = 10000 # run the experiment n times

waiting_time1 = sum([monkey(A,'abab') for _ in range(n)])/n

waiting_time2 = sum([monkey(A,'aabb') for _ in range(n)])/n

print(f"Average waiting time for pattern abab = {waiting_time1}")

print(f"Average waiting time for pattern aabb = {waiting_time2}")

The function monkey generates a random string that ends with the given pattern and returns

the length of the random string. We run 10,000 experiments for each of the two patterns "abab"

and "aabb" and compute the average length of the random string. Note that the only difference

between the two experiments is the ending patterns. A sample output of the program is

Average waiting time for pattern abab = 89.1899

Average waiting time for pattern aabb = 81.2196

The simulation results are in accordance with the theoretic analysis.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

theorem ex_13_6_5_abab_concrete_stoppedValue_eq_terminalTeamGain_ae :
    thm_13_18_stoppedValueReal
        ex_13_6_5_ababConcreteIIDEntrantBankrollProcess
        ex_13_6_5_ababFirstOccurrence
      =ᵐ[ex_13_6_5_typingMeasure]
        fun ω : ex_13_6_5_TypingPath =>
          ex_13_6_5_ababTerminalTeamGain
            (ex_13_6_5_ababWaitingTime ω : ℝ) := by
  filter_upwards [ex_13_6_5_ababFirstOccurrence_stopsAtWaitingTime] with ω hT
  simpa using
    ex_13_6_5_abab_concrete_iid_entrant_bankroll_process
      ω (t := ex_13_6_5_ababWaitingTime ω) hT

theorem ex_13_6_5_aabb_concrete_stoppedValue_eq_terminalTeamGain_ae :
    thm_13_18_stoppedValueReal
        ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess
        ex_13_6_5_aabbFirstOccurrence
      =ᵐ[ex_13_6_5_typingMeasure]
        fun ω : ex_13_6_5_TypingPath =>
          ex_13_6_5_aabbTerminalTeamGain
            (ex_13_6_5_aabbWaitingTime ω : ℝ) := by
  filter_upwards [ex_13_6_5_aabbFirstOccurrence_stopsAtWaitingTime] with ω hT
  simpa using
    ex_13_6_5_aabb_concrete_iid_entrant_bankroll_process
      ω (t := ex_13_6_5_aabbWaitingTime ω) hT

theorem ex_13_6_5_abab_expectedWaitingTime_concrete :
    ∫ ω, (ex_13_6_5_ababWaitingTime ω : ℝ)
      ∂ex_13_6_5_typingMeasure = 90 := by
  let G :
      ex_13_6_5_GamblingTeamProcess ex_13_6_5_typingMeasure
        ex_13_6_5_typingNaturalFiltrationBefore :=
    { X := ex_13_6_5_ababConcreteIIDEntrantBankrollProcess
      T := ex_13_6_5_ababFirstOccurrence
      waitingTime := ex_13_6_5_ababWaitingTime
      teamRoundGain := ex_13_6_5_ababConcreteIIDTeamRoundGain
      martingale :=
        ex_13_6_5_ababConcreteIIDEntrantBankrollProcess_martingaleBefore
      stoppingTime := ex_13_6_5_ababFirstOccurrence_stoppingTimeBefore
      startsWithNoActiveBankroll :=
        ex_13_6_5_ababConcreteIIDEntrantBankrollProcess_startsWithNoActiveBankroll
      stopsAtWaitingTime := ex_13_6_5_ababFirstOccurrence_stopsAtWaitingTime
      waitingTime_integrable := ex_13_6_5_ababWaitingTime_integrable
      bankrollUpdate :=
        ex_13_6_5_ababConcreteIIDEntrantBankrollProcess_bankrollUpdate
      teamRoundGain_uniformBounded :=
        ex_13_6_5_ababConcreteIIDTeamRoundGain_uniformBounded }
  have hZero :
      ∫ ω, thm_13_18_stoppedValueReal
          ex_13_6_5_ababConcreteIIDEntrantBankrollProcess
          ex_13_6_5_ababFirstOccurrence ω
        ∂ex_13_6_5_typingMeasure = 0 := by
    simpa [G] using
      ex_13_6_5_teamGain_zero_from_optionalStopping G (by
        intro n
        simpa [G] using
          ex_13_6_5_typingNaturalFiltrationBefore_sigmaFinite n)
  have hStoppedIntegral :
      ∫ ω, thm_13_18_stoppedValueReal
          ex_13_6_5_ababConcreteIIDEntrantBankrollProcess
          ex_13_6_5_ababFirstOccurrence ω
        ∂ex_13_6_5_typingMeasure =
      ∫ ω,
          ex_13_6_5_ababTerminalTeamGain
            (ex_13_6_5_ababWaitingTime ω : ℝ)
        ∂ex_13_6_5_typingMeasure :=
    integral_congr_ae
      ex_13_6_5_abab_concrete_stoppedValue_eq_terminalTeamGain_ae
  have hTerminalIntegral :
      ∫ ω,
          ex_13_6_5_ababTerminalTeamGain
            (ex_13_6_5_ababWaitingTime ω : ℝ)
        ∂ex_13_6_5_typingMeasure =
        90 - ∫ ω, (ex_13_6_5_ababWaitingTime ω : ℝ)
          ∂ex_13_6_5_typingMeasure :=
    ex_13_6_5_ababTerminalTeamGain_integral_eq
      (P := ex_13_6_5_typingMeasure)
      ex_13_6_5_ababWaitingTime_integrable
  have hSourceEquation :
      0 = 90 - ∫ ω, (ex_13_6_5_ababWaitingTime ω : ℝ)
        ∂ex_13_6_5_typingMeasure := by
    calc
      0 = ∫ ω, thm_13_18_stoppedValueReal
          ex_13_6_5_ababConcreteIIDEntrantBankrollProcess
          ex_13_6_5_ababFirstOccurrence ω
        ∂ex_13_6_5_typingMeasure := hZero.symm
      _ = ∫ ω,
          ex_13_6_5_ababTerminalTeamGain
            (ex_13_6_5_ababWaitingTime ω : ℝ)
        ∂ex_13_6_5_typingMeasure := hStoppedIntegral
      _ = 90 - ∫ ω, (ex_13_6_5_ababWaitingTime ω : ℝ)
        ∂ex_13_6_5_typingMeasure := hTerminalIntegral
  linarith

theorem ex_13_6_5_aabb_expectedWaitingTime_concrete :
    ∫ ω, (ex_13_6_5_aabbWaitingTime ω : ℝ)
      ∂ex_13_6_5_typingMeasure = 81 := by
  let G :
      ex_13_6_5_GamblingTeamProcess ex_13_6_5_typingMeasure
        ex_13_6_5_typingNaturalFiltrationBefore :=
    { X := ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess
      T := ex_13_6_5_aabbFirstOccurrence
      waitingTime := ex_13_6_5_aabbWaitingTime
      teamRoundGain := ex_13_6_5_aabbConcreteIIDTeamRoundGain
      martingale :=
        ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_martingaleBefore
      stoppingTime := ex_13_6_5_aabbFirstOccurrence_stoppingTimeBefore
      startsWithNoActiveBankroll :=
        ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_startsWithNoActiveBankroll
      stopsAtWaitingTime := ex_13_6_5_aabbFirstOccurrence_stopsAtWaitingTime
      waitingTime_integrable := ex_13_6_5_aabbWaitingTime_integrable
      bankrollUpdate :=
        ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_bankrollUpdate
      teamRoundGain_uniformBounded :=
        ex_13_6_5_aabbConcreteIIDTeamRoundGain_uniformBounded }
  have hZero :
      ∫ ω, thm_13_18_stoppedValueReal
          ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess
          ex_13_6_5_aabbFirstOccurrence ω
        ∂ex_13_6_5_typingMeasure = 0 := by
    simpa [G] using
      ex_13_6_5_teamGain_zero_from_optionalStopping G (by
        intro n
        simpa [G] using
          ex_13_6_5_typingNaturalFiltrationBefore_sigmaFinite n)
  have hStoppedIntegral :
      ∫ ω, thm_13_18_stoppedValueReal
          ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess
          ex_13_6_5_aabbFirstOccurrence ω
        ∂ex_13_6_5_typingMeasure =
      ∫ ω,
          ex_13_6_5_aabbTerminalTeamGain
            (ex_13_6_5_aabbWaitingTime ω : ℝ)
        ∂ex_13_6_5_typingMeasure :=
    integral_congr_ae
      ex_13_6_5_aabb_concrete_stoppedValue_eq_terminalTeamGain_ae
  have hTerminalIntegral :
      ∫ ω,
          ex_13_6_5_aabbTerminalTeamGain
            (ex_13_6_5_aabbWaitingTime ω : ℝ)
        ∂ex_13_6_5_typingMeasure =
        81 - ∫ ω, (ex_13_6_5_aabbWaitingTime ω : ℝ)
          ∂ex_13_6_5_typingMeasure :=
    ex_13_6_5_aabbTerminalTeamGain_integral_eq
      (P := ex_13_6_5_typingMeasure)
      ex_13_6_5_aabbWaitingTime_integrable
  have hSourceEquation :
      0 = 81 - ∫ ω, (ex_13_6_5_aabbWaitingTime ω : ℝ)
        ∂ex_13_6_5_typingMeasure := by
    calc
      0 = ∫ ω, thm_13_18_stoppedValueReal
          ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess
          ex_13_6_5_aabbFirstOccurrence ω
        ∂ex_13_6_5_typingMeasure := hZero.symm
      _ = ∫ ω,
          ex_13_6_5_aabbTerminalTeamGain
            (ex_13_6_5_aabbWaitingTime ω : ℝ)
        ∂ex_13_6_5_typingMeasure := hStoppedIntegral
      _ = 81 - ∫ ω, (ex_13_6_5_aabbWaitingTime ω : ℝ)
        ∂ex_13_6_5_typingMeasure := hTerminalIntegral
  linarith

/-- The first-step equations for the four `abab` prefix states, with `E0`
the expected waiting time from no matched prefix. -/
def ex_13_6_5_ababWaitingTimeEquations
    (E0 E1 E2 E3 : ℝ) : Prop :=
  E0 = 1 + (1 / 3) * E1 + (2 / 3) * E0 ∧
    E1 = 1 + (1 / 3) * E1 + (1 / 3) * E2 + (1 / 3) * E0 ∧
      E2 = 1 + (1 / 3) * E3 + (2 / 3) * E0 ∧
        E3 = 1 + (1 / 3) * E1 + (1 / 3) * E0

theorem ex_13_6_5_ababWaitingTimeEquations_solution :
    ex_13_6_5_ababWaitingTimeEquations 90 87 81 60 := by
  norm_num [ex_13_6_5_ababWaitingTimeEquations]

theorem ex_13_6_5_ababExpectedWaitingTime_unique {E0 E1 E2 E3 : ℝ}
    (h : ex_13_6_5_ababWaitingTimeEquations E0 E1 E2 E3) :
    E0 = 90 := by
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

/-- Source-facing expectation conclusion for the `abab` waiting time: any
solution of the textbook first-step expectation equations has `E[T_abab]=90`. -/
theorem ex_13_6_5_abab_expectedWaitingTime {E_T_abab E_after_a
    E_after_ab E_after_aba : ℝ}
    (h :
      ex_13_6_5_ababWaitingTimeEquations E_T_abab E_after_a
        E_after_ab E_after_aba) :
    E_T_abab = 90 :=
  ex_13_6_5_ababExpectedWaitingTime_unique h

/-- The first-step equations for the four `aabb` prefix states. -/
def ex_13_6_5_aabbWaitingTimeEquations
    (E0 E1 E2 E3 : ℝ) : Prop :=
  E0 = 1 + (1 / 3) * E1 + (2 / 3) * E0 ∧
    E1 = 1 + (1 / 3) * E2 + (2 / 3) * E0 ∧
      E2 = 1 + (1 / 3) * E2 + (1 / 3) * E3 + (1 / 3) * E0 ∧
        E3 = 1 + (1 / 3) * E1 + (1 / 3) * E0

theorem ex_13_6_5_aabbWaitingTimeEquations_solution :
    ex_13_6_5_aabbWaitingTimeEquations 81 78 69 54 := by
  norm_num [ex_13_6_5_aabbWaitingTimeEquations]

theorem ex_13_6_5_aabbExpectedWaitingTime_unique {E0 E1 E2 E3 : ℝ}
    (h : ex_13_6_5_aabbWaitingTimeEquations E0 E1 E2 E3) :
    E0 = 81 := by
  rcases h with ⟨h0, h1, h2, h3⟩
  linarith

/-- Source-facing expectation conclusion for the `aabb` waiting time: any
solution of the textbook first-step expectation equations has `E[T_aabb]=81`. -/
theorem ex_13_6_5_aabb_expectedWaitingTime {E_T_aabb E_after_a
    E_after_aa E_after_aab : ℝ}
    (h :
      ex_13_6_5_aabbWaitingTimeEquations E_T_aabb E_after_a
        E_after_aa E_after_aab) :
    E_T_aabb = 81 :=
  ex_13_6_5_aabbExpectedWaitingTime_unique h

theorem ex_13_6_5_abab_expectedWaitingTime_from_sourceEquation
    {E_T_abab : ℝ} (h : 0 = 90 - E_T_abab) :
    E_T_abab = 90 := by
  linarith

theorem ex_13_6_5_aabb_expectedWaitingTime_from_sourceEquation
    {E_T_aabb : ℝ} (h : 0 = 81 - E_T_aabb) :
    E_T_aabb = 81 := by
  linarith

/-- The theoretical waiting-time comparison in the example: `aabb` has the
smaller expected waiting time. -/
theorem ex_13_6_5_aabb_shorter_than_abab :
    (81 : ℝ) < 90 := by
  norm_num

/-- The sample average printed in the source simulation for `abab`. -/
def ex_13_6_5_sampleAverage_abab : ℝ :=
  (891899 / 10000 : ℝ)

/-- The sample average printed in the source simulation for `aabb`. -/
def ex_13_6_5_sampleAverage_aabb : ℝ :=
  (812196 / 10000 : ℝ)

/-- The displayed simulation output is close to the theoretical values stated
above.  This records the empirical confirmation from the source text without
turning the simulation into a proof of the theorem. -/
theorem ex_13_6_5_sampleOutput_consistent :
    |ex_13_6_5_sampleAverage_abab - 90| < 1 ∧
      |ex_13_6_5_sampleAverage_aabb - 81| < 1 := by
  norm_num [ex_13_6_5_sampleAverage_abab,
    ex_13_6_5_sampleAverage_aabb]

/-- Example 13.6.5: the gambling-team optional-stopping route gives expected
waiting times `90` for `abab` and `81` for `aabb`, so `aabb` is shorter in
expectation.  The first two conjuncts are closed statements about the actual
iid three-key typing process; the remaining conjuncts record the payoff algebra
and displayed simulation check. -/
theorem ex_13_6_5 :
    (∫ ω, (ex_13_6_5_ababWaitingTime ω : ℝ)
      ∂ex_13_6_5_typingMeasure = 90) ∧
      (∫ ω, (ex_13_6_5_aabbWaitingTime ω : ℝ)
        ∂ex_13_6_5_typingMeasure = 81) ∧
        (∀ t : ℝ, ex_13_6_5_ababTerminalTeamGain t = 90 - t) ∧
          (∀ t : ℝ, ex_13_6_5_aabbTerminalTeamGain t = 81 - t) ∧
            (81 : ℝ) < 90 ∧
              (|ex_13_6_5_sampleAverage_abab - 90| < 1 ∧
                |ex_13_6_5_sampleAverage_aabb - 81| < 1) := by
  exact ⟨ex_13_6_5_abab_expectedWaitingTime_concrete,
    ex_13_6_5_aabb_expectedWaitingTime_concrete,
    ex_13_6_5_ababTerminalTeamGain_eq,
    ex_13_6_5_aabbTerminalTeamGain_eq,
    ex_13_6_5_aabb_shorter_than_abab,
    ex_13_6_5_sampleOutput_consistent⟩
