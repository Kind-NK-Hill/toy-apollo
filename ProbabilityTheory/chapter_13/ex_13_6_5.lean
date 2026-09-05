/-
TASK ID: ex_13_6_5
TYPE: Example_Proof
SOURCE PLAN: chapter13-martingale-stopping-time
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_13.ex_13_6_5_optional_stopping_support




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



theorem ex_13_6_5_abab_expectedWaitingTime {E_T_abab E_after_a
    E_after_ab E_after_aba : ℝ}
    (h :
      ex_13_6_5_ababWaitingTimeEquations E_T_abab E_after_a
        E_after_ab E_after_aba) :
    E_T_abab = 90 :=
  ex_13_6_5_ababExpectedWaitingTime_unique h

 
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



theorem ex_13_6_5_aabb_shorter_than_abab :
    (81 : ℝ) < 90 := by
  norm_num

 
def ex_13_6_5_sampleAverage_abab : ℝ :=
  (891899 / 10000 : ℝ)

 
def ex_13_6_5_sampleAverage_aabb : ℝ :=
  (812196 / 10000 : ℝ)



theorem ex_13_6_5_sampleOutput_consistent :
    |ex_13_6_5_sampleAverage_abab - 90| < 1 ∧
      |ex_13_6_5_sampleAverage_aabb - 81| < 1 := by
  norm_num [ex_13_6_5_sampleAverage_abab,
    ex_13_6_5_sampleAverage_aabb]



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
