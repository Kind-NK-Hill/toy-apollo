/-
TASK ID: ex_13_6_5_optional_stopping_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_13.ex_13_6_5_abab_support
import ProbabilityTheory.chapter_13.ex_13_6_5_aabb_support

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section



theorem ex_13_6_5_concrete_iid_entrant_team_structural_support :
    ProbabilityTheory.iIndepFun
        (fun n (ω : ex_13_6_5_TypingPath) => ω n)
        ex_13_6_5_typingMeasure ∧
      def_13_8 ex_13_6_5_typingNaturalFiltration
        ex_13_6_5_ababFirstOccurrence ∧
      def_13_8 ex_13_6_5_typingNaturalFiltration
        ex_13_6_5_aabbFirstOccurrence ∧
      (∀ n : ℕ,
        SigmaFinite
          (ex_13_6_5_typingMeasure.trim
            (ex_13_6_5_typingNaturalFiltration_le n))) ∧
      (ex_13_6_5_ababConcreteIIDEntrantBankrollProcess 0 =
        fun _ : ex_13_6_5_TypingPath => (0 : ℝ)) ∧
      (ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess 0 =
        fun _ : ex_13_6_5_TypingPath => (0 : ℝ)) ∧
      (∃ c : ℝ,
        0 ≤ c ∧
          ∀ n : ℕ, ∀ᵐ ω ∂ex_13_6_5_typingMeasure,
            |ex_13_6_5_ababConcreteIIDEntrantBankrollProcess (n + 1) ω -
              ex_13_6_5_ababConcreteIIDEntrantBankrollProcess n ω| ≤ c) ∧
      (∃ c : ℝ,
        0 ≤ c ∧
          ∀ n : ℕ, ∀ᵐ ω ∂ex_13_6_5_typingMeasure,
            |ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess (n + 1) ω -
              ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess n ω| ≤ c) ∧
      (∀ ω : ex_13_6_5_TypingPath,
        ex_13_6_5_ababFirstOccurrence ω ≠ ⊤ →
          ex_13_6_5_ababFirstOccurrence ω =
            (ex_13_6_5_ababWaitingTime ω : WithTop ℕ)) ∧
      (∀ ω : ex_13_6_5_TypingPath,
        ex_13_6_5_aabbFirstOccurrence ω ≠ ⊤ →
          ex_13_6_5_aabbFirstOccurrence ω =
            (ex_13_6_5_aabbWaitingTime ω : WithTop ℕ)) ∧
      (∀ (ω : ex_13_6_5_TypingPath) {t : ℕ},
        ex_13_6_5_ababFirstOccurrence ω = (t : WithTop ℕ) →
          thm_13_18_stoppedValueReal
              ex_13_6_5_ababConcreteIIDEntrantBankrollProcess
              ex_13_6_5_ababFirstOccurrence ω =
            ex_13_6_5_ababTerminalTeamGain (t : ℝ)) ∧
      (∀ (ω : ex_13_6_5_TypingPath) {t : ℕ},
        ex_13_6_5_aabbFirstOccurrence ω = (t : WithTop ℕ) →
          thm_13_18_stoppedValueReal
              ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess
              ex_13_6_5_aabbFirstOccurrence ω =
            ex_13_6_5_aabbTerminalTeamGain (t : ℝ)) := by
  refine ⟨ex_13_6_5_typingMeasure_iIndepFun,
    ex_13_6_5_ababFirstOccurrence_stoppingTime,
    ex_13_6_5_aabbFirstOccurrence_stoppingTime,
    ex_13_6_5_typingNaturalFiltration_sigmaFinite,
    ex_13_6_5_ababConcreteIIDEntrantBankrollProcess_zero,
    ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_zero,
    ex_13_6_5_ababConcreteIIDEntrantBankrollProcess_bounded_increments,
    ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_bounded_increments,
    ?_, ?_,
    ?_, ?_⟩
  · intro ω hFinite
    exact
      ex_13_6_5_firstOccurrence_eq_waitingTimeOf_of_finite
        (T := ex_13_6_5_ababFirstOccurrence) hFinite
  · intro ω hFinite
    exact
      ex_13_6_5_firstOccurrence_eq_waitingTimeOf_of_finite
        (T := ex_13_6_5_aabbFirstOccurrence) hFinite
  · intro ω t hT
    exact ex_13_6_5_abab_concrete_iid_entrant_bankroll_process ω hT
  · intro ω t hT
    exact ex_13_6_5_aabb_concrete_iid_entrant_bankroll_process ω hT



theorem ex_13_6_5_concrete_iid_entrant_team_corrected_filtration_support :
    def_13_6_isFiltration
        (𝓕 := inferInstanceAs (MeasurableSpace ex_13_6_5_TypingPath))
        ex_13_6_5_typingNaturalFiltrationBefore ∧
      def_13_8 ex_13_6_5_typingNaturalFiltrationBefore
        ex_13_6_5_ababFirstOccurrence ∧
      def_13_8 ex_13_6_5_typingNaturalFiltrationBefore
        ex_13_6_5_aabbFirstOccurrence ∧
      (∀ n : ℕ,
        SigmaFinite
          (ex_13_6_5_typingMeasure.trim
            (ex_13_6_5_typingNaturalFiltrationBefore_le n))) ∧
      def_13_6_adapted ex_13_6_5_typingNaturalFiltrationBefore
        ex_13_6_5_ababConcreteIIDEntrantBankrollProcess ∧
      def_13_6_adapted ex_13_6_5_typingNaturalFiltrationBefore
        ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess ∧
      (∀ n : ℕ,
        Integrable (ex_13_6_5_ababConcreteIIDEntrantBankrollProcess n)
          ex_13_6_5_typingMeasure) ∧
      (∀ n : ℕ,
        Integrable (ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess n)
          ex_13_6_5_typingMeasure) ∧
      (∀ n : ℕ,
        ex_13_6_5_typingMeasure[
          ex_13_6_5_ababConcreteIIDEntrantBankrollProcess n |
          ex_13_6_5_typingNaturalFiltrationBefore n] =
            ex_13_6_5_ababConcreteIIDEntrantBankrollProcess n) ∧
      (∀ n : ℕ,
        ex_13_6_5_typingMeasure[
          ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess n |
          ex_13_6_5_typingNaturalFiltrationBefore n] =
            ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess n) := by
  refine ⟨
    ex_13_6_5_typingNaturalFiltrationBefore_isFiltration_ambient,
    ex_13_6_5_ababFirstOccurrence_stoppingTimeBefore,
    ex_13_6_5_aabbFirstOccurrence_stoppingTimeBefore,
    ex_13_6_5_typingNaturalFiltrationBefore_sigmaFinite,
    ex_13_6_5_ababConcreteIIDEntrantBankrollProcess_adaptedBefore,
    ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_adaptedBefore,
    ex_13_6_5_ababConcreteIIDEntrantBankrollProcess_integrable,
    ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_integrable,
    ex_13_6_5_ababConcreteIIDEntrantBankrollProcess_condExp_selfBefore,
    ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_condExp_selfBefore⟩

theorem ex_13_6_5_ababConcreteIIDEntrantBankrollProcess_martingaleBefore :
    def_13_7 ex_13_6_5_typingMeasure
      ex_13_6_5_typingNaturalFiltrationBefore
      ex_13_6_5_ababConcreteIIDEntrantBankrollProcess := by
  exact ⟨
    ex_13_6_5_typingNaturalFiltrationBefore_isFiltration_ambient,
    ex_13_6_5_ababConcreteIIDEntrantBankrollProcess_integrable,
    ex_13_6_5_ababConcreteIIDEntrantBankrollProcess_adaptedBefore,
    ex_13_6_5_ababConcreteIIDEntrantBankrollProcess_oneStepConditionBefore⟩

theorem ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_martingaleBefore :
    def_13_7 ex_13_6_5_typingMeasure
      ex_13_6_5_typingNaturalFiltrationBefore
      ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess := by
  exact ⟨
    ex_13_6_5_typingNaturalFiltrationBefore_isFiltration_ambient,
    ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_integrable,
    ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_adaptedBefore,
    ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_oneStepConditionBefore⟩

theorem ex_13_6_5_concrete_iid_entrant_team_martingale_support :
    def_13_7 ex_13_6_5_typingMeasure
        ex_13_6_5_typingNaturalFiltrationBefore
        ex_13_6_5_ababConcreteIIDEntrantBankrollProcess ∧
      def_13_7 ex_13_6_5_typingMeasure
        ex_13_6_5_typingNaturalFiltrationBefore
        ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess :=
  ⟨ex_13_6_5_ababConcreteIIDEntrantBankrollProcess_martingaleBefore,
    ex_13_6_5_aabbConcreteIIDEntrantBankrollProcess_martingaleBefore⟩

 
def ex_13_6_5_uniformKeyMass (_k : ex_13_6_5_Key) : ℝ :=
  1 / 3

theorem ex_13_6_5_uniformKeyMass_total :
    ex_13_6_5_uniformKeyMass ex_13_6_5_Key.a +
        ex_13_6_5_uniformKeyMass ex_13_6_5_Key.b +
      ex_13_6_5_uniformKeyMass ex_13_6_5_Key.c = 1 := by
  norm_num [ex_13_6_5_uniformKeyMass]

 
def ex_13_6_5_wordCylinder (word : List ex_13_6_5_Key) :
    Set ex_13_6_5_TypingPath :=
  {ω | ∀ i : Fin word.length, ω i.1 = word.get i}

 
def ex_13_6_5_iidWordProbability (word : List ex_13_6_5_Key) : ℝ :=
  (1 / 3 : ℝ) ^ word.length

theorem ex_13_6_5_iidPatternProbabilities :
    ex_13_6_5_iidWordProbability ex_13_6_5_pattern_abab =
        (1 / 3 : ℝ) ^ 4 ∧
      ex_13_6_5_iidWordProbability ex_13_6_5_pattern_aabb =
        (1 / 3 : ℝ) ^ 4 := by
  constructor <;>
    norm_num [ex_13_6_5_iidWordProbability,
      ex_13_6_5_pattern_abab, ex_13_6_5_pattern_aabb]



structure ex_13_6_5_IIDThreeKeyTypingSpace where
  P : Measure ex_13_6_5_TypingPath
  probabilityMeasure : IsProbabilityMeasure P
  wordCylinder_probability :
    ∀ word : List ex_13_6_5_Key,
      P (ex_13_6_5_wordCylinder word) =
        ENNReal.ofReal (ex_13_6_5_iidWordProbability word)



def ex_13_6_5_terminalBankroll {Ω : Type*}
    (terminalGain : ℝ → ℝ) (waitingTime : Ω → ℕ) :
    ℕ → Ω → ℝ :=
  fun n ω =>
    if waitingTime ω ≤ n then terminalGain (waitingTime ω : ℝ) else 0



structure ex_13_6_5_GamblingTeamProcess {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (𝓕n : ℕ → MeasurableSpace Ω) where
  X : ℕ → Ω → ℝ
  T : Ω → WithTop ℕ
  waitingTime : Ω → ℕ
  teamRoundGain : ℕ → Ω → ℝ
  martingale : def_13_7 P 𝓕n X
  stoppingTime : def_13_8 𝓕n T
  startsWithNoActiveBankroll : X 0 =ᵐ[P] fun _ : Ω => (0 : ℝ)
  stopsAtWaitingTime : ∀ᵐ ω ∂P, T ω = (waitingTime ω : WithTop ℕ)
  waitingTime_integrable : Integrable (fun ω => (waitingTime ω : ℝ)) P
  bankrollUpdate :
    ∀ n : ℕ,
      (fun ω => X (n + 1) ω - X n ω) =ᵐ[P] teamRoundGain n
  teamRoundGain_uniformBounded :
    ∃ c : ℝ,
      0 ≤ c ∧
        ∀ n : ℕ, ∀ᵐ ω ∂P, |teamRoundGain n ω| ≤ c

theorem ex_13_6_5_GamblingTeamProcess_initialGain_integral_zero {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω}
    (G : ex_13_6_5_GamblingTeamProcess P 𝓕n) :
    ∫ ω, G.X 0 ω ∂P = 0 := by
  calc
    ∫ ω, G.X 0 ω ∂P = ∫ _ω : Ω, (0 : ℝ) ∂P :=
      integral_congr_ae G.startsWithNoActiveBankroll
    _ = 0 := by simp

theorem ex_13_6_5_GamblingTeamProcess_increment_bounded {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω}
    (G : ex_13_6_5_GamblingTeamProcess P 𝓕n) :
    ∃ c : ℝ,
      0 ≤ c ∧
        ∀ n : ℕ, ∀ᵐ ω ∂P, |G.X (n + 1) ω - G.X n ω| ≤ c := by
  rcases G.teamRoundGain_uniformBounded with ⟨c, hc_nonneg, hc_bound⟩
  refine ⟨c, hc_nonneg, ?_⟩
  intro n
  filter_upwards [G.bankrollUpdate n, hc_bound n] with ω hupdate hbound
  calc
    |G.X (n + 1) ω - G.X n ω| = |G.teamRoundGain n ω| := by
      rw [hupdate]
    _ ≤ c := hbound

theorem ex_13_6_5_GamblingTeamProcess_boundedIncrementCaseCanonical
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕n : ℕ → MeasurableSpace Ω}
    (G : ex_13_6_5_GamblingTeamProcess P 𝓕n) :
    thm_13_18_boundedIncrementCaseCanonical P G.X G.T :=
  ⟨G.waitingTime, G.stopsAtWaitingTime, G.waitingTime_integrable,
    ex_13_6_5_GamblingTeamProcess_increment_bounded G⟩

theorem ex_13_6_5_GamblingTeamProcess_optionalStoppingCasesCanonical
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕n : ℕ → MeasurableSpace Ω}
    (G : ex_13_6_5_GamblingTeamProcess P 𝓕n) :
    thm_13_18_optionalStoppingCasesCanonical P G.X G.T :=
  Or.inr
    (Or.inr
      (ex_13_6_5_GamblingTeamProcess_boundedIncrementCaseCanonical G))



theorem ex_13_6_5_teamGain_zero_from_optionalStopping {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕n : ℕ → MeasurableSpace Ω}
    (G : ex_13_6_5_GamblingTeamProcess P 𝓕n)
    (hSigmaFinite :
      ∀ n : ℕ,
        SigmaFinite (P.trim ((def_13_7_isFiltration G.martingale).1 n))) :
    ∫ ω, thm_13_18_stoppedValueReal G.X G.T ω ∂P = 0 := by
  calc
    ∫ ω, thm_13_18_stoppedValueReal G.X G.T ω ∂P =
        ∫ ω, G.X 0 ω ∂P :=
          thm_13_18_canonical G.martingale G.stoppingTime hSigmaFinite
            (ex_13_6_5_GamblingTeamProcess_optionalStoppingCasesCanonical G)
    _ = 0 :=
          ex_13_6_5_GamblingTeamProcess_initialGain_integral_zero G



structure ex_13_6_5_TerminalModeledGamblingTeamProcess {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (𝓕n : ℕ → MeasurableSpace Ω) (terminalGain : ℝ → ℝ) where
  T : Ω → WithTop ℕ
  waitingTime : Ω → ℕ
  teamRoundGain : ℕ → Ω → ℝ
  martingale :
    def_13_7 P 𝓕n
      (ex_13_6_5_terminalBankroll terminalGain waitingTime)
  stoppingTime : def_13_8 𝓕n T
  startsWithNoActiveBankroll :
    ex_13_6_5_terminalBankroll terminalGain waitingTime 0
      =ᵐ[P] fun _ : Ω => (0 : ℝ)
  stopsAtWaitingTime : ∀ᵐ ω ∂P, T ω = (waitingTime ω : WithTop ℕ)
  waitingTime_integrable : Integrable (fun ω => (waitingTime ω : ℝ)) P
  bankrollUpdate :
    ∀ n : ℕ,
      (fun ω =>
        ex_13_6_5_terminalBankroll terminalGain waitingTime (n + 1) ω -
          ex_13_6_5_terminalBankroll terminalGain waitingTime n ω)
        =ᵐ[P] teamRoundGain n
  teamRoundGain_uniformBounded :
    ∃ c : ℝ,
      0 ≤ c ∧
        ∀ n : ℕ, ∀ᵐ ω ∂P, |teamRoundGain n ω| ≤ c

def ex_13_6_5_TerminalModeledGamblingTeamProcess.toGamblingTeamProcess
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕n : ℕ → MeasurableSpace Ω} {terminalGain : ℝ → ℝ}
    (M :
      ex_13_6_5_TerminalModeledGamblingTeamProcess P 𝓕n
        terminalGain) :
    ex_13_6_5_GamblingTeamProcess P 𝓕n where
  X := ex_13_6_5_terminalBankroll terminalGain M.waitingTime
  T := M.T
  waitingTime := M.waitingTime
  teamRoundGain := M.teamRoundGain
  martingale := M.martingale
  stoppingTime := M.stoppingTime
  startsWithNoActiveBankroll := M.startsWithNoActiveBankroll
  stopsAtWaitingTime := M.stopsAtWaitingTime
  waitingTime_integrable := M.waitingTime_integrable
  bankrollUpdate := M.bankrollUpdate
  teamRoundGain_uniformBounded := M.teamRoundGain_uniformBounded

theorem ex_13_6_5_modeled_stoppedValue_eq_terminalTeamGain
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕n : ℕ → MeasurableSpace Ω} {terminalGain : ℝ → ℝ}
    (M :
      ex_13_6_5_TerminalModeledGamblingTeamProcess P 𝓕n
        terminalGain) :
    thm_13_18_stoppedValueReal
        (ex_13_6_5_terminalBankroll terminalGain M.waitingTime) M.T
      =ᵐ[P] fun ω => terminalGain (M.waitingTime ω : ℝ) := by
  filter_upwards [M.stopsAtWaitingTime] with ω hT
  simp [thm_13_18_stoppedValueReal,
    ex_13_6_5_terminalBankroll, hT]

abbrev ex_13_6_5_ababModeledGamblingTeamProcess {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (𝓕n : ℕ → MeasurableSpace Ω) :=
  ex_13_6_5_TerminalModeledGamblingTeamProcess P 𝓕n
    ex_13_6_5_ababTerminalTeamGain

abbrev ex_13_6_5_aabbModeledGamblingTeamProcess {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (𝓕n : ℕ → MeasurableSpace Ω) :=
  ex_13_6_5_TerminalModeledGamblingTeamProcess P 𝓕n
    ex_13_6_5_aabbTerminalTeamGain

theorem ex_13_6_5_abab_stoppedValue_eq_terminalTeamGain
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕n : ℕ → MeasurableSpace Ω}
    (M : ex_13_6_5_ababModeledGamblingTeamProcess P 𝓕n) :
    thm_13_18_stoppedValueReal
        (ex_13_6_5_terminalBankroll
          ex_13_6_5_ababTerminalTeamGain M.waitingTime) M.T
      =ᵐ[P]
        fun ω => ex_13_6_5_ababTerminalTeamGain
          (M.waitingTime ω : ℝ) :=
  ex_13_6_5_modeled_stoppedValue_eq_terminalTeamGain M

theorem ex_13_6_5_aabb_stoppedValue_eq_terminalTeamGain
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕n : ℕ → MeasurableSpace Ω}
    (M : ex_13_6_5_aabbModeledGamblingTeamProcess P 𝓕n) :
    thm_13_18_stoppedValueReal
        (ex_13_6_5_terminalBankroll
          ex_13_6_5_aabbTerminalTeamGain M.waitingTime) M.T
      =ᵐ[P]
        fun ω => ex_13_6_5_aabbTerminalTeamGain
          (M.waitingTime ω : ℝ) :=
  ex_13_6_5_modeled_stoppedValue_eq_terminalTeamGain M

theorem ex_13_6_5_abab_expectedWaitingTime_from_gamblingTeam
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕n : ℕ → MeasurableSpace Ω}
    (M : ex_13_6_5_ababModeledGamblingTeamProcess P 𝓕n)
    (hSigmaFinite :
      ∀ n : ℕ,
        SigmaFinite (P.trim ((def_13_7_isFiltration M.martingale).1 n))) :
    ∫ ω, (M.waitingTime ω : ℝ) ∂P = 90 := by
  let G :=
    ex_13_6_5_TerminalModeledGamblingTeamProcess.toGamblingTeamProcess M
  have hZero :
      ∫ ω, thm_13_18_stoppedValueReal G.X G.T ω ∂P = 0 :=
    ex_13_6_5_teamGain_zero_from_optionalStopping G (by
      simpa [G,
        ex_13_6_5_TerminalModeledGamblingTeamProcess.toGamblingTeamProcess]
        using hSigmaFinite)
  have hStoppedIntegral :
      ∫ ω,
          thm_13_18_stoppedValueReal
            (ex_13_6_5_terminalBankroll
              ex_13_6_5_ababTerminalTeamGain M.waitingTime) M.T ω ∂P =
        ∫ ω,
          ex_13_6_5_ababTerminalTeamGain (M.waitingTime ω : ℝ) ∂P :=
    integral_congr_ae
      (ex_13_6_5_abab_stoppedValue_eq_terminalTeamGain M)
  have hTerminalIntegral :
      ∫ ω,
          ex_13_6_5_ababTerminalTeamGain (M.waitingTime ω : ℝ) ∂P =
        90 - ∫ ω, (M.waitingTime ω : ℝ) ∂P :=
    ex_13_6_5_ababTerminalTeamGain_integral_eq
      (P := P) M.waitingTime_integrable
  have hSourceEquation :
      0 = 90 - ∫ ω, (M.waitingTime ω : ℝ) ∂P := by
    calc
      0 = ∫ ω, thm_13_18_stoppedValueReal G.X G.T ω ∂P :=
        hZero.symm
      _ =
          ∫ ω,
            thm_13_18_stoppedValueReal
              (ex_13_6_5_terminalBankroll
                ex_13_6_5_ababTerminalTeamGain M.waitingTime) M.T ω
              ∂P := by
            rfl
      _ = ∫ ω,
            ex_13_6_5_ababTerminalTeamGain (M.waitingTime ω : ℝ) ∂P :=
            hStoppedIntegral
      _ = 90 - ∫ ω, (M.waitingTime ω : ℝ) ∂P :=
            hTerminalIntegral
  linarith

theorem ex_13_6_5_aabb_expectedWaitingTime_from_gamblingTeam
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕n : ℕ → MeasurableSpace Ω}
    (M : ex_13_6_5_aabbModeledGamblingTeamProcess P 𝓕n)
    (hSigmaFinite :
      ∀ n : ℕ,
        SigmaFinite (P.trim ((def_13_7_isFiltration M.martingale).1 n))) :
    ∫ ω, (M.waitingTime ω : ℝ) ∂P = 81 := by
  let G :=
    ex_13_6_5_TerminalModeledGamblingTeamProcess.toGamblingTeamProcess M
  have hZero :
      ∫ ω, thm_13_18_stoppedValueReal G.X G.T ω ∂P = 0 :=
    ex_13_6_5_teamGain_zero_from_optionalStopping G (by
      simpa [G,
        ex_13_6_5_TerminalModeledGamblingTeamProcess.toGamblingTeamProcess]
        using hSigmaFinite)
  have hStoppedIntegral :
      ∫ ω,
          thm_13_18_stoppedValueReal
            (ex_13_6_5_terminalBankroll
              ex_13_6_5_aabbTerminalTeamGain M.waitingTime) M.T ω ∂P =
        ∫ ω,
          ex_13_6_5_aabbTerminalTeamGain (M.waitingTime ω : ℝ) ∂P :=
    integral_congr_ae
      (ex_13_6_5_aabb_stoppedValue_eq_terminalTeamGain M)
  have hTerminalIntegral :
      ∫ ω,
          ex_13_6_5_aabbTerminalTeamGain (M.waitingTime ω : ℝ) ∂P =
        81 - ∫ ω, (M.waitingTime ω : ℝ) ∂P :=
    ex_13_6_5_aabbTerminalTeamGain_integral_eq
      (P := P) M.waitingTime_integrable
  have hSourceEquation :
      0 = 81 - ∫ ω, (M.waitingTime ω : ℝ) ∂P := by
    calc
      0 = ∫ ω, thm_13_18_stoppedValueReal G.X G.T ω ∂P :=
        hZero.symm
      _ =
          ∫ ω,
            thm_13_18_stoppedValueReal
              (ex_13_6_5_terminalBankroll
                ex_13_6_5_aabbTerminalTeamGain M.waitingTime) M.T ω
              ∂P := by
            rfl
      _ = ∫ ω,
            ex_13_6_5_aabbTerminalTeamGain (M.waitingTime ω : ℝ) ∂P :=
            hStoppedIntegral
      _ = 81 - ∫ ω, (M.waitingTime ω : ℝ) ∂P :=
            hTerminalIntegral
  linarith
