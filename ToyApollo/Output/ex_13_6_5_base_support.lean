/-
TASK ID: ex_13_6_5_base_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Support.IIDWord
import ToyApollo.Output.def_13_6

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

inductive ex_13_6_5_Key where
  | a
  | b
  | c
deriving DecidableEq, Repr, Fintype

instance ex_13_6_5_keyInhabited : Inhabited ex_13_6_5_Key :=
  ⟨ex_13_6_5_Key.a⟩

instance ex_13_6_5_keyMeasurableSpace :
    MeasurableSpace ex_13_6_5_Key := ⊤

def ex_13_6_5_pattern_abab : List ex_13_6_5_Key :=
  [ex_13_6_5_Key.a, ex_13_6_5_Key.b, ex_13_6_5_Key.a,
    ex_13_6_5_Key.b]

def ex_13_6_5_pattern_aabb : List ex_13_6_5_Key :=
  [ex_13_6_5_Key.a, ex_13_6_5_Key.a, ex_13_6_5_Key.b,
    ex_13_6_5_Key.b]

theorem ex_13_6_5_pattern_abab_length :
    ex_13_6_5_pattern_abab.length = 4 := by
  rfl

theorem ex_13_6_5_pattern_aabb_length :
    ex_13_6_5_pattern_aabb.length = 4 := by
  rfl

def ex_13_6_5_ababWordFin : Fin 4 → ex_13_6_5_Key := fun i =>
  ex_13_6_5_pattern_abab.get
    ⟨i.1, by simpa [ex_13_6_5_pattern_abab] using i.2⟩

def ex_13_6_5_aabbWordFin : Fin 4 → ex_13_6_5_Key := fun i =>
  ex_13_6_5_pattern_aabb.get
    ⟨i.1, by simpa [ex_13_6_5_pattern_aabb] using i.2⟩

def ex_13_6_5_fairBetNetGain (m : ℝ) (correct : Bool) : ℝ :=
  if correct then 3 * m - m else -m

theorem ex_13_6_5_fairBet_expected_zero (m : ℝ) :
    (1 / 3 : ℝ) * ex_13_6_5_fairBetNetGain m true +
      (2 / 3 : ℝ) * ex_13_6_5_fairBetNetGain m false = 0 := by
  simp [ex_13_6_5_fairBetNetGain]
  ring

def ex_13_6_5_keyFairBetNet
    (m : ℝ) (target observed : ex_13_6_5_Key) : ℝ :=
  ex_13_6_5_fairBetNetGain m (observed = target)

theorem ex_13_6_5_keyFairBetNet_measurable
    (m : ℝ) (target : ex_13_6_5_Key) :
    Measurable fun observed : ex_13_6_5_Key =>
      ex_13_6_5_keyFairBetNet m target observed := by
  classical
  simp [ex_13_6_5_keyFairBetNet, ex_13_6_5_fairBetNetGain]
  exact Measurable.ite (measurableSet_singleton target)
    measurable_const measurable_const

def ex_13_6_5_gamblerNetAfterWins (wins : ℕ) : ℝ :=
  (3 : ℝ) ^ wins - 1

theorem ex_13_6_5_fourWins_netGain :
    ex_13_6_5_gamblerNetAfterWins 4 = 80 := by
  norm_num [ex_13_6_5_gamblerNetAfterWins]

theorem ex_13_6_5_twoWins_netGain :
    ex_13_6_5_gamblerNetAfterWins 2 = 8 := by
  norm_num [ex_13_6_5_gamblerNetAfterWins]

theorem ex_13_6_5_gamblerNetAfterWins_abs_le_four
    {wins : ℕ} (hwins : wins ≤ 4) :
    |ex_13_6_5_gamblerNetAfterWins wins| ≤ 80 := by
  interval_cases wins <;> norm_num [ex_13_6_5_gamblerNetAfterWins]

theorem ex_13_6_5_active_start_card_le_four (n : ℕ) :
    ((Finset.range (n + 1)).filter (fun start : ℕ => n < start + 4)).card ≤ 4 := by
  have hcard :=
    Finset.card_le_card_of_injOn
      (s := (Finset.range (n + 1)).filter (fun start : ℕ => n < start + 4))
      (t := Finset.range 4)
      (f := fun start : ℕ => n - start)
      (by
        intro start hstart
        have hstart_range : start < n + 1 :=
          Finset.mem_range.mp (Finset.mem_filter.mp hstart).1
        have hstart_active : n < start + 4 := (Finset.mem_filter.mp hstart).2
        have hstart_le : start ≤ n := Nat.lt_succ_iff.mp hstart_range
        have hsub_lt : n - start < 4 := by
          rw [tsub_lt_iff_right hstart_le]
          omega
        exact Finset.mem_range.mpr hsub_lt)
      (by
        intro x hx y hy hxy
        have hx_range : x < n + 1 :=
          Finset.mem_range.mp (Finset.mem_filter.mp hx).1
        have hy_range : y < n + 1 :=
          Finset.mem_range.mp (Finset.mem_filter.mp hy).1
        have hx_le : x ≤ n := Nat.lt_succ_iff.mp hx_range
        have hy_le : y ≤ n := Nat.lt_succ_iff.mp hy_range
        have hx_add : n - x + x = n := Nat.sub_add_cancel hx_le
        have hy_add : n - y + y = n := Nat.sub_add_cancel hy_le
        have hEq : n - x + x = n - y + y := by
          rw [hx_add, hy_add]
        have hEq' : n - y + x = n - y + y := by
          simpa [hxy] using hEq
        exact Nat.add_left_cancel hEq')
  simpa [Finset.card_range] using hcard

theorem ex_13_6_5_sum_range_extend (n : ℕ) (f : ℕ → ℝ) :
    (∑ start ∈ Finset.range n, f start) =
      ∑ start ∈ Finset.range (n + 1), (if start < n then f start else 0) := by
  rw [Finset.sum_range_succ]
  simp
  apply Finset.sum_congr rfl
  intro start hstart
  have hlt : start < n := Finset.mem_range.mp hstart
  simp [hlt]

theorem ex_13_6_5_bankroll_increment_abs_le
    {Ω : Type*} (net : Ω → ℕ → ℕ → ℝ)
    (hStable :
      ∀ (ω : Ω) (n start : ℕ),
        start + 4 ≤ n → net ω (n + 1) start = net ω n start)
    (hBound : ∀ (ω : Ω) (t start : ℕ), |net ω t start| ≤ 80)
    (n : ℕ) (ω : Ω) :
    |(∑ start ∈ Finset.range (n + 1), net ω (n + 1) start) -
      (∑ start ∈ Finset.range n, net ω n start)| ≤ 640 := by
  let term : ℕ → ℝ :=
    fun start => net ω (n + 1) start -
      if start < n then net ω n start else 0
  have hOld :
      (∑ start ∈ Finset.range n, net ω n start) =
        ∑ start ∈ Finset.range (n + 1),
          (if start < n then net ω n start else 0) :=
    ex_13_6_5_sum_range_extend n (fun start => net ω n start)
  have hdiff :
      (∑ start ∈ Finset.range (n + 1), net ω (n + 1) start) -
        (∑ start ∈ Finset.range n, net ω n start) =
        ∑ start ∈ Finset.range (n + 1), term start := by
    rw [hOld, ← Finset.sum_sub_distrib]
  have hterm_zero :
      ∀ start ∈ Finset.range (n + 1),
        ¬ n < start + 4 → term start = 0 := by
    intro start hstart hnot
    have hle_done : start + 4 ≤ n := le_of_not_gt hnot
    have hlt : start < n := by
      have hs : start < n + 1 := Finset.mem_range.mp hstart
      omega
    simp [term, hlt, hStable ω n start hle_done]
  have hfilter :
      (∑ start ∈ Finset.range (n + 1), term start) =
        ∑ start ∈
          (Finset.range (n + 1)).filter (fun start : ℕ => n < start + 4),
          term start := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro start hstart
    by_cases hactive : n < start + 4
    · simp [hactive]
    · simp [hactive, hterm_zero start hstart hactive]
  have hterm_bound :
      ∀ start ∈
          (Finset.range (n + 1)).filter (fun start : ℕ => n < start + 4),
        |term start| ≤ 160 := by
    intro start hstart
    have ha : |net ω (n + 1) start| ≤ 80 := hBound ω (n + 1) start
    have hb : |(if start < n then net ω n start else 0)| ≤ 80 := by
      by_cases hlt : start < n
      · simpa [hlt] using hBound ω n start
      · simp [hlt]
    calc
      |term start| =
          |net ω (n + 1) start -
            (if start < n then net ω n start else 0)| := rfl
      _ ≤ |net ω (n + 1) start| +
          |(if start < n then net ω n start else 0)| := abs_sub _ _
      _ ≤ 80 + 80 := add_le_add ha hb
      _ = 160 := by norm_num
  have hsum_abs :
      |∑ start ∈
          (Finset.range (n + 1)).filter (fun start : ℕ => n < start + 4),
          term start| ≤
        ∑ start ∈
          (Finset.range (n + 1)).filter (fun start : ℕ => n < start + 4),
          |term start| :=
    Finset.abs_sum_le_sum_abs term
      ((Finset.range (n + 1)).filter (fun start : ℕ => n < start + 4))
  have hsum_le :
      (∑ start ∈
          (Finset.range (n + 1)).filter (fun start : ℕ => n < start + 4),
          |term start|) ≤
        ∑ start ∈
          (Finset.range (n + 1)).filter (fun start : ℕ => n < start + 4),
          (160 : ℝ) := by
    apply Finset.sum_le_sum
    intro start hstart
    exact hterm_bound start hstart
  have hcard :
      (((Finset.range (n + 1)).filter
        (fun start : ℕ => n < start + 4)).card : ℝ) ≤ 4 := by
    exact_mod_cast ex_13_6_5_active_start_card_le_four n
  have hconst :
      (∑ start ∈
          (Finset.range (n + 1)).filter (fun start : ℕ => n < start + 4),
          (160 : ℝ)) ≤ 640 := by
    rw [Finset.sum_const]
    simp [nsmul_eq_mul]
    nlinarith
  calc
    |(∑ start ∈ Finset.range (n + 1), net ω (n + 1) start) -
      (∑ start ∈ Finset.range n, net ω n start)| =
        |∑ start ∈ Finset.range (n + 1), term start| := by
          rw [hdiff]
    _ = |∑ start ∈
          (Finset.range (n + 1)).filter (fun start : ℕ => n < start + 4),
          term start| := by
          rw [hfilter]
    _ ≤ ∑ start ∈
          (Finset.range (n + 1)).filter (fun start : ℕ => n < start + 4),
          |term start| := hsum_abs
    _ ≤ ∑ start ∈
          (Finset.range (n + 1)).filter (fun start : ℕ => n < start + 4),
          (160 : ℝ) := hsum_le
    _ ≤ 640 := hconst

def ex_13_6_5_losingEntrantsContribution (t survivors : ℝ) : ℝ :=
  (t - survivors) * (-1)

def ex_13_6_5_entrantTerminalTeamGain
    (t : ℝ) (survivorWins : List ℕ) : ℝ :=
  ex_13_6_5_losingEntrantsContribution t survivorWins.length +
    (survivorWins.map ex_13_6_5_gamblerNetAfterWins).sum

def ex_13_6_5_ababSurvivorWinLengths : List ℕ := [4, 2]

theorem ex_13_6_5_abab_survivor_count :
    ex_13_6_5_ababSurvivorWinLengths.length = 2 := by
  rfl

def ex_13_6_5_aabbSurvivorWinLengths : List ℕ := [4]

theorem ex_13_6_5_aabb_survivor_count :
    ex_13_6_5_aabbSurvivorWinLengths.length = 1 := by
  rfl

def ex_13_6_5_isTerminalSurvivorWinLength
    (pattern : List ex_13_6_5_Key) (wins : ℕ) : Bool :=
  decide (0 < wins) &&
    decide (wins ≤ pattern.length) &&
      decide
        (pattern.drop (pattern.length - wins) =
          pattern.take wins)

def ex_13_6_5_terminalSurvivorWinLengthsFromPattern
    (pattern : List ex_13_6_5_Key) : List ℕ :=
  ((List.range (pattern.length + 1)).reverse).filter
    (ex_13_6_5_isTerminalSurvivorWinLength pattern)

theorem ex_13_6_5_abab_terminalSurvivorWinLengthsFromPattern :
    ex_13_6_5_terminalSurvivorWinLengthsFromPattern
        ex_13_6_5_pattern_abab =
      ex_13_6_5_ababSurvivorWinLengths := by
  native_decide

theorem ex_13_6_5_aabb_terminalSurvivorWinLengthsFromPattern :
    ex_13_6_5_terminalSurvivorWinLengthsFromPattern
        ex_13_6_5_pattern_aabb =
      ex_13_6_5_aabbSurvivorWinLengths := by
  native_decide

theorem ex_13_6_5_abab_survivor_suffix_prefix_lengths :
    ex_13_6_5_ababSurvivorWinLengths = [4, 2] := by
  rfl

theorem ex_13_6_5_aabb_survivor_suffix_prefix_lengths :
    ex_13_6_5_aabbSurvivorWinLengths = [4] := by
  rfl

def ex_13_6_5_ababTerminalTeamGain (t : ℝ) : ℝ :=
  ex_13_6_5_entrantTerminalTeamGain t
    ex_13_6_5_ababSurvivorWinLengths

theorem ex_13_6_5_ababTerminalTeamGain_sourceFormula (t : ℝ) :
    ex_13_6_5_ababTerminalTeamGain t =
      (t - 2) * (-1) + (81 - 1) + (9 - 1) := by
  simp [ex_13_6_5_ababTerminalTeamGain,
    ex_13_6_5_entrantTerminalTeamGain,
    ex_13_6_5_ababSurvivorWinLengths,
    ex_13_6_5_losingEntrantsContribution,
    ex_13_6_5_gamblerNetAfterWins]
  ring

theorem ex_13_6_5_ababTerminalTeamGain_eq (t : ℝ) :
    ex_13_6_5_ababTerminalTeamGain t = 90 - t := by
  rw [ex_13_6_5_ababTerminalTeamGain_sourceFormula]
  ring

theorem ex_13_6_5_abab_concrete_stoppedValue_eq_terminalTeamGain
    (t : ℝ) :
    ex_13_6_5_entrantTerminalTeamGain t
        (ex_13_6_5_terminalSurvivorWinLengthsFromPattern
          ex_13_6_5_pattern_abab) =
      ex_13_6_5_ababTerminalTeamGain t := by
  rw [ex_13_6_5_abab_terminalSurvivorWinLengthsFromPattern]
  rfl

theorem ex_13_6_5_ababTerminalTeamGain_integral_eq {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {τ : Ω → ℝ} (hτ : Integrable τ P) :
    ∫ ω, ex_13_6_5_ababTerminalTeamGain (τ ω) ∂P =
      90 - ∫ ω, τ ω ∂P := by
  calc
    ∫ ω, ex_13_6_5_ababTerminalTeamGain (τ ω) ∂P =
        ∫ ω, (90 : ℝ) - τ ω ∂P := by
          apply integral_congr_ae
          filter_upwards with ω
          exact ex_13_6_5_ababTerminalTeamGain_eq (τ ω)
    _ = ∫ ω, (fun _ : Ω => (90 : ℝ)) ω ∂P -
        ∫ ω, τ ω ∂P := by
          exact integral_sub (integrable_const (90 : ℝ)) hτ
    _ = 90 - ∫ ω, τ ω ∂P := by
          simp

def ex_13_6_5_aabbTerminalTeamGain (t : ℝ) : ℝ :=
  ex_13_6_5_entrantTerminalTeamGain t
    ex_13_6_5_aabbSurvivorWinLengths

theorem ex_13_6_5_aabbTerminalTeamGain_sourceFormula (t : ℝ) :
    ex_13_6_5_aabbTerminalTeamGain t =
      (t - 1) * (-1) + (81 - 1) := by
  simp [ex_13_6_5_aabbTerminalTeamGain,
    ex_13_6_5_entrantTerminalTeamGain,
    ex_13_6_5_aabbSurvivorWinLengths,
    ex_13_6_5_losingEntrantsContribution,
    ex_13_6_5_gamblerNetAfterWins]
  ring

theorem ex_13_6_5_aabbTerminalTeamGain_eq (t : ℝ) :
    ex_13_6_5_aabbTerminalTeamGain t = 81 - t := by
  rw [ex_13_6_5_aabbTerminalTeamGain_sourceFormula]
  ring

theorem ex_13_6_5_aabb_concrete_stoppedValue_eq_terminalTeamGain
    (t : ℝ) :
    ex_13_6_5_entrantTerminalTeamGain t
        (ex_13_6_5_terminalSurvivorWinLengthsFromPattern
          ex_13_6_5_pattern_aabb) =
      ex_13_6_5_aabbTerminalTeamGain t := by
  rw [ex_13_6_5_aabb_terminalSurvivorWinLengthsFromPattern]
  rfl

theorem ex_13_6_5_aabbTerminalTeamGain_integral_eq {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {τ : Ω → ℝ} (hτ : Integrable τ P) :
    ∫ ω, ex_13_6_5_aabbTerminalTeamGain (τ ω) ∂P =
      81 - ∫ ω, τ ω ∂P := by
  calc
    ∫ ω, ex_13_6_5_aabbTerminalTeamGain (τ ω) ∂P =
        ∫ ω, (81 : ℝ) - τ ω ∂P := by
          apply integral_congr_ae
          filter_upwards with ω
          exact ex_13_6_5_aabbTerminalTeamGain_eq (τ ω)
    _ = ∫ ω, (fun _ : Ω => (81 : ℝ)) ω ∂P -
        ∫ ω, τ ω ∂P := by
          exact integral_sub (integrable_const (81 : ℝ)) hτ
    _ = 81 - ∫ ω, τ ω ∂P := by
          simp

abbrev ex_13_6_5_TypingPath := ℕ → ex_13_6_5_Key

theorem ex_13_6_5_coord_eq_measurableSet
    (idx : ℕ) (k : ex_13_6_5_Key) :
    MeasurableSet {ω : ex_13_6_5_TypingPath | ω idx = k} := by
  change MeasurableSet
    ((fun ω : ex_13_6_5_TypingPath => ω idx) ⁻¹'
      ({k} : Set ex_13_6_5_Key))
  exact measurable_pi_apply idx (measurableSet_singleton k)

noncomputable def ex_13_6_5_keyMeasure :
    Measure ex_13_6_5_Key :=
  (PMF.uniformOfFintype ex_13_6_5_Key).toMeasure

instance ex_13_6_5_keyMeasure_isProbabilityMeasure :
    IsProbabilityMeasure ex_13_6_5_keyMeasure := by
  dsimp [ex_13_6_5_keyMeasure]
  infer_instance

theorem ex_13_6_5_keyMeasure_singleton
    (k : ex_13_6_5_Key) :
    ex_13_6_5_keyMeasure ({k} : Set ex_13_6_5_Key) =
      (1 / 3 : ℝ≥0∞) := by
  have hcard : Fintype.card ex_13_6_5_Key = 3 := by
    native_decide
  simpa [ex_13_6_5_keyMeasure, hcard] using
    (PMF.toMeasure_uniformOfFintype_apply
      (α := ex_13_6_5_Key) (s := ({k} : Set ex_13_6_5_Key))
      (measurableSet_singleton k))

theorem ex_13_6_5_keyFairBetNet_integral_zero
    (m : ℝ) (target : ex_13_6_5_Key) :
    ∫ observed,
        ex_13_6_5_keyFairBetNet m target observed ∂ex_13_6_5_keyMeasure = 0 := by
  have hcard : Fintype.card ex_13_6_5_Key = 3 := by
    native_decide
  have huniv :
      (Finset.univ : Finset ex_13_6_5_Key) =
        {ex_13_6_5_Key.a, ex_13_6_5_Key.b, ex_13_6_5_Key.c} := by
    native_decide
  rw [ex_13_6_5_keyMeasure]
  rw [PMF.integral_eq_sum]
  fin_cases target <;>
    simp [huniv, ex_13_6_5_keyFairBetNet,
      ex_13_6_5_fairBetNetGain, hcard] <;>
      ring

noncomputable def ex_13_6_5_typingMeasure :
    Measure ex_13_6_5_TypingPath :=
  Measure.infinitePi fun _ : ℕ => ex_13_6_5_keyMeasure

instance ex_13_6_5_typingMeasure_isProbabilityMeasure :
    IsProbabilityMeasure ex_13_6_5_typingMeasure := by
  dsimp [ex_13_6_5_typingMeasure]
  infer_instance

theorem ex_13_6_5_typingMeasure_iIndepFun :
    ProbabilityTheory.iIndepFun
      (fun n (ω : ex_13_6_5_TypingPath) => ω n)
      ex_13_6_5_typingMeasure := by
  simpa [ex_13_6_5_typingMeasure] using
    (ProbabilityTheory.iIndepFun_infinitePi
      (P := fun _ : ℕ => ex_13_6_5_keyMeasure)
      (X := fun _ k => k)
      (fun _ => measurable_id))

theorem ex_13_6_5_keyFairBetNet_coord_integral_zero
    (n : ℕ) (m : ℝ) (target : ex_13_6_5_Key) :
    ∫ ω,
        ex_13_6_5_keyFairBetNet m target (ω n) ∂ex_13_6_5_typingMeasure =
      0 := by
  have hmap :
      Measure.map (fun ω : ex_13_6_5_TypingPath => ω n)
          ex_13_6_5_typingMeasure =
        ex_13_6_5_keyMeasure := by
    simpa [ex_13_6_5_typingMeasure] using
      (Measure.infinitePi_map_eval
        (μ := fun _ : ℕ => ex_13_6_5_keyMeasure) n)
  calc
    ∫ ω,
        ex_13_6_5_keyFairBetNet m target (ω n) ∂ex_13_6_5_typingMeasure =
        ∫ observed,
          ex_13_6_5_keyFairBetNet m target observed ∂
            Measure.map (fun ω : ex_13_6_5_TypingPath => ω n)
              ex_13_6_5_typingMeasure := by
          exact
            (integral_map
              (μ := ex_13_6_5_typingMeasure)
              (φ := fun ω : ex_13_6_5_TypingPath => ω n)
              (f := fun observed : ex_13_6_5_Key =>
                ex_13_6_5_keyFairBetNet m target observed)
              (measurable_pi_apply n).aemeasurable
              ((ex_13_6_5_keyFairBetNet_measurable m target).aestronglyMeasurable)).symm
    _ = ∫ observed,
          ex_13_6_5_keyFairBetNet m target observed ∂ex_13_6_5_keyMeasure := by
          rw [hmap]
    _ = 0 := ex_13_6_5_keyFairBetNet_integral_zero m target

theorem ex_13_6_5_keyFairBetNet_abs_le
    (m : ℝ) (target observed : ex_13_6_5_Key) :
    |ex_13_6_5_keyFairBetNet m target observed| ≤ 2 * |m| := by
  by_cases h : observed = target
  · have hgain :
        ex_13_6_5_keyFairBetNet m target observed = 2 * m := by
      simp [ex_13_6_5_keyFairBetNet, ex_13_6_5_fairBetNetGain, h]
      ring
    rw [hgain]
    simpa using (abs_mul (2 : ℝ) m).le
  · simp [ex_13_6_5_keyFairBetNet, ex_13_6_5_fairBetNetGain, h]
    nlinarith [abs_nonneg m]

theorem ex_13_6_5_keyFairBetNet_coord_integrable
    (n : ℕ) (m : ℝ) (target : ex_13_6_5_Key) :
    Integrable
      (fun ω : ex_13_6_5_TypingPath =>
        ex_13_6_5_keyFairBetNet m target (ω n))
      ex_13_6_5_typingMeasure := by
  refine Integrable.of_bound
    (((ex_13_6_5_keyFairBetNet_measurable m target).comp
      (measurable_pi_apply n)).aestronglyMeasurable)
    (2 * |m|) ?_
  exact Filter.Eventually.of_forall fun ω => by
    simpa [Real.norm_eq_abs] using
      ex_13_6_5_keyFairBetNet_abs_le m target (ω n)

def ex_13_6_5_keyHistory (n : ℕ) :
    ex_13_6_5_TypingPath → Fin (n + 1) → ex_13_6_5_Key :=
  fun ω k => ω k.1

theorem ex_13_6_5_keyHistory_measurable (n : ℕ) :
    Measurable (ex_13_6_5_keyHistory n) := by
  rw [measurable_pi_iff]
  intro k
  simpa [ex_13_6_5_keyHistory] using measurable_pi_apply k.1

@[reducible]
def ex_13_6_5_keyHistorySigma (n : ℕ) :
    MeasurableSpace ex_13_6_5_TypingPath :=
  MeasurableSpace.comap (ex_13_6_5_keyHistory n)
    (⊤ : MeasurableSpace (Fin (n + 1) → ex_13_6_5_Key))

@[reducible]
def ex_13_6_5_typingNaturalFiltration :
    ℕ → MeasurableSpace ex_13_6_5_TypingPath :=
  fun n => ex_13_6_5_keyHistorySigma n

def ex_13_6_5_restrictHistory {n m : ℕ} (hnm : n ≤ m)
    (hist : Fin (m + 1) → ex_13_6_5_Key) :
    Fin (n + 1) → ex_13_6_5_Key :=
  fun k => hist ⟨k.1, by omega⟩

theorem ex_13_6_5_keyHistory_eq_restrict {n m : ℕ} (hnm : n ≤ m)
    (ω : ex_13_6_5_TypingPath) :
    ex_13_6_5_keyHistory n ω =
      ex_13_6_5_restrictHistory hnm (ex_13_6_5_keyHistory m ω) := by
  funext k
  rfl

theorem ex_13_6_5_typingNaturalFiltration_isFiltration :
    @def_13_6_isFiltration ex_13_6_5_TypingPath
      (⊤ : MeasurableSpace ex_13_6_5_TypingPath)
      ex_13_6_5_typingNaturalFiltration := by
  constructor
  · intro n
    exact le_top
  · intro n m hnm
    rw [MeasurableSpace.le_def]
    intro s hs
    rw [ex_13_6_5_typingNaturalFiltration,
      ex_13_6_5_keyHistorySigma] at hs ⊢
    rcases (MeasurableSpace.measurableSet_comap.mp hs) with
      ⟨u, _hu, hs_eq⟩
    apply MeasurableSpace.measurableSet_comap.mpr
    refine ⟨ex_13_6_5_restrictHistory hnm ⁻¹' u, by trivial, ?_⟩
    rw [← hs_eq]
    ext ω
    simp [ex_13_6_5_keyHistory_eq_restrict hnm]

theorem ex_13_6_5_typingNaturalFiltration_le (n : ℕ) :
    ex_13_6_5_typingNaturalFiltration n ≤
      inferInstanceAs (MeasurableSpace ex_13_6_5_TypingPath) := by
  rw [MeasurableSpace.le_def]
  intro s hs
  rw [ex_13_6_5_typingNaturalFiltration,
    ex_13_6_5_keyHistorySigma] at hs
  rcases (MeasurableSpace.measurableSet_comap.mp hs) with
    ⟨u, _hu, hs_eq⟩
  rw [← hs_eq]
  exact (ex_13_6_5_keyHistory_measurable n) u.to_countable.measurableSet

theorem ex_13_6_5_coord_eq_mem_naturalFiltration
    {idx n : ℕ} (hidx : idx ≤ n) (k : ex_13_6_5_Key) :
    @MeasurableSet ex_13_6_5_TypingPath
      (ex_13_6_5_typingNaturalFiltration n)
      {ω : ex_13_6_5_TypingPath | ω idx = k} := by
  rw [ex_13_6_5_typingNaturalFiltration,
    ex_13_6_5_keyHistorySigma,
    MeasurableSpace.measurableSet_comap]
  refine ⟨{hist : Fin (n + 1) → ex_13_6_5_Key |
      hist ⟨idx, Nat.lt_succ_of_le hidx⟩ = k}, by trivial, ?_⟩
  ext ω
  simp [ex_13_6_5_keyHistory]

theorem ex_13_6_5_typingNaturalFiltration_sigmaFinite :
    ∀ n : ℕ,
      SigmaFinite
        (ex_13_6_5_typingMeasure.trim
          (ex_13_6_5_typingNaturalFiltration_le n)) := by
  intro n
  infer_instance

def ex_13_6_5_keyHistoryBefore (n : ℕ) :
    ex_13_6_5_TypingPath → Fin n → ex_13_6_5_Key :=
  fun ω k => ω k.1

theorem ex_13_6_5_keyHistoryBefore_measurable (n : ℕ) :
    Measurable (ex_13_6_5_keyHistoryBefore n) := by
  rw [measurable_pi_iff]
  intro k
  simpa [ex_13_6_5_keyHistoryBefore] using measurable_pi_apply k.1

theorem ex_13_6_5_keyHistoryBeforeSpace_measurableSpace_eq_top
    (n : ℕ) :
    (inferInstance : MeasurableSpace (Fin n → ex_13_6_5_Key)) = ⊤ := by
  apply le_antisymm
  · exact le_top
  · rw [MeasurableSpace.le_def]
    intro s _hs
    exact s.to_countable.measurableSet

@[reducible]
def ex_13_6_5_keyHistoryBeforeSigma (n : ℕ) :
    MeasurableSpace ex_13_6_5_TypingPath :=
  MeasurableSpace.comap (ex_13_6_5_keyHistoryBefore n)
    (⊤ : MeasurableSpace (Fin n → ex_13_6_5_Key))

@[reducible]
def ex_13_6_5_typingNaturalFiltrationBefore :
    ℕ → MeasurableSpace ex_13_6_5_TypingPath :=
  fun n => ex_13_6_5_keyHistoryBeforeSigma n

def ex_13_6_5_restrictHistoryBefore {n m : ℕ} (hnm : n ≤ m)
    (hist : Fin m → ex_13_6_5_Key) :
    Fin n → ex_13_6_5_Key :=
  fun k => hist ⟨k.1, by omega⟩

theorem ex_13_6_5_keyHistoryBefore_eq_restrict {n m : ℕ} (hnm : n ≤ m)
    (ω : ex_13_6_5_TypingPath) :
    ex_13_6_5_keyHistoryBefore n ω =
      ex_13_6_5_restrictHistoryBefore hnm
        (ex_13_6_5_keyHistoryBefore m ω) := by
  funext k
  rfl

theorem ex_13_6_5_typingNaturalFiltrationBefore_isFiltration :
    @def_13_6_isFiltration ex_13_6_5_TypingPath
      (⊤ : MeasurableSpace ex_13_6_5_TypingPath)
      ex_13_6_5_typingNaturalFiltrationBefore := by
  constructor
  · intro n
    exact le_top
  · intro n m hnm
    rw [MeasurableSpace.le_def]
    intro s hs
    rw [ex_13_6_5_typingNaturalFiltrationBefore,
      ex_13_6_5_keyHistoryBeforeSigma] at hs ⊢
    rcases (MeasurableSpace.measurableSet_comap.mp hs) with
      ⟨u, _hu, hs_eq⟩
    apply MeasurableSpace.measurableSet_comap.mpr
    refine ⟨ex_13_6_5_restrictHistoryBefore hnm ⁻¹' u, by trivial, ?_⟩
    rw [← hs_eq]
    ext ω
    simp [ex_13_6_5_keyHistoryBefore_eq_restrict hnm]

theorem ex_13_6_5_typingNaturalFiltrationBefore_le (n : ℕ) :
    ex_13_6_5_typingNaturalFiltrationBefore n ≤
      inferInstanceAs (MeasurableSpace ex_13_6_5_TypingPath) := by
  rw [MeasurableSpace.le_def]
  intro s hs
  rw [ex_13_6_5_typingNaturalFiltrationBefore,
    ex_13_6_5_keyHistoryBeforeSigma] at hs
  rcases (MeasurableSpace.measurableSet_comap.mp hs) with
    ⟨u, _hu, hs_eq⟩
  rw [← hs_eq]
  exact (ex_13_6_5_keyHistoryBefore_measurable n) u.to_countable.measurableSet

theorem ex_13_6_5_typingNaturalFiltrationBefore_isFiltration_ambient :
    @def_13_6_isFiltration ex_13_6_5_TypingPath
      (inferInstanceAs (MeasurableSpace ex_13_6_5_TypingPath))
      ex_13_6_5_typingNaturalFiltrationBefore := by
  constructor
  · intro n
    exact ex_13_6_5_typingNaturalFiltrationBefore_le n
  · exact ex_13_6_5_typingNaturalFiltrationBefore_isFiltration.2

theorem ex_13_6_5_coord_eq_mem_naturalFiltrationBefore
    {idx n : ℕ} (hidx : idx < n) (k : ex_13_6_5_Key) :
    @MeasurableSet ex_13_6_5_TypingPath
      (ex_13_6_5_typingNaturalFiltrationBefore n)
      {ω : ex_13_6_5_TypingPath | ω idx = k} := by
  rw [ex_13_6_5_typingNaturalFiltrationBefore,
    ex_13_6_5_keyHistoryBeforeSigma,
    MeasurableSpace.measurableSet_comap]
  refine ⟨{hist : Fin n → ex_13_6_5_Key |
      hist ⟨idx, hidx⟩ = k}, by trivial, ?_⟩
  ext ω
  simp [ex_13_6_5_keyHistoryBefore]

theorem ex_13_6_5_typingNaturalFiltrationBefore_sigmaFinite :
    ∀ n : ℕ,
      SigmaFinite
        (ex_13_6_5_typingMeasure.trim
          (ex_13_6_5_typingNaturalFiltrationBefore_le n)) := by
  intro n
  infer_instance

theorem ex_13_6_5_typingNaturalFiltrationBefore_succ_eq_old
    (n : ℕ) :
    ex_13_6_5_typingNaturalFiltrationBefore (n + 1) =
      ex_13_6_5_typingNaturalFiltration n := by
  rfl

theorem ex_13_6_5_nextKey_indep_keyHistoryBefore (n : ℕ) :
    ProbabilityTheory.IndepFun
      (fun ω : ex_13_6_5_TypingPath => ω n)
      (ex_13_6_5_keyHistoryBefore n)
      ex_13_6_5_typingMeasure := by
  classical
  let S : Finset ℕ := {n}
  let T : Finset ℕ := Finset.range n
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro x hxS hxT
    have hx : x = n := by simpa [S] using hxS
    subst x
    exact (Nat.lt_irrefl n) (Finset.mem_range.mp hxT)
  have hraw :
      ProbabilityTheory.IndepFun
        (fun ω : ex_13_6_5_TypingPath =>
          fun i : S => (fun j (ω : ex_13_6_5_TypingPath) => ω j) i.1 ω)
        (fun ω : ex_13_6_5_TypingPath =>
          fun i : T => (fun j (ω : ex_13_6_5_TypingPath) => ω j) i.1 ω)
        ex_13_6_5_typingMeasure :=
    ex_13_6_5_typingMeasure_iIndepFun.indepFun_finset S T hST
      (fun i => measurable_pi_apply i)
  let leftEval : (S → ex_13_6_5_Key) → ex_13_6_5_Key :=
    fun hist => hist ⟨n, by simp [S]⟩
  let rightHistory : (T → ex_13_6_5_Key) → Fin n → ex_13_6_5_Key :=
    fun hist k => hist ⟨k.1, by simpa [T] using k.2⟩
  have hleft : Measurable leftEval := by
    let sIndex : S := ⟨n, by simp [S]⟩
    exact measurable_pi_apply sIndex
  have hright : Measurable rightHistory := by
    rw [measurable_pi_iff]
    intro k
    let tIndex : T := ⟨k.1, by simpa [T] using k.2⟩
    exact measurable_pi_apply tIndex
  simpa [leftEval, rightHistory, Function.comp_def,
    ex_13_6_5_keyHistoryBefore, S, T] using hraw.comp hleft hright

theorem ex_13_6_5_keyFairBetNet_condExp_before_zero
    (n : ℕ) (m : ℝ) (target : ex_13_6_5_Key) :
    ex_13_6_5_typingMeasure[
      (fun ω : ex_13_6_5_TypingPath =>
        ex_13_6_5_keyFairBetNet m target (ω n)) |
      ex_13_6_5_typingNaturalFiltrationBefore n] =ᵐ[ex_13_6_5_typingMeasure]
        (0 : ex_13_6_5_TypingPath → ℝ) := by
  let X : ex_13_6_5_TypingPath → ℝ :=
    fun ω => ex_13_6_5_keyFairBetNet m target (ω n)
  have hXm : Measurable X :=
    (ex_13_6_5_keyFairBetNet_measurable m target).comp
      (measurable_pi_apply n)
  have hX_sub :
      MeasurableSpace.comap X (borel ℝ) ≤
        inferInstanceAs (MeasurableSpace ex_13_6_5_TypingPath) :=
    hXm.comap_le
  have hBefore_sub :
      ex_13_6_5_typingNaturalFiltrationBefore n ≤
        inferInstanceAs (MeasurableSpace ex_13_6_5_TypingPath) :=
    ex_13_6_5_typingNaturalFiltrationBefore_le n
  haveI :
      SigmaFinite
        (ex_13_6_5_typingMeasure.trim hBefore_sub) :=
    ex_13_6_5_typingNaturalFiltrationBefore_sigmaFinite n
  have hIndepFun :
      ProbabilityTheory.IndepFun X
        (ex_13_6_5_keyHistoryBefore n)
        ex_13_6_5_typingMeasure := by
    simpa [X, Function.comp_def] using
      (ex_13_6_5_nextKey_indep_keyHistoryBefore n).comp
        (ex_13_6_5_keyFairBetNet_measurable m target) measurable_id
  have hIndep :
      ProbabilityTheory.Indep
        (MeasurableSpace.comap X (borel ℝ))
        (ex_13_6_5_typingNaturalFiltrationBefore n)
        ex_13_6_5_typingMeasure := by
    have hIndepRaw :=
      (ProbabilityTheory.IndepFun_iff_Indep X
        (ex_13_6_5_keyHistoryBefore n)
        ex_13_6_5_typingMeasure).1 hIndepFun
    simpa [ProbabilityTheory.IndepFun,
      ex_13_6_5_typingNaturalFiltrationBefore,
      ex_13_6_5_keyHistoryBeforeSigma,
      ex_13_6_5_keyHistoryBeforeSpace_measurableSpace_eq_top n] using hIndepRaw
  have hcond :
      ex_13_6_5_typingMeasure[X |
        ex_13_6_5_typingNaturalFiltrationBefore n] =ᵐ[ex_13_6_5_typingMeasure]
          fun _ : ex_13_6_5_TypingPath => ex_13_6_5_typingMeasure[X] :=
    condExp_indep_eq hX_sub hBefore_sub
      ((comap_measurable X).stronglyMeasurable) hIndep
  have hmean : ex_13_6_5_typingMeasure[X] = 0 := by
    simpa [X] using
      ex_13_6_5_keyFairBetNet_coord_integral_zero n m target
  exact hcond.trans (Filter.Eventually.of_forall fun ω => by simp [hmean])

theorem ex_13_6_5_keyFairBetNet_indicator_condExp_before_zero
    (n : ℕ) (m : ℝ) (target : ex_13_6_5_Key)
    {A : Set ex_13_6_5_TypingPath}
    (hA :
      @MeasurableSet ex_13_6_5_TypingPath
        (ex_13_6_5_typingNaturalFiltrationBefore n) A) :
    ex_13_6_5_typingMeasure[
      A.indicator
        (fun ω : ex_13_6_5_TypingPath =>
          ex_13_6_5_keyFairBetNet m target (ω n)) |
      ex_13_6_5_typingNaturalFiltrationBefore n] =ᵐ[ex_13_6_5_typingMeasure]
        (0 : ex_13_6_5_TypingPath → ℝ) := by
  have hzero :=
    ex_13_6_5_keyFairBetNet_condExp_before_zero n m target
  have hindicator :
      ex_13_6_5_typingMeasure[
        A.indicator
          (fun ω : ex_13_6_5_TypingPath =>
            ex_13_6_5_keyFairBetNet m target (ω n)) |
        ex_13_6_5_typingNaturalFiltrationBefore n] =ᵐ[ex_13_6_5_typingMeasure]
          A.indicator
            (ex_13_6_5_typingMeasure[
              (fun ω : ex_13_6_5_TypingPath =>
                ex_13_6_5_keyFairBetNet m target (ω n)) |
              ex_13_6_5_typingNaturalFiltrationBefore n]) :=
    condExp_indicator
      (ex_13_6_5_keyFairBetNet_coord_integrable n m target) hA
  refine hindicator.trans ?_
  filter_upwards [hzero] with ω hω
  by_cases hmem : ω ∈ A
  · simp [Set.indicator_of_mem hmem, hω]
  · simp [Set.indicator_of_notMem hmem]
