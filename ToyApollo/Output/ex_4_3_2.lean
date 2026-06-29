import Mathlib
import ToyApollo.Output.def_4_3_limsup_liminf

open Filter

/-- The interleaved sequence from Example 4.3.2. -/
noncomputable def ex_4_3_2_seq (n : ℕ) : ℝ :=
  if Even n then (-1 : ℝ) - 1 / ((n : ℝ) + 1) else 1 + 1 / ((n : ℝ) + 1)

theorem ex_4_3_2_seq_even (n : ℕ) :
    ex_4_3_2_seq (2 * n) = (-1 : ℝ) - 1 / (((2 * n : ℕ) : ℝ) + 1) := by
  have h : Even (2 * n) := by
    exact Even.mul_right ⟨1, by simp⟩ n
  simp [ex_4_3_2_seq, h]

theorem ex_4_3_2_seq_odd (n : ℕ) :
    ex_4_3_2_seq (2 * n + 1) = 1 + 1 / (((2 * n + 1 : ℕ) : ℝ) + 1) := by
  have hEven : Even (2 * n) := by
    exact Even.mul_right ⟨1, by simp⟩ n
  have hOdd : ¬ Even (2 * n + 1) := by
    intro h1
    exact (Nat.even_add_one.mp h1) hEven
  simp [ex_4_3_2_seq, hOdd]

theorem ex_4_3_2_even_lt_neg_one (n : ℕ) :
    ex_4_3_2_seq (2 * n) < (-1 : ℝ) := by
  rw [ex_4_3_2_seq_even]
  have hpos : (0 : ℝ) < 1 / (((2 * n : ℕ) : ℝ) + 1) := by
    positivity
  linarith

theorem ex_4_3_2_one_lt_odd (n : ℕ) :
    (1 : ℝ) < ex_4_3_2_seq (2 * n + 1) := by
  rw [ex_4_3_2_seq_odd]
  have hpos : (0 : ℝ) < 1 / (((2 * n + 1 : ℕ) : ℝ) + 1) := by
    positivity
  linarith

theorem ex_4_3_2_seq_le_two (n : ℕ) :
    ex_4_3_2_seq n ≤ (2 : ℝ) := by
  by_cases hEven : Even n
  · rw [ex_4_3_2_seq, if_pos hEven]
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
      positivity
    linarith
  · rw [ex_4_3_2_seq, if_neg hEven]
    have hfrac : 1 / ((n : ℝ) + 1) ≤ 1 := by
      have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
      have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      have hpos : (0 : ℝ) < (1 : ℝ) := by norm_num
      have hrecip : 1 / ((n : ℝ) + 1) ≤ 1 / (1 : ℝ) := by
        exact one_div_le_one_div_of_le hpos hden
      simpa using hrecip
    linarith

theorem ex_4_3_2_neg_two_le_seq (n : ℕ) :
    (-2 : ℝ) ≤ ex_4_3_2_seq n := by
  by_cases hEven : Even n
  · rw [ex_4_3_2_seq, if_pos hEven]
    have hfrac : 1 / ((n : ℝ) + 1) ≤ 1 := by
      have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
      have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      have hpos : (0 : ℝ) < (1 : ℝ) := by norm_num
      have hrecip : 1 / ((n : ℝ) + 1) ≤ 1 / (1 : ℝ) := by
        exact one_div_le_one_div_of_le hpos hden
      simpa using hrecip
    linarith
  · rw [ex_4_3_2_seq, if_neg hEven]
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
      positivity
    linarith

theorem ex_4_3_2_limsup : Filter.limsup ex_4_3_2_seq atTop = (1 : ℝ) := by
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) atTop ex_4_3_2_seq := by
    exact Filter.isBoundedUnder_of_eventually_le (Eventually.of_forall ex_4_3_2_seq_le_two)
  have hcobdd : Filter.IsCoboundedUnder (· ≤ ·) atTop ex_4_3_2_seq := by
    exact Filter.isCoboundedUnder_le_of_le atTop ex_4_3_2_neg_two_le_seq
  have h_lower : (1 : ℝ) ≤ Filter.limsup ex_4_3_2_seq atTop := by
    have hfreq : ∃ᶠ n : ℕ in atTop, (1 : ℝ) ≤ ex_4_3_2_seq n := by
      refine Filter.frequently_atTop.2 ?_
      intro N
      refine ⟨2 * N + 1, by omega, ?_⟩
      have hodd : (1 : ℝ) < ex_4_3_2_seq (2 * N + 1) := ex_4_3_2_one_lt_odd N
      linarith
    exact Filter.le_limsup_of_frequently_le hfreq hbdd
  have h_upper_eps : ∀ ε : ℝ, 0 < ε → Filter.limsup ex_4_3_2_seq atTop ≤ 1 + ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    have h_event : ∀ᶠ n : ℕ in atTop, ex_4_3_2_seq n ≤ 1 + ε := by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨N, ?_⟩
      intro n hn
      by_cases hEven : Even n
      · rw [ex_4_3_2_seq, if_pos hEven]
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      · rw [ex_4_3_2_seq, if_neg hEven]
        have hden : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by
          exact_mod_cast Nat.succ_le_succ hn
        have hfrac : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
          exact one_div_le_one_div_of_le (by positivity) hden
        linarith
    exact Filter.limsup_le_of_le hcobdd h_event
  have h_upper : Filter.limsup ex_4_3_2_seq atTop ≤ (1 : ℝ) := by
    by_contra h
    have hlt : (1 : ℝ) < Filter.limsup ex_4_3_2_seq atTop := lt_of_not_ge h
    let ε : ℝ := (Filter.limsup ex_4_3_2_seq atTop - 1) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    have hbound := h_upper_eps ε hε
    dsimp [ε] at hbound
    linarith
  exact le_antisymm h_upper h_lower

theorem ex_4_3_2_liminf : Filter.liminf ex_4_3_2_seq atTop = (-1 : ℝ) := by
  have hbdd : Filter.IsBoundedUnder (· ≥ ·) atTop ex_4_3_2_seq := by
    exact Filter.isBoundedUnder_of_eventually_ge (Eventually.of_forall ex_4_3_2_neg_two_le_seq)
  have hcobdd : Filter.IsCoboundedUnder (· ≥ ·) atTop ex_4_3_2_seq := by
    exact Filter.isCoboundedUnder_ge_of_le atTop ex_4_3_2_seq_le_two
  have h_upper : Filter.liminf ex_4_3_2_seq atTop ≤ (-1 : ℝ) := by
    have hfreq : ∃ᶠ n : ℕ in atTop, ex_4_3_2_seq n ≤ (-1 : ℝ) := by
      refine Filter.frequently_atTop.2 ?_
      intro N
      refine ⟨2 * N, by omega, ?_⟩
      have heven : ex_4_3_2_seq (2 * N) < (-1 : ℝ) := ex_4_3_2_even_lt_neg_one N
      linarith
    exact Filter.liminf_le_of_frequently_le hfreq hbdd
  have h_lower_eps : ∀ ε : ℝ, 0 < ε → (-1 : ℝ) - ε ≤ Filter.liminf ex_4_3_2_seq atTop := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    have h_event : ∀ᶠ n : ℕ in atTop, (-1 : ℝ) - ε ≤ ex_4_3_2_seq n := by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨N, ?_⟩
      intro n hn
      by_cases hEven : Even n
      · rw [ex_4_3_2_seq, if_pos hEven]
        have hden : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by
          exact_mod_cast Nat.succ_le_succ hn
        have hfrac : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
          exact one_div_le_one_div_of_le (by positivity) hden
        linarith
      · rw [ex_4_3_2_seq, if_neg hEven]
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    exact Filter.le_liminf_of_le hcobdd h_event
  have h_lower : (-1 : ℝ) ≤ Filter.liminf ex_4_3_2_seq atTop := by
    by_contra h
    have hlt : Filter.liminf ex_4_3_2_seq atTop < (-1 : ℝ) := lt_of_not_ge h
    let ε : ℝ := ((-1 : ℝ) - Filter.liminf ex_4_3_2_seq atTop) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    have hbound := h_lower_eps ε hε
    dsimp [ε] at hbound
    linarith
  exact le_antisymm h_upper h_lower

/--
Example 4.3.2: the interleaved sequence does not converge, but its limsup is `1` and its liminf
is `-1`.
-/
theorem ex_4_3_2 :
    Filter.limsup ex_4_3_2_seq atTop = (1 : ℝ) ∧
      Filter.liminf ex_4_3_2_seq atTop = (-1 : ℝ) := by
  exact ⟨ex_4_3_2_limsup, ex_4_3_2_liminf⟩
