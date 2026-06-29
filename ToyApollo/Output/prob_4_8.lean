/-
TASK ID: prob_4_8
TYPE: Problem
SOURCE PLAN: 12_chap4_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open Filter Real

noncomputable def seq1 : ℕ → ℝ := fun n => sin ((n : ℝ) * π / 3)
noncomputable def seq2 : ℕ → ℝ :=
  fun k => if k % 2 = 1 then Real.log (k : ℝ) else 1 / (k : ℝ)

lemma prob_4_8a_limsup :
    limsup (fun n => (seq1 n : EReal)) atTop = (sin (π / 3) : EReal) := by
  have h_periodic : ∀ n, seq1 n ≤ Real.sin (Real.pi / 3) := by
    unfold seq1
    intro n
    rw [← Real.cos_sub_pi_div_two]
    rw [← Real.cos_pi_div_two_sub]
    ring_nf
    norm_num
    rcases Nat.mod_lt n zero_lt_three with hn
    rw [← Nat.mod_add_div n 3]
    norm_num [mul_add, mul_assoc, mul_comm Real.pi _, mul_div]
    ring_nf
    norm_num [mul_div]
    interval_cases n % 3 <;> norm_num [Real.cos_add, Real.sin_add, mul_div]
    · positivity
    · exact Real.cos_le_one _
    · norm_num [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring]
      exact Real.cos_le_one _
  refine' le_antisymm (csInf_le _ _) (le_csInf _ _)
  · refine' ⟨⊥, fun x hx => _⟩
    aesop
  · aesop
  · exact ⟨_, Filter.eventually_map.mpr <|
      Filter.eventually_atTop.mpr
        ⟨0, fun n hn =>
          show (seq1 n : EReal) ≤ ↑(Real.sin (Real.pi / 3)) from
            mod_cast h_periodic n⟩⟩
  · norm_num [seq1]
    intro b x hx
    specialize hx (6 * x + 1) (by linarith)
    norm_num [add_mul, mul_assoc, mul_div_assoc] at hx
    convert hx using 1
    rw [show (6 * (x * Real.pi) + Real.pi) / 3 =
        Real.pi / 3 + 2 * x * Real.pi by ring]
    norm_num [mul_assoc, mul_left_comm]

lemma prob_4_8a_liminf :
    liminf (fun n => (seq1 n : EReal)) atTop = (-sin (π / 3) : EReal) := by
  refine' le_antisymm (_ : liminf _ _ ≤ _) _
  · refine' Filter.liminf_le_of_frequently_le' _
    refine' Filter.frequently_atTop.2 fun n => _
    refine' ⟨6 * n + 4, by linarith, _⟩
    norm_num [seq1]
    rw [← Real.sin_pi_div_three, ← Real.sin_pi_sub]
    ring_nf
    norm_num [mul_assoc, mul_comm Real.pi _, mul_div]
  · rw [Filter.liminf_eq_iSup_iInf_of_nat']
    refine' le_iSup_of_le (4 : ℕ) _
    refine' le_ciInf fun i => _
    unfold seq1
    norm_num
    ring_nf
    norm_cast
    norm_num [mul_div]
    rw [show Real.pi * 4 / 3 = Real.pi + Real.pi / 3 by ring, Real.sin_add]
    norm_num [Real.sin_add, Real.cos_add]
    ring_nf
    norm_num
    rw [← Nat.mod_add_div i 6]
    norm_num
    ring_nf
    norm_num [mul_assoc, mul_comm Real.pi _, mul_div]
    have := Nat.mod_lt i (by decide : 6 > 0)
    interval_cases i % 6 <;> norm_num <;> ring_nf <;> norm_num [mul_div]
    · rw [show Real.pi * 2 / 3 = Real.pi - Real.pi / 3 by ring]
      norm_num
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three]
    · positivity
    · rw [show Real.pi * 4 / 3 = Real.pi + Real.pi / 3 by ring,
        Real.cos_add, Real.sin_add]
      norm_num
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three]
    · norm_num [show Real.pi * 5 / 3 = 2 * Real.pi - Real.pi / 3 by ring]
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three]

lemma prob_4_8b_limsup :
    limsup (fun k => (seq2 k : EReal)) atTop = ⊤ := by
  apply top_le_iff.mp
  refine le_limsup_of_le (u := fun k => (seq2 k : EReal)) (by isBoundedDefault) ?_
  · intro b hb
    by_cases hb_top : b = ⊤
    · subst hb_top
      exact le_rfl
    · have h_upper_toReal : ∀ᶠ n in atTop, (seq2 n : EReal) ≤ (b.toReal : EReal) := by
        exact hb.mono fun n hn => le_trans hn (EReal.le_coe_toReal hb_top)
      rcases Filter.eventually_atTop.mp h_upper_toReal with ⟨N, hN⟩
      let m : ℕ := max N ⌈Real.exp (b.toReal)⌉₊
      let k : ℕ := 2 * m + 1
      have hk_ge_N : N ≤ k := by
        dsimp [k, m]
        omega
      have hk_odd : k % 2 = 1 := by
        dsimp [k]
        omega
      have hk_pos : 0 < (k : ℝ) := by positivity
      have hk_gt_exp : Real.exp (b.toReal) < (k : ℝ) := by
        have hceil_le :
            Real.exp (b.toReal) ≤ ((⌈Real.exp (b.toReal)⌉₊ : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_ceil (Real.exp (b.toReal))
        have hceil :
            Real.exp (b.toReal) < ((⌈Real.exp (b.toReal)⌉₊ : ℕ) : ℝ) + 1 := by
          linarith
        have hstep_nat : (⌈Real.exp (b.toReal)⌉₊ : ℕ) + 1 ≤ k := by
          dsimp [k, m]
          omega
        have hstep : ((⌈Real.exp (b.toReal)⌉₊ : ℕ) : ℝ) + 1 ≤ (k : ℝ) := by
          exact_mod_cast hstep_nat
        exact lt_of_lt_of_le hceil hstep
      have hlogk : b.toReal < Real.log (k : ℝ) := by
        rw [Real.lt_log_iff_exp_lt hk_pos]
        exact hk_gt_exp
      have hk_upper : (Real.log (k : ℝ) : EReal) ≤ (b.toReal : EReal) := by
        have hk_eventual := hN k hk_ge_N
        simpa [seq2, hk_odd] using hk_eventual
      exfalso
      exact (not_lt_of_ge hk_upper) (by exact_mod_cast hlogk)

lemma prob_4_8b_liminf :
    liminf (fun k => (seq2 k : EReal)) atTop = (0 : EReal) := by
  have h_seq2_eps : ∀ ε > 0, ∃ N, ∀ k ≥ N, k % 2 = 0 → seq2 k < ε := by
    unfold seq2
    exact fun ε hε =>
      ⟨⌈ε⁻¹⌉₊ + 1, fun k hk₁ hk₂ => by
        rw [if_neg (by linarith)]
        simpa using inv_lt_of_inv_lt₀ hε <| Nat.lt_of_ceil_lt hk₁⟩
  refine' csSup_eq_of_forall_le_of_forall_lt_exists_gt _ _ _ <;> norm_num
  · use 0
    use 2
    intro k hk
    unfold seq2
    split_ifs <;> norm_num
    positivity
  · contrapose! h_seq2_eps
    obtain ⟨a, x, hx₁, hx₂⟩ := h_seq2_eps
    cases' a with a a
    · aesop
    · exact ⟨a, by exact_mod_cast hx₂, fun N =>
        ⟨2 * (N + x + 1), by linarith, by norm_num,
          by exact_mod_cast hx₁ _ (by linarith)⟩⟩
    · exact absurd (hx₁ (2 * x + 2) (by linarith)) (by norm_num [seq2])
  · exact fun w hw => ⟨0, ⟨0, fun n hn => by
      unfold seq2
      split_ifs <;> positivity⟩, hw⟩

theorem prob_4_8 :
    limsup (fun n => (seq1 n : EReal)) atTop = (sin (π / 3) : EReal) ∧
    liminf (fun n => (seq1 n : EReal)) atTop = (-sin (π / 3) : EReal) ∧
    limsup (fun k => (seq2 k : EReal)) atTop = ⊤ ∧
    liminf (fun k => (seq2 k : EReal)) atTop = (0 : EReal) :=
  ⟨prob_4_8a_limsup, prob_4_8a_liminf, prob_4_8b_limsup, prob_4_8b_liminf⟩
