import ToyApollo.Output.prob_8_6_component_support

open Real Nat Finset
open MeasureTheory ProbabilityTheory Set
open TVCore

noncomputable section

lemma n_mul_div_sq (lam : ℝ) (n : ℝ) (hn : n ≠ 0) :
    n * (lam / n) ^ 2 = lam ^ 2 / n := by
  field_simp

-- ============================================================================
-- Main theorem
-- ============================================================================

/--
**Problem 8.6 (Poisson Approximation of Binomial Distribution).**

Note: We add `hn : 0 < n` (needed since λ²/0 = 0 in Lean) and `hln : lam ≤ ↑n`
(so λ/n ∈ [0,1]).
-/
theorem prob_8_6_part_d_helper
    (n : ℕ) (lam : ℝ) (hlam : lam ≥ 0) (hn : 0 < n) (hln : lam ≤ ↑n) :
    d_TV (Binom n (lam / ↑n)) (Poi lam) ≤ lam ^ 2 / ↑n := by
  have hn' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hn'' : (n : ℝ) ≠ 0 := ne_of_gt hn'
  have hp0 : 0 ≤ lam / ↑n := div_nonneg hlam.le hn'.le
  have hp1 : lam / ↑n ≤ 1 := div_le_one_of_le₀ hln hn'.le
  have hlam_eq : ↑n * (lam / ↑n) = lam := mul_div_cancel₀ lam hn''
  -- Rewrite as n-fold convolutions
  rw [binom_eq_conv_ber n (lam / ↑n)]
  rw [show Poi lam = pmfConvN (Poi (lam / ↑n)) n from by
    conv_lhs => rw [← hlam_eq]; exact poi_eq_conv_poi n (lam / ↑n) hp0]
  -- Apply the n-fold TV bound and Ber-Poi TV bound
  have h1 := d_TV_convN_bound (Ber (lam / ↑n)) (Poi (lam / ↑n))
    (ber_nonneg _ hp0 hp1) (ber_sum_one _)
    (poi_nonneg _ hp0) (poi_sum_one _ hp0) n
  have h2 := ber_poi_tv_le_sq _ hp0
  rw [← n_mul_div_sq lam ↑n hn'']
  exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hn'.le)

/-- Textbook-facing part (d): the positivity side conditions are packed into the subtype
arguments, so the exported interface is the substitution step itself. -/
theorem prob_8_6_part_d (n : ℕ+) (lam : Set.Icc (0 : ℝ) (n : ℝ)) :
    d_TV (Binom (n : ℕ) (lam.1 / (n : ℝ))) (Poi lam.1) ≤ lam.1 ^ 2 / (n : ℝ) := by
  exact prob_8_6_part_d_helper (n := (n : ℕ)) (lam := lam.1) lam.2.1 n.pos lam.2.2

/-- Exported wrapper for Problem 8.6: this is part (d), with the earlier parts also exported
as their own reusable declarations. -/
theorem prob_8_6_support_result (n : ℕ+) (lam : Set.Icc (0 : ℝ) (n : ℝ)) :
    d_TV (Binom (n : ℕ) (lam.1 / (n : ℝ))) (Poi lam.1) ≤ lam.1 ^ 2 / (n : ℝ) :=
  prob_8_6_part_d n lam

end
