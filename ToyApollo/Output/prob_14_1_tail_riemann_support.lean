/-
TASK ID: prob_14_1_tail_riemann_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.prob_14_1_grid_cdf_support

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators ENNReal Asymptotics

noncomputable section

theorem prob_14_1_polyaWhiteMassFormula_gamma_ratio_product_isEquivalent_of_total_count_sequence
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b)
    (nseq kseq : ℕ → ℕ)
    (hk_le : ∀ᶠ j in atTop, kseq j ≤ nseq j)
    (hn_top : Tendsto nseq atTop atTop)
    (hk_top : Tendsto kseq atTop atTop)
    (hrest_top : Tendsto (fun j : ℕ => nseq j - kseq j) atTop atTop) :
    (fun j : ℕ =>
        prob_14_1_polyaWhiteMassFormula w b (nseq j) (kseq j)) ~[atTop]
      (fun j : ℕ =>
        (((1 / ProbabilityTheory.beta w b) *
          ((nseq j : ℝ) ^ (1 - (b + w)))) *
          ((kseq j : ℝ) ^ (w - 1))) *
          (((nseq j - kseq j : ℕ) : ℝ) ^ (b - 1))) := by
  have hEq :
      (fun j : ℕ =>
        prob_14_1_polyaWhiteMassFormula w b (nseq j) (kseq j)) =ᶠ[atTop]
      (fun j : ℕ =>
        (((1 / ProbabilityTheory.beta w b) *
          (Real.Gamma ((nseq j : ℝ) + 1) /
            Real.Gamma (b + w + nseq j))) *
          (Real.Gamma (w + kseq j) /
            Real.Gamma ((kseq j : ℝ) + 1))) *
          (Real.Gamma (b + ((nseq j - kseq j : ℕ) : ℝ)) /
            Real.Gamma (((nseq j - kseq j : ℕ) : ℝ) + 1))) := by
    filter_upwards [hk_le] with j hj
    rw [prob_14_1_polyaWhiteMassFormula_eq_beta_gamma_ratio_split hw hb hj]
  have hconst :
      (fun _ : ℕ => 1 / ProbabilityTheory.beta w b) ~[atTop]
        (fun _ : ℕ => 1 / ProbabilityTheory.beta w b) :=
    Filter.EventuallyEq.rfl.isEquivalent
  have hA :
      (fun j : ℕ =>
        Real.Gamma ((nseq j : ℝ) + 1) / Real.Gamma (b + w + nseq j)) ~[atTop]
        (fun j : ℕ => (nseq j : ℝ) ^ (1 - (b + w))) := by
    simpa [Function.comp_def, add_comm, add_left_comm, add_assoc] using
      (prob_14_1_shifted_gamma_ratio_isEquivalent
        (a := (1 : ℝ)) (c := b + w) zero_lt_one
        (add_pos hb hw)).comp_tendsto hn_top
  have hB :
      (fun j : ℕ =>
        Real.Gamma (w + kseq j) / Real.Gamma ((kseq j : ℝ) + 1)) ~[atTop]
        (fun j : ℕ => (kseq j : ℝ) ^ (w - 1)) := by
    simpa [Function.comp_def, add_comm, add_left_comm, add_assoc] using
      (prob_14_1_shifted_gamma_ratio_isEquivalent
        (a := w) (c := (1 : ℝ)) hw zero_lt_one).comp_tendsto hk_top
  have hC :
      (fun j : ℕ =>
        Real.Gamma (b + ((nseq j - kseq j : ℕ) : ℝ)) /
          Real.Gamma (((nseq j - kseq j : ℕ) : ℝ) + 1)) ~[atTop]
        (fun j : ℕ => ((nseq j - kseq j : ℕ) : ℝ) ^ (b - 1)) := by
    simpa [Function.comp_def, add_comm, add_left_comm, add_assoc] using
      (prob_14_1_shifted_gamma_ratio_isEquivalent
        (a := b) (c := (1 : ℝ)) hb zero_lt_one).comp_tendsto hrest_top
  exact hEq.isEquivalent.trans (((hconst.mul hA).mul hB).mul hC)

theorem prob_14_1_scaled_gamma_kernel_tendsto_of_total_count_sequence
    {w b x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (nseq kseq : ℕ → ℕ)
    (hk_ratio :
      Tendsto (fun j : ℕ => (kseq j : ℝ) / (nseq j : ℝ)) atTop (𝓝 x))
    (hrest_ratio :
      Tendsto
        (fun j : ℕ => ((nseq j - kseq j : ℕ) : ℝ) / (nseq j : ℝ))
        atTop (𝓝 (1 - x)))
    (hn_pos : ∀ᶠ j in atTop, 0 < nseq j)
    (hk_pos : ∀ᶠ j in atTop, 0 < kseq j)
    (hrest_pos : ∀ᶠ j in atTop, 0 < nseq j - kseq j) :
    Tendsto
      (fun j : ℕ =>
        (nseq j : ℝ) *
          ((((1 / ProbabilityTheory.beta w b) *
            ((nseq j : ℝ) ^ (1 - (b + w)))) *
            ((kseq j : ℝ) ^ (w - 1))) *
            (((nseq j - kseq j : ℕ) : ℝ) ^ (b - 1))))
      atTop
      (𝓝 ((1 / ProbabilityTheory.beta w b) *
        x ^ (w - 1) * (1 - x) ^ (b - 1))) := by
  have hxrest : 0 < 1 - x := sub_pos.mpr hx1
  have hratio_kernel :
      Tendsto
        (fun j : ℕ =>
          (1 / ProbabilityTheory.beta w b) *
            ((kseq j : ℝ) / (nseq j : ℝ)) ^ (w - 1) *
            (((nseq j - kseq j : ℕ) : ℝ) / (nseq j : ℝ)) ^ (b - 1))
        atTop
        (𝓝 ((1 / ProbabilityTheory.beta w b) *
          x ^ (w - 1) * (1 - x) ^ (b - 1))) := by
    have hkpow :
        Tendsto
          (fun j : ℕ => ((kseq j : ℝ) / (nseq j : ℝ)) ^ (w - 1))
          atTop (𝓝 (x ^ (w - 1))) :=
      hk_ratio.rpow tendsto_const_nhds (Or.inl hx0.ne')
    have hrpow :
        Tendsto
          (fun j : ℕ =>
            (((nseq j - kseq j : ℕ) : ℝ) / (nseq j : ℝ)) ^ (b - 1))
          atTop (𝓝 ((1 - x) ^ (b - 1))) :=
      hrest_ratio.rpow tendsto_const_nhds (Or.inl hxrest.ne')
    simpa [mul_assoc] using
      ((tendsto_const_nhds.mul hkpow).mul hrpow)
  refine Tendsto.congr' ?_ hratio_kernel
  filter_upwards [hn_pos, hk_pos, hrest_pos] with j hn hk hnrest
  have hn_pos_real : 0 < (nseq j : ℝ) := by exact_mod_cast hn
  have hk_pos_real : 0 < (kseq j : ℝ) := by exact_mod_cast hk
  have hrest_pos_real : 0 < ((nseq j - kseq j : ℕ) : ℝ) := by
    exact_mod_cast hnrest
  exact (prob_14_1_scaled_gamma_kernel_eq_ratio_kernel
    (C := 1 / ProbabilityTheory.beta w b) (w := w) (b := b)
    (n := (nseq j : ℝ)) (k := (kseq j : ℝ))
    (r := ((nseq j - kseq j : ℕ) : ℝ))
    hn_pos_real hk_pos_real hrest_pos_real).symm

theorem prob_14_1_scaled_polya_mass_tendsto_betaDensity_of_total_count_sequence
    {w b x : ℝ} (hw : 0 < w) (hb : 0 < b)
    (hx0 : 0 < x) (hx1 : x < 1)
    (nseq kseq : ℕ → ℕ)
    (hk_le : ∀ᶠ j in atTop, kseq j ≤ nseq j)
    (hn_top : Tendsto nseq atTop atTop)
    (hk_top : Tendsto kseq atTop atTop)
    (hrest_top : Tendsto (fun j : ℕ => nseq j - kseq j) atTop atTop)
    (hk_ratio :
      Tendsto (fun j : ℕ => (kseq j : ℝ) / (nseq j : ℝ)) atTop (𝓝 x))
    (hrest_ratio :
      Tendsto
        (fun j : ℕ => ((nseq j - kseq j : ℕ) : ℝ) / (nseq j : ℝ))
        atTop (𝓝 (1 - x)))
    (hn_pos : ∀ᶠ j in atTop, 0 < nseq j)
    (hk_pos : ∀ᶠ j in atTop, 0 < kseq j)
    (hrest_pos : ∀ᶠ j in atTop, 0 < nseq j - kseq j) :
    Tendsto
      (fun j : ℕ =>
        (nseq j : ℝ) * prob_14_1_polyaWhiteMassFormula w b (nseq j) (kseq j))
      atTop
      (𝓝 (prob_14_1_betaDensity w b (1 / ProbabilityTheory.beta w b) x)) := by
  have hmain :=
    prob_14_1_polyaWhiteMassFormula_gamma_ratio_product_isEquivalent_of_total_count_sequence
      hw hb nseq kseq hk_le hn_top hk_top hrest_top
  have hn_equiv :
      (fun j : ℕ => (nseq j : ℝ)) ~[atTop] (fun j : ℕ => (nseq j : ℝ)) :=
    Filter.EventuallyEq.rfl.isEquivalent
  have hscaled :
      (fun j : ℕ =>
        (nseq j : ℝ) * prob_14_1_polyaWhiteMassFormula w b (nseq j) (kseq j)) ~[atTop]
      (fun j : ℕ =>
        (nseq j : ℝ) *
          ((((1 / ProbabilityTheory.beta w b) *
            ((nseq j : ℝ) ^ (1 - (b + w)))) *
            ((kseq j : ℝ) ^ (w - 1))) *
            (((nseq j - kseq j : ℕ) : ℝ) ^ (b - 1)))) :=
    hn_equiv.mul hmain
  have hkernel :=
    prob_14_1_scaled_gamma_kernel_tendsto_of_total_count_sequence
      (w := w) (b := b) hx0 hx1 nseq kseq
      hk_ratio hrest_ratio hn_pos hk_pos hrest_pos
  have hdensity :
      (1 / ProbabilityTheory.beta w b) *
        x ^ (w - 1) * (1 - x) ^ (b - 1) =
      prob_14_1_betaDensity w b (1 / ProbabilityTheory.beta w b) x := by
    have hxmem : x ∈ Set.Ioo (0 : ℝ) 1 := by
      exact ⟨hx0, hx1⟩
    simp [prob_14_1_betaDensity, hxmem, mul_assoc]
  rw [← hdensity]
  exact (hscaled.tendsto_nhds_iff).2 hkernel

theorem prob_14_1_compact_interior_uniform_scaled_polya_mass_tendsto_betaDensity
    {w b a c : ℝ} (hw : 0 < w) (hb : 0 < b)
    (ha : 0 < a) (_hac : a ≤ c) (hc : c < 1) :
    ∀ eps > 0, ∀ᶠ n : ℕ in atTop,
      ∀ k : ℕ, k ≤ n →
        a ≤ (k : ℝ) / (n : ℝ) →
        (k : ℝ) / (n : ℝ) ≤ c →
        |(n : ℝ) * prob_14_1_polyaWhiteMassFormula w b n k -
          prob_14_1_betaDensity w b (1 / ProbabilityTheory.beta w b)
            ((k : ℝ) / (n : ℝ))| < eps := by
  intro eps heps
  by_contra hbad
  have hfreq :
      ∃ᶠ n : ℕ in atTop,
        ∃ k : ℕ,
          k ≤ n ∧
          a ≤ (k : ℝ) / (n : ℝ) ∧
          (k : ℝ) / (n : ℝ) ≤ c ∧
          eps ≤
            |(n : ℝ) * prob_14_1_polyaWhiteMassFormula w b n k -
              prob_14_1_betaDensity w b (1 / ProbabilityTheory.beta w b)
                ((k : ℝ) / (n : ℝ))| := by
    have hfreq0 :
        ∃ᶠ n : ℕ in atTop,
          ¬ ∀ k : ℕ, k ≤ n →
            a ≤ (k : ℝ) / (n : ℝ) →
            (k : ℝ) / (n : ℝ) ≤ c →
            |(n : ℝ) * prob_14_1_polyaWhiteMassFormula w b n k -
              prob_14_1_betaDensity w b (1 / ProbabilityTheory.beta w b)
                ((k : ℝ) / (n : ℝ))| < eps :=
      (Filter.not_eventually).1 hbad
    simpa [not_forall, Classical.not_imp, not_lt] using hfreq0
  rcases Filter.extraction_of_frequently_atTop hfreq with ⟨φ, hφmono, hφbad⟩
  choose k hk using hφbad
  have hφ_pos : ∀ j : ℕ, 0 < φ j := by
    intro j
    by_contra hnot
    have hzero : φ j = 0 := Nat.eq_zero_of_not_pos hnot
    have hratio_zero : (k j : ℝ) / (φ j : ℝ) = 0 := by
      simp [hzero]
    have ha_le_zero : a ≤ 0 := by
      simpa [hratio_zero] using (hk j).2.1
    linarith
  let r : ℕ → ℝ := fun j => (k j : ℝ) / (φ j : ℝ)
  have hr_mem : ∀ j, r j ∈ Set.Icc a c := by
    intro j
    exact ⟨(hk j).2.1, (hk j).2.2.1⟩
  rcases isCompact_Icc.tendsto_subseq hr_mem with
    ⟨x, hxIcc, ψ, hψmono, hψtend⟩
  have hx0 : 0 < x := lt_of_lt_of_le ha hxIcc.1
  have hx1 : x < 1 := lt_of_le_of_lt hxIcc.2 hc
  have hφψ_top : Tendsto (fun j : ℕ => φ (ψ j)) atTop atTop :=
    hφmono.tendsto_atTop.comp hψmono.tendsto_atTop
  have hφψ_real_top :
      Tendsto (fun j : ℕ => (φ (ψ j) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp hφψ_top
  have hk_le :
      ∀ᶠ j : ℕ in atTop, k (ψ j) ≤ φ (ψ j) :=
    Filter.Eventually.of_forall fun j => (hk (ψ j)).1
  have hk_ratio :
      Tendsto (fun j : ℕ => (k (ψ j) : ℝ) / (φ (ψ j) : ℝ))
        atTop (𝓝 x) := by
    simpa [r, Function.comp_def] using hψtend
  have hrest_ratio :
      Tendsto
        (fun j : ℕ => ((φ (ψ j) - k (ψ j) : ℕ) : ℝ) / (φ (ψ j) : ℝ))
        atTop (𝓝 (1 - x)) := by
    have hone_sub :
        Tendsto
          (fun j : ℕ => 1 - (k (ψ j) : ℝ) / (φ (ψ j) : ℝ))
          atTop (𝓝 (1 - x)) :=
      tendsto_const_nhds.sub hk_ratio
    refine Tendsto.congr' ?_ hone_sub
    filter_upwards with j
    have hle : k (ψ j) ≤ φ (ψ j) := (hk (ψ j)).1
    have hφ_pos_real : 0 < (φ (ψ j) : ℝ) := by
      exact_mod_cast hφ_pos (ψ j)
    have hφ_ne : (φ (ψ j) : ℝ) ≠ 0 := ne_of_gt hφ_pos_real
    calc
      1 - (k (ψ j) : ℝ) / (φ (ψ j) : ℝ)
          = ((φ (ψ j) : ℝ) - (k (ψ j) : ℝ)) / (φ (ψ j) : ℝ) := by
            field_simp [hφ_ne]
      _ = ((φ (ψ j) - k (ψ j) : ℕ) : ℝ) / (φ (ψ j) : ℝ) := by
            rw [Nat.cast_sub hle]
  have hk_top : Tendsto (fun j : ℕ => k (ψ j)) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro m
    have hlarge :
        ∀ᶠ j : ℕ in atTop, (m : ℝ) / a ≤ (φ (ψ j) : ℝ) :=
      hφψ_real_top.eventually_ge_atTop ((m : ℝ) / a)
    rcases eventually_atTop.1 hlarge with ⟨J, hJ⟩
    refine ⟨J, ?_⟩
    intro j hj
    have hNlarge := hJ j hj
    have hφ_pos_real : 0 < (φ (ψ j) : ℝ) := by
      exact_mod_cast hφ_pos (ψ j)
    have hlower : a ≤ (k (ψ j) : ℝ) / (φ (ψ j) : ℝ) :=
      (hk (ψ j)).2.1
    have hmul_left : (m : ℝ) ≤ a * (φ (ψ j) : ℝ) := by
      calc
        (m : ℝ) = ((m : ℝ) / a) * a := by
          field_simp [ne_of_gt ha]
        _ ≤ (φ (ψ j) : ℝ) * a :=
          mul_le_mul_of_nonneg_right hNlarge (le_of_lt ha)
        _ = a * (φ (ψ j) : ℝ) := by ring
    have hmul_right : a * (φ (ψ j) : ℝ) ≤ (k (ψ j) : ℝ) :=
      (le_div_iff₀ hφ_pos_real).mp hlower
    exact Nat.cast_le.mp (le_trans hmul_left hmul_right)
  have hrest_top :
      Tendsto (fun j : ℕ => φ (ψ j) - k (ψ j)) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro m
    let d : ℝ := 1 - c
    have hd_pos : 0 < d := by
      dsimp [d]
      exact sub_pos.mpr hc
    have hlarge :
        ∀ᶠ j : ℕ in atTop, (m : ℝ) / d ≤ (φ (ψ j) : ℝ) :=
      hφψ_real_top.eventually_ge_atTop ((m : ℝ) / d)
    rcases eventually_atTop.1 hlarge with ⟨J, hJ⟩
    refine ⟨J, ?_⟩
    intro j hj
    have hNlarge := hJ j hj
    have hle : k (ψ j) ≤ φ (ψ j) := (hk (ψ j)).1
    have hφ_pos_real : 0 < (φ (ψ j) : ℝ) := by
      exact_mod_cast hφ_pos (ψ j)
    have hupper : (k (ψ j) : ℝ) / (φ (ψ j) : ℝ) ≤ c :=
      (hk (ψ j)).2.2.1
    have hmul_left : (m : ℝ) ≤ d * (φ (ψ j) : ℝ) := by
      calc
        (m : ℝ) = ((m : ℝ) / d) * d := by
          field_simp [ne_of_gt hd_pos]
        _ ≤ (φ (ψ j) : ℝ) * d :=
          mul_le_mul_of_nonneg_right hNlarge (le_of_lt hd_pos)
        _ = d * (φ (ψ j) : ℝ) := by ring
    have hK_le : (k (ψ j) : ℝ) ≤ c * (φ (ψ j) : ℝ) :=
      (div_le_iff₀ hφ_pos_real).mp hupper
    have hmul_right :
        d * (φ (ψ j) : ℝ) ≤ ((φ (ψ j) - k (ψ j) : ℕ) : ℝ) := by
      rw [Nat.cast_sub hle]
      dsimp [d]
      nlinarith
    exact Nat.cast_le.mp (le_trans hmul_left hmul_right)
  have hφψ_pos :
      ∀ᶠ j : ℕ in atTop, 0 < φ (ψ j) :=
    Filter.Eventually.of_forall fun j => hφ_pos (ψ j)
  have hk_pos :
      ∀ᶠ j : ℕ in atTop, 0 < k (ψ j) := by
    filter_upwards [hk_top.eventually_ge_atTop 1] with j hj
    exact hj
  have hrest_pos :
      ∀ᶠ j : ℕ in atTop, 0 < φ (ψ j) - k (ψ j) := by
    filter_upwards [hrest_top.eventually_ge_atTop 1] with j hj
    exact hj
  have hlocal :
      Tendsto
        (fun j : ℕ =>
          (φ (ψ j) : ℝ) *
            prob_14_1_polyaWhiteMassFormula w b (φ (ψ j)) (k (ψ j)))
        atTop
        (𝓝 (prob_14_1_betaDensity w b (1 / ProbabilityTheory.beta w b) x)) :=
    prob_14_1_scaled_polya_mass_tendsto_betaDensity_of_total_count_sequence
      hw hb hx0 hx1
      (fun j : ℕ => φ (ψ j)) (fun j : ℕ => k (ψ j))
      hk_le hφψ_top hk_top hrest_top hk_ratio hrest_ratio
      hφψ_pos hk_pos hrest_pos
  have hdensity_grid :
      Tendsto
        (fun j : ℕ =>
          prob_14_1_betaDensity w b (1 / ProbabilityTheory.beta w b)
            ((k (ψ j) : ℝ) / (φ (ψ j) : ℝ)))
        atTop
        (𝓝 (prob_14_1_betaDensity w b (1 / ProbabilityTheory.beta w b) x)) := by
    have hxrest : 0 < 1 - x := sub_pos.mpr hx1
    have hone_sub :
        Tendsto
          (fun j : ℕ => 1 - (k (ψ j) : ℝ) / (φ (ψ j) : ℝ))
          atTop (𝓝 (1 - x)) :=
      tendsto_const_nhds.sub hk_ratio
    have hkpow :
        Tendsto
          (fun j : ℕ => ((k (ψ j) : ℝ) / (φ (ψ j) : ℝ)) ^ (w - 1))
          atTop (𝓝 (x ^ (w - 1))) :=
      hk_ratio.rpow tendsto_const_nhds (Or.inl hx0.ne')
    have hrpow :
        Tendsto
          (fun j : ℕ =>
            (1 - (k (ψ j) : ℝ) / (φ (ψ j) : ℝ)) ^ (b - 1))
          atTop (𝓝 ((1 - x) ^ (b - 1))) :=
      hone_sub.rpow tendsto_const_nhds (Or.inl hxrest.ne')
    have hexpr :
        Tendsto
          (fun j : ℕ =>
            (1 / ProbabilityTheory.beta w b) *
              ((k (ψ j) : ℝ) / (φ (ψ j) : ℝ)) ^ (w - 1) *
              (1 - (k (ψ j) : ℝ) / (φ (ψ j) : ℝ)) ^ (b - 1))
          atTop
          (𝓝 ((1 / ProbabilityTheory.beta w b) *
            x ^ (w - 1) * (1 - x) ^ (b - 1))) := by
      simpa [mul_assoc] using
        ((tendsto_const_nhds.mul hkpow).mul hrpow)
    have hdensity_x :
        (1 / ProbabilityTheory.beta w b) *
          x ^ (w - 1) * (1 - x) ^ (b - 1) =
        prob_14_1_betaDensity w b (1 / ProbabilityTheory.beta w b) x := by
      have hxmem : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx0, hx1⟩
      simp [prob_14_1_betaDensity, hxmem, mul_assoc]
    rw [← hdensity_x]
    refine Tendsto.congr' ?_ hexpr
    filter_upwards with j
    have hmem : ((k (ψ j) : ℝ) / (φ (ψ j) : ℝ)) ∈ Set.Ioo (0 : ℝ) 1 := by
      exact ⟨lt_of_lt_of_le ha (hk (ψ j)).2.1,
        lt_of_le_of_lt (hk (ψ j)).2.2.1 hc⟩
    simp [prob_14_1_betaDensity, hmem, sub_eq_add_neg, mul_assoc]
  have hdiff :
      Tendsto
        (fun j : ℕ =>
          (φ (ψ j) : ℝ) *
              prob_14_1_polyaWhiteMassFormula w b (φ (ψ j)) (k (ψ j)) -
            prob_14_1_betaDensity w b (1 / ProbabilityTheory.beta w b)
              ((k (ψ j) : ℝ) / (φ (ψ j) : ℝ)))
        atTop (𝓝 (0 : ℝ)) := by
    simpa using hlocal.sub hdensity_grid
  have habs :
      Tendsto
        (fun j : ℕ =>
          |(φ (ψ j) : ℝ) *
              prob_14_1_polyaWhiteMassFormula w b (φ (ψ j)) (k (ψ j)) -
            prob_14_1_betaDensity w b (1 / ProbabilityTheory.beta w b)
              ((k (ψ j) : ℝ) / (φ (ψ j) : ℝ))|)
        atTop (𝓝 (0 : ℝ)) := by
    simpa using hdiff.abs
  have hsmall :
      ∀ᶠ j : ℕ in atTop,
        |(φ (ψ j) : ℝ) *
            prob_14_1_polyaWhiteMassFormula w b (φ (ψ j)) (k (ψ j)) -
          prob_14_1_betaDensity w b (1 / ProbabilityTheory.beta w b)
            ((k (ψ j) : ℝ) / (φ (ψ j) : ℝ))| < eps := by
    exact habs (isOpen_Iio.mem_nhds heps)
  rcases eventually_atTop.1 hsmall with ⟨J, hJ⟩
  exact not_le_of_gt (hJ J le_rfl) (hk (ψ J)).2.2.2

theorem prob_14_1_clipped_beta_kernel_continuous
    {w b a c : ℝ} (ha : 0 < a) (hac : a ≤ c) (hc : c < 1) :
    Continuous
      (fun y : PUnit.{1} → ℝ =>
        (1 / ProbabilityTheory.beta w b) *
          (min c (max a (y PUnit.unit))) ^ (w - 1) *
          (1 - min c (max a (y PUnit.unit))) ^ (b - 1)) := by
  have hmax :
      Continuous (fun y : PUnit.{1} → ℝ => max a (y PUnit.unit)) :=
    continuous_const.max (continuous_apply PUnit.unit)
  have hclip :
      Continuous (fun y : PUnit.{1} → ℝ => min c (max a (y PUnit.unit))) :=
    continuous_const.min hmax
  have hclip_pos :
      ∀ y : PUnit.{1} → ℝ, 0 < min c (max a (y PUnit.unit)) := by
    intro y
    exact lt_of_lt_of_le ha (le_min hac (le_max_left a (y PUnit.unit)))
  have hclip_lt_one :
      ∀ y : PUnit.{1} → ℝ, min c (max a (y PUnit.unit)) < 1 := by
    intro y
    exact lt_of_le_of_lt (min_le_left c (max a (y PUnit.unit))) hc
  have hpow_left :
      Continuous
        (fun y : PUnit.{1} → ℝ =>
          (min c (max a (y PUnit.unit))) ^ (w - 1)) :=
    hclip.rpow continuous_const
      (fun y => Or.inl (ne_of_gt (hclip_pos y)))
  have hsub :
      Continuous
        (fun y : PUnit.{1} → ℝ => 1 - min c (max a (y PUnit.unit))) :=
    continuous_const.sub hclip
  have hpow_right :
      Continuous
        (fun y : PUnit.{1} → ℝ =>
          (1 - min c (max a (y PUnit.unit))) ^ (b - 1)) :=
    hsub.rpow continuous_const
      (fun y => Or.inl (ne_of_gt (sub_pos.mpr (hclip_lt_one y))))
  simpa [mul_assoc] using
    ((continuous_const.mul hpow_left).mul hpow_right)

theorem prob_14_1_clipped_beta_kernel_eq_density_on_punitInterval
    {w b a c : ℝ} (ha : 0 < a) (hc : c < 1)
    {y : PUnit.{1} → ℝ} (hy : y ∈ prob_14_1_punitInterval a c) :
    (1 / ProbabilityTheory.beta w b) *
        (min c (max a (y PUnit.unit))) ^ (w - 1) *
        (1 - min c (max a (y PUnit.unit))) ^ (b - 1) =
      prob_14_1_betaDensity w b (1 / ProbabilityTheory.beta w b)
        (y PUnit.unit) := by
  rcases hy with ⟨hya, hyc⟩
  have hyIoo : y PUnit.unit ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_lt_of_le ha hya, lt_of_le_of_lt hyc hc⟩
  simp [prob_14_1_betaDensity, hyIoo, max_eq_right hya,
    min_eq_right hyc, mul_assoc]

theorem prob_14_1_Icc_card_div_nat_le_two_of_grid_bounds
    {a c : ℝ} {n lo hi : ℕ} (hn : 0 < n) (hc : c < 1)
    (hIcc :
      ∀ k : ℕ,
        (a ≤ (k : ℝ) / (n : ℝ) ∧ (k : ℝ) / (n : ℝ) ≤ c) ↔
          k ∈ Finset.Icc lo hi) :
    ((Finset.Icc lo hi).card : ℝ) / (n : ℝ) ≤ 2 := by
  have hn_pos_real : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsubset : Finset.Icc lo hi ⊆ Finset.range (n + 1) := by
    intro k hk
    have hbounds := (hIcc k).mpr hk
    have hk_ratio_lt_one : (k : ℝ) / (n : ℝ) < 1 :=
      lt_of_le_of_lt hbounds.2 hc
    have hk_lt_real : (k : ℝ) < (n : ℝ) := by
      have hmul := (div_lt_iff₀ hn_pos_real).mp hk_ratio_lt_one
      simpa using hmul
    have hk_lt_nat : k < n := by exact_mod_cast hk_lt_real
    exact Finset.mem_range.mpr (Nat.lt_succ_of_lt hk_lt_nat)
  have hcard_nat :
      (Finset.Icc lo hi).card ≤ (Finset.range (n + 1)).card :=
    Finset.card_le_card hsubset
  have hcard_real : ((Finset.Icc lo hi).card : ℝ) ≤ (n + 1 : ℕ) := by
    exact_mod_cast (by simpa using hcard_nat)
  have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hn)
  calc
    ((Finset.Icc lo hi).card : ℝ) / (n : ℝ)
        ≤ ((n + 1 : ℕ) : ℝ) / (n : ℝ) :=
          div_le_div_of_nonneg_right hcard_real hn_pos_real.le
    _ = ((n : ℝ) + 1) / (n : ℝ) := by norm_num
    _ ≤ 2 := by
          rw [div_le_iff₀ hn_pos_real]
          nlinarith

theorem prob_14_1_interior_grid_sum_tendsto_integral_of_bounds
    {w b a x : ℝ} (hw : 0 < w) (hb : 0 < b)
    (ha : 0 < a) (hax : a ≤ x) (hx : x < 1)
    (lo hi : ℕ → ℕ)
    (hIcc :
      Filter.Eventually (fun n : ℕ =>
        0 < n ∧
          ∀ k : ℕ,
            (a ≤ (k : ℝ) / (n : ℝ) ∧
              (k : ℝ) / (n : ℝ) ≤ x) ↔
              k ∈ Finset.Icc (lo n) (hi n)) atTop) :
    Tendsto
      (fun n : ℕ =>
        (Finset.Icc (lo n) (hi n)).sum
          (fun k : ℕ => prob_14_1_polyaWhiteMassFormula w b n k))
      atTop
      (𝓝 (∫ y in prob_14_1_punitInterval a x,
        prob_14_1_betaDensity w b (1 / ProbabilityTheory.beta w b)
          (y PUnit.unit))) := by
  let clippedF : (PUnit.{1} → ℝ) → ℝ :=
    fun y =>
      (1 / ProbabilityTheory.beta w b) *
        (min x (max a (y PUnit.unit))) ^ (w - 1) *
        (1 - min x (max a (y PUnit.unit))) ^ (b - 1)
  let densityF : (PUnit.{1} → ℝ) → ℝ :=
    fun y =>
      prob_14_1_betaDensity w b (1 / ProbabilityTheory.beta w b)
        (y PUnit.unit)
  let massSum : ℕ → ℝ :=
    fun n =>
      (Finset.Icc (lo n) (hi n)).sum
        (fun k : ℕ => prob_14_1_polyaWhiteMassFormula w b n k)
  let densitySum : ℕ → ℝ :=
    fun n =>
      (1 / (n : ℝ)) *
        (Finset.Icc (lo n) (hi n)).sum
          (fun k : ℕ =>
            densityF (fun _ : PUnit.{1} => (k : ℝ) / (n : ℝ)))
  let target : ℝ := ∫ y in prob_14_1_punitInterval a x, densityF y
  change Tendsto massSum atTop (𝓝 target)
  have hClippedContinuous : Continuous clippedF := by
    simpa [clippedF] using
      prob_14_1_clipped_beta_kernel_continuous
        (w := w) (b := b) (a := a) (c := x) ha hax hx
  have hIntegralEq :
      (∫ y in prob_14_1_punitInterval a x, clippedF y) = target := by
    refine MeasureTheory.setIntegral_congr_ae
      (prob_14_1_punitInterval_measurable a x) ?_
    exact Filter.Eventually.of_forall fun y hy => by
      simpa [clippedF, densityF] using
        prob_14_1_clipped_beta_kernel_eq_density_on_punitInterval
          (w := w) (b := b) (a := a) (c := x) ha hx hy
  have hRiemannClipped :
      Tendsto
        (fun n : ℕ =>
          (1 / (n : ℝ)) *
            (Finset.Icc (lo n) (hi n)).sum
              (fun k : ℕ =>
                clippedF (fun _ : PUnit.{1} => (k : ℝ) / (n : ℝ))))
        atTop
        (𝓝 (∫ y in prob_14_1_punitInterval a x, clippedF y)) :=
    prob_14_1_unit_partition_Icc_sum_tendsto_integral_of_bounds
      (a := a) (c := x) (F := clippedF) hClippedContinuous
      (le_of_lt ha) lo hi hIcc
  have hRiemannDensity : Tendsto densitySum atTop (𝓝 target) := by
    rw [← hIntegralEq]
    refine hRiemannClipped.congr' ?_
    filter_upwards [hIcc] with n hn
    dsimp [densitySum]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hbounds := (hn.2 k).mpr hk
    have hmem :
        (fun _ : PUnit.{1} => (k : ℝ) / (n : ℝ)) ∈
          prob_14_1_punitInterval a x := hbounds
    exact
      (prob_14_1_clipped_beta_kernel_eq_density_on_punitInterval
        (w := w) (b := b) (a := a) (c := x) ha hx hmem)
  have hCard :
      ∀ᶠ n : ℕ in atTop,
        (n : ℝ) ≠ 0 ∧
          (((Finset.Icc (lo n) (hi n)).card : ℝ) / (n : ℝ) ≤ 2) := by
    filter_upwards [hIcc] with n hn
    have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn.1)
    exact ⟨hn_ne,
      prob_14_1_Icc_card_div_nat_le_two_of_grid_bounds
        (a := a) (c := x) (n := n) (lo := lo n) (hi := hi n)
        hn.1 hx hn.2⟩
  have hUniform :
      ∀ eps > 0, ∀ᶠ n : ℕ in atTop,
        ∀ k ∈ Finset.Icc (lo n) (hi n),
          |(n : ℝ) * prob_14_1_polyaWhiteMassFormula w b n k -
            densityF (fun _ : PUnit.{1} => (k : ℝ) / (n : ℝ))| ≤ eps := by
    intro eps heps
    have hCompact :=
      prob_14_1_compact_interior_uniform_scaled_polya_mass_tendsto_betaDensity
        (w := w) (b := b) (a := a) (c := x) hw hb ha hax hx eps heps
    filter_upwards [hIcc, hCompact] with n hn hcompact k hk
    have hbounds := (hn.2 k).mpr hk
    have hn_pos_real : 0 < (n : ℝ) := by exact_mod_cast hn.1
    have hk_ratio_lt_one : (k : ℝ) / (n : ℝ) < 1 :=
      lt_of_le_of_lt hbounds.2 hx
    have hk_lt_real : (k : ℝ) < (n : ℝ) := by
      have hmul := (div_lt_iff₀ hn_pos_real).mp hk_ratio_lt_one
      simpa using hmul
    have hk_le_n : k ≤ n := by
      have hk_lt_nat : k < n := by exact_mod_cast hk_lt_real
      exact Nat.le_of_lt hk_lt_nat
    simpa [densityF] using
      le_of_lt (hcompact k hk_le_n hbounds.1 hbounds.2)
  have hErrorAbs :
      Tendsto
        (fun n : ℕ => |massSum n - densitySum n|)
        atTop (𝓝 (0 : ℝ)) := by
    simpa [massSum, densitySum, densityF] using
      prob_14_1_sum_scaled_error_tendsto_zero
        (s := fun n : ℕ => Finset.Icc (lo n) (hi n))
        (p := fun n k => prob_14_1_polyaWhiteMassFormula w b n k)
        (f := fun n k =>
          prob_14_1_betaDensity w b (1 / ProbabilityTheory.beta w b)
            ((k : ℝ) / (n : ℝ)))
        (M := (2 : ℝ)) (by norm_num) hCard hUniform
  have hDensityDiff :
      Tendsto
        (fun n : ℕ => |densitySum n - target|)
        atTop (𝓝 (0 : ℝ)) := by
    simpa [Real.norm_eq_abs] using
      (tendsto_iff_norm_sub_tendsto_zero.mp hRiemannDensity)
  refine Metric.tendsto_atTop.2 ?_
  intro eps heps
  let δ : ℝ := eps / 2
  have hδ_pos : 0 < δ := by positivity
  have hSmallError :
      ∀ᶠ n : ℕ in atTop, |massSum n - densitySum n| < δ :=
    hErrorAbs (isOpen_Iio.mem_nhds hδ_pos)
  have hSmallRiemann :
      ∀ᶠ n : ℕ in atTop, |densitySum n - target| < δ :=
    hDensityDiff (isOpen_Iio.mem_nhds hδ_pos)
  rcases eventually_atTop.1 (hSmallError.and hSmallRiemann) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  rcases hN n hn with ⟨hErr, hRiem⟩
  have htriangle :
      |massSum n - target| ≤
        |massSum n - densitySum n| + |densitySum n - target| := by
    calc
      |massSum n - target|
          = |(massSum n - densitySum n) + (densitySum n - target)| := by ring
      _ ≤ |massSum n - densitySum n| + |densitySum n - target| := abs_add_le _ _
  have hlt : |massSum n - target| < eps := by
    have hsum : |massSum n - densitySum n| + |densitySum n - target| < eps := by
      dsimp [δ] at hErr hRiem
      linarith
    exact lt_of_le_of_lt htriangle hsum
  simpa [Real.dist_eq] using hlt

theorem prob_14_1_beta_law_Ioo_eq_one
    {w b : ℝ} (beta : prob_14_1_BetaLawData w b) :
    (beta.law : Measure ℝ) (Set.Ioo (0 : ℝ) 1) = 1 := by
  have hcompl :
      (beta.law : Measure ℝ) (Set.Ioo (0 : ℝ) 1)ᶜ = 0 := by
    rw [beta.density_represents_law
      (Set.Ioo (0 : ℝ) 1)ᶜ measurableSet_Ioo.compl]
    apply lintegral_eq_zero_of_ae_eq_zero
    exact Filter.Eventually.of_forall fun y => by
      by_cases hy : y ∈ (Set.Ioo (0 : ℝ) 1)ᶜ
      · have hyout : y ≤ 0 ∨ 1 ≤ y := by
          rw [Set.mem_compl_iff, Set.mem_Ioo] at hy
          by_cases h0 : 0 < y
          · right
            exact le_of_not_gt (fun h1 => hy ⟨h0, h1⟩)
          · left
            exact le_of_not_gt h0
        rw [Set.indicator_of_mem hy]
        rcases hyout with hy0 | hy1
        · simp [prob_14_1_betaDensity_eq_zero_of_nonpos (w := w) (b := b)
            (C := beta.normalizingConstant) hy0]
        · simp [prob_14_1_betaDensity_eq_zero_of_one_le (w := w) (b := b)
            (C := beta.normalizingConstant) hy1]
      · rw [Set.indicator_of_notMem hy]
        rfl
  have hEq :
      (beta.law : Measure ℝ) (Set.Ioo (0 : ℝ) 1) =
        (beta.law : Measure ℝ) Set.univ := by
    exact measure_eq_measure_of_null_diff
      (by intro y _hy; exact trivial)
      (by
        simpa [Set.diff_eq, Set.compl_inter, Set.univ_inter] using hcompl)
  rw [hEq]
  simpa using ProbabilityMeasure.coeFn_univ beta.law

theorem prob_14_1_compact_subset_Ioo_subset_Icc
    {K : Set ℝ} (hKcompact : IsCompact K)
    (hKsub : K ⊆ Set.Ioo (0 : ℝ) 1)
    (hKne : K.Nonempty) :
    ∃ a c : ℝ, 0 < a ∧ a ≤ c ∧ c < 1 ∧ K ⊆ Set.Icc a c := by
  rcases hKcompact.exists_isMinOn hKne (continuous_id.continuousOn) with
    ⟨xmin, hxmin_mem, hxmin_min⟩
  rcases hKcompact.exists_isMaxOn hKne (continuous_id.continuousOn) with
    ⟨xmax, hxmax_mem, hxmax_max⟩
  refine ⟨xmin, xmax, ?_, ?_, ?_, ?_⟩
  · exact (hKsub hxmin_mem).1
  · have hle_all : ∀ y ∈ K, xmin ≤ y := by
      intro y hy
      have hset : {z : ℝ | xmin ≤ z} ∈ Filter.principal K := by
        simpa [IsMinOn, IsMinFilter] using hxmin_min
      exact hset hy
    exact hle_all xmax hxmax_mem
  · exact (hKsub hxmax_mem).2
  · intro y hy
    constructor
    · have hset : {z : ℝ | xmin ≤ z} ∈ Filter.principal K := by
        simpa [IsMinOn, IsMinFilter] using hxmin_min
      exact hset hy
    · have hset : {z : ℝ | z ≤ xmax} ∈ Filter.principal K := by
        simpa [IsMaxOn, IsMaxFilter] using hxmax_max
      exact hset hy

theorem prob_14_1_beta_law_exists_Icc_core_gt
    {w b η : ℝ} (beta : prob_14_1_BetaLawData w b) (hη : 0 < η) :
    ∃ a c : ℝ,
      0 < a ∧ a ≤ c ∧ c < 1 ∧
        1 - η < ((beta.law : Measure ℝ) (Set.Icc a c)).toReal := by
  let δ : ℝ := min η (1 / 2)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min hη (by norm_num)
  have hδ_le_eta : δ ≤ η := by
    dsimp [δ]
    exact min_le_left η (1 / 2)
  have hδ_lt_one : δ < 1 := by
    dsimp [δ]
    exact lt_of_le_of_lt (min_le_right η (1 / 2)) (by norm_num)
  have htarget_nonneg : 0 ≤ 1 - δ := by linarith
  have htarget_pos : 0 < 1 - δ := by linarith
  have hlt_one :
      ENNReal.ofReal (1 - δ) <
        (beta.law : Measure ℝ) (Set.Ioo (0 : ℝ) 1) := by
    rw [prob_14_1_beta_law_Ioo_eq_one beta]
    rw [ENNReal.ofReal_lt_one]
    linarith
  rcases (isOpen_Ioo.exists_lt_isCompact
      (μ := (beta.law : Measure ℝ)) hlt_one) with
    ⟨K, hKsub, hKcompact, hKgt⟩
  have hK_ne_top : (beta.law : Measure ℝ) K ≠ ⊤ :=
    measure_ne_top (beta.law : Measure ℝ) K
  have hOf_ne_top : ENNReal.ofReal (1 - δ) ≠ ⊤ := by simp
  have hK_toReal_gt : 1 - δ < ((beta.law : Measure ℝ) K).toReal := by
    have hto :
        (ENNReal.ofReal (1 - δ)).toReal <
          ((beta.law : Measure ℝ) K).toReal :=
      (ENNReal.toReal_lt_toReal hOf_ne_top hK_ne_top).2 hKgt
    simpa [ENNReal.toReal_ofReal htarget_nonneg] using hto
  have hKne : K.Nonempty := by
    by_contra hnot
    have hEmpty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hnot
    have hzero : ((beta.law : Measure ℝ) K).toReal = 0 := by
      simp [hEmpty]
    linarith
  rcases prob_14_1_compact_subset_Ioo_subset_Icc hKcompact hKsub hKne with
    ⟨a, c, ha, hac, hc, hKIcc⟩
  refine ⟨a, c, ha, hac, hc, ?_⟩
  have hmono_en :
      (beta.law : Measure ℝ) K ≤ (beta.law : Measure ℝ) (Set.Icc a c) :=
    measure_mono hKIcc
  have hIcc_ne_top : (beta.law : Measure ℝ) (Set.Icc a c) ≠ ⊤ :=
    measure_ne_top (beta.law : Measure ℝ) (Set.Icc a c)
  have hmono_real :
      ((beta.law : Measure ℝ) K).toReal ≤
        ((beta.law : Measure ℝ) (Set.Icc a c)).toReal :=
    ENNReal.toReal_mono hIcc_ne_top hmono_en
  have hmain : 1 - η ≤ 1 - δ := by linarith
  exact lt_of_le_of_lt hmain (lt_of_lt_of_le hK_toReal_gt hmono_real)

theorem prob_14_1_punitInterval_eval_image (a c : ℝ) :
    (fun y : PUnit.{1} → ℝ => y PUnit.unit) ''
      prob_14_1_punitInterval a c = Set.Icc a c := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    refine ⟨fun _ : PUnit.{1} => x, hx, rfl⟩

theorem prob_14_1_punitInterval_integral_eq_real_Icc_integral
    {a c : ℝ} (F : ℝ → ℝ) :
    (∫ y in prob_14_1_punitInterval a c, F (y PUnit.unit)) =
      ∫ x in Set.Icc a c, F x := by
  let e : ((PUnit.{1} → ℝ) ≃ᵐ ℝ) :=
    MeasurableEquiv.piUnique (fun _ : PUnit.{1} => ℝ)
  have he_apply : ⇑e = fun y : PUnit.{1} → ℝ => y PUnit.unit := by
    simpa [e] using MeasurableEquiv.piUnique_apply (fun _ : PUnit.{1} => ℝ)
  have hmp_pi :=
    measurePreserving_piUnique (fun _ : PUnit.{1} => (volume : Measure ℝ))
  have hmp : MeasurePreserving (fun y : PUnit.{1} → ℝ => y PUnit.unit)
      (volume : Measure (PUnit.{1} → ℝ)) (volume : Measure ℝ) := by
    simpa [he_apply, MeasureTheory.volume_pi] using hmp_pi
  have hemb : MeasurableEmbedding (fun y : PUnit.{1} → ℝ => y PUnit.unit) := by
    simpa [he_apply] using e.measurableEmbedding
  have h := hmp.setIntegral_image_emb hemb F (prob_14_1_punitInterval a c)
  rw [prob_14_1_punitInterval_eval_image a c] at h
  exact h.symm

theorem prob_14_1_betaDensity_nonneg
    {w b C x : ℝ} (hC : 0 ≤ C) :
    0 ≤ prob_14_1_betaDensity w b C x := by
  rw [prob_14_1_betaDensity]
  by_cases hx : x ∈ Set.Ioo (0 : ℝ) 1
  · rw [if_pos hx]
    have hx0 : 0 ≤ x := le_of_lt hx.1
    have hx1 : 0 ≤ 1 - x := sub_nonneg.mpr (le_of_lt hx.2)
    exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hx0 (w - 1)))
      (Real.rpow_nonneg hx1 (b - 1))
  · rw [if_neg hx]

theorem prob_14_1_clipped_beta_kernel_real_continuous
    {w b C a c : ℝ} (ha : 0 < a) (hac : a ≤ c) (hc : c < 1) :
    Continuous
      (fun x : ℝ =>
        C * (min c (max a x)) ^ (w - 1) *
          (1 - min c (max a x)) ^ (b - 1)) := by
  have hmax : Continuous (fun x : ℝ => max a x) :=
    continuous_const.max continuous_id
  have hclip : Continuous (fun x : ℝ => min c (max a x)) :=
    continuous_const.min hmax
  have hclip_pos : ∀ x : ℝ, 0 < min c (max a x) := by
    intro x
    exact lt_of_lt_of_le ha (le_min hac (le_max_left a x))
  have hclip_lt_one : ∀ x : ℝ, min c (max a x) < 1 := by
    intro x
    exact lt_of_le_of_lt (min_le_left c (max a x)) hc
  have hpow_left : Continuous (fun x : ℝ => (min c (max a x)) ^ (w - 1)) :=
    hclip.rpow continuous_const (fun x => Or.inl (ne_of_gt (hclip_pos x)))
  have hsub : Continuous (fun x : ℝ => 1 - min c (max a x)) :=
    continuous_const.sub hclip
  have hpow_right : Continuous (fun x : ℝ =>
      (1 - min c (max a x)) ^ (b - 1)) :=
    hsub.rpow continuous_const
      (fun x => Or.inl (ne_of_gt (sub_pos.mpr (hclip_lt_one x))))
  simpa [mul_assoc] using ((continuous_const.mul hpow_left).mul hpow_right)

theorem prob_14_1_clipped_beta_kernel_real_eq_density_on_Icc
    {w b C a c x : ℝ} (ha : 0 < a) (hc : c < 1)
    (hx : x ∈ Set.Icc a c) :
    C * (min c (max a x)) ^ (w - 1) *
        (1 - min c (max a x)) ^ (b - 1) =
      prob_14_1_betaDensity w b C x := by
  have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hc⟩
  simp [prob_14_1_betaDensity, hxIoo, max_eq_right hx.1,
    min_eq_right hx.2, mul_assoc]

theorem prob_14_1_beta_law_Icc_toReal_eq_punit_integral
    {w b a c : ℝ} (beta : prob_14_1_BetaLawData w b)
    (ha : 0 < a) (hac : a ≤ c) (hc : c < 1) :
    ((beta.law : Measure ℝ) (Set.Icc a c)).toReal =
      ∫ y in prob_14_1_punitInterval a c,
        prob_14_1_betaDensity w b beta.normalizingConstant (y PUnit.unit) := by
  let F : ℝ → ℝ :=
    fun x => prob_14_1_betaDensity w b beta.normalizingConstant x
  have hμ :
      (beta.law : Measure ℝ) (Set.Icc a c) =
        ∫⁻ x in Set.Icc a c, ENNReal.ofReal (F x) := by
    rw [beta.density_represents_law (Set.Icc a c) measurableSet_Icc]
    rw [lintegral_indicator measurableSet_Icc]
  have hContClipped : Continuous
      (fun x : ℝ =>
        beta.normalizingConstant * (min c (max a x)) ^ (w - 1) *
          (1 - min c (max a x)) ^ (b - 1)) :=
    prob_14_1_clipped_beta_kernel_real_continuous
      (w := w) (b := b) (C := beta.normalizingConstant)
      (a := a) (c := c) ha hac hc
  have hContOn : ContinuousOn F (Set.Icc a c) := by
    refine hContClipped.continuousOn.congr ?_
    intro x hx
    dsimp [F]
    exact (prob_14_1_clipped_beta_kernel_real_eq_density_on_Icc
      (w := w) (b := b) (C := beta.normalizingConstant)
      (a := a) (c := c) ha hc hx).symm
  have hInt : IntegrableOn F (Set.Icc a c) (volume : Measure ℝ) :=
    hContOn.integrableOn_Icc
  have hNonneg :
      ∀ᵐ x ∂((volume : Measure ℝ).restrict (Set.Icc a c)), 0 ≤ F x :=
    Filter.Eventually.of_forall fun x =>
      prob_14_1_betaDensity_nonneg (w := w) (b := b)
        (C := beta.normalizingConstant) beta.normalizingConstant_pos.le
  have hIntegralLintegral :
      ∫ x in Set.Icc a c, F x =
        (∫⁻ x in Set.Icc a c, ENNReal.ofReal (F x)).toReal :=
    integral_eq_lintegral_of_nonneg_ae hNonneg hInt.integrable.aestronglyMeasurable
  calc
    ((beta.law : Measure ℝ) (Set.Icc a c)).toReal
        = (∫⁻ x in Set.Icc a c, ENNReal.ofReal (F x)).toReal := by
            rw [hμ]
    _ = ∫ x in Set.Icc a c, F x := hIntegralLintegral.symm
    _ = ∫ y in prob_14_1_punitInterval a c, F (y PUnit.unit) := by
          rw [prob_14_1_punitInterval_integral_eq_real_Icc_integral]
    _ = ∫ y in prob_14_1_punitInterval a c,
        prob_14_1_betaDensity w b beta.normalizingConstant (y PUnit.unit) := rfl

theorem prob_14_1_nat_le_floor_iff_of_nonneg {A : ℝ} (hA : 0 ≤ A) {k : ℕ} :
    k ≤ Nat.floor A ↔ (k : ℝ) ≤ A := by
  constructor
  · intro hk
    exact le_trans (by exact_mod_cast hk) (Nat.floor_le hA)
  · intro hk
    exact Nat.le_floor hk

theorem prob_14_1_grid_bounds_Icc_ceil_floor
    {a c : ℝ} {n : ℕ} (hn : 0 < n) (_ha : 0 ≤ a) (hc : 0 ≤ c) :
    ∀ k : ℕ,
      (a ≤ (k : ℝ) / (n : ℝ) ∧ (k : ℝ) / (n : ℝ) ≤ c) ↔
        k ∈ Finset.Icc (Nat.ceil (a * (n : ℝ))) (Nat.floor (c * (n : ℝ))) := by
  intro k
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcn_nonneg : 0 ≤ c * (n : ℝ) := mul_nonneg hc hnreal.le
  rw [prob_14_1_grid_div_bounds_iff_mul_le (a := a) (c := c) (n := n) (k := k) hn]
  constructor
  · intro h
    rw [Finset.mem_Icc]
    constructor
    · exact (Nat.ceil_le).2 h.1
    · exact (prob_14_1_nat_le_floor_iff_of_nonneg hcn_nonneg).2 h.2
  · intro h
    rw [Finset.mem_Icc] at h
    constructor
    · exact (Nat.ceil_le).1 h.1
    · exact (prob_14_1_nat_le_floor_iff_of_nonneg hcn_nonneg).1 h.2

theorem prob_14_1_floor_mul_le_self_nat_of_lt_one
    {c : ℝ} {n : ℕ} (_hc_nonneg : 0 ≤ c) (hc : c < 1) :
    Nat.floor (c * (n : ℝ)) ≤ n := by
  have hcn_le : c * (n : ℝ) ≤ (n : ℝ) := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    nlinarith
  exact Nat.floor_le_of_le hcn_le

theorem prob_14_1_Icc_grid_sum_tendsto_beta_law_Icc
    {w b a c : ℝ} (hw : 0 < w) (hb : 0 < b)
    (ha : 0 < a) (hac : a ≤ c) (hc : c < 1) :
    Tendsto
      (fun n : ℕ =>
        (Finset.Icc (Nat.ceil (a * (n : ℝ))) (Nat.floor (c * (n : ℝ)))).sum
          (fun k : ℕ => prob_14_1_polyaWhiteMassFormula w b n k))
      atTop
      (𝓝 (((prob_14_1_standardBetaLawData hw hb).law : Measure ℝ)
        (Set.Icc a c)).toReal) := by
  let beta := prob_14_1_standardBetaLawData hw hb
  let lo : ℕ → ℕ := fun n => Nat.ceil (a * (n : ℝ))
  let hi : ℕ → ℕ := fun n => Nat.floor (c * (n : ℝ))
  have hIcc :
      Filter.Eventually (fun n : ℕ =>
        0 < n ∧
          ∀ k : ℕ,
            (a ≤ (k : ℝ) / (n : ℝ) ∧
              (k : ℝ) / (n : ℝ) ≤ c) ↔
              k ∈ Finset.Icc (lo n) (hi n)) atTop := by
    exact eventually_atTop.2
      ⟨1, fun n hn => by
        have hnpos : 0 < n := Nat.succ_le_iff.mp hn
        exact ⟨hnpos,
          prob_14_1_grid_bounds_Icc_ceil_floor
            (a := a) (c := c) (n := n) hnpos ha.le
            (le_trans ha.le hac)⟩⟩
  have hInterior :=
    prob_14_1_interior_grid_sum_tendsto_integral_of_bounds
      (w := w) (b := b) (a := a) (x := c)
      hw hb ha hac hc lo hi hIcc
  have hTarget :
      (((beta.law : Measure ℝ) (Set.Icc a c)).toReal) =
        ∫ y in prob_14_1_punitInterval a c,
          prob_14_1_betaDensity w b (1 / ProbabilityTheory.beta w b)
            (y PUnit.unit) := by
    have h :=
      prob_14_1_beta_law_Icc_toReal_eq_punit_integral
        (w := w) (b := b) (a := a) (c := c) beta ha hac hc
    simpa [beta, prob_14_1_standardBetaLawData] using h
  rw [hTarget]
  simpa [lo, hi, one_div] using hInterior
