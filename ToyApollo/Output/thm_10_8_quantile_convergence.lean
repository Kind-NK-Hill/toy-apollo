/-
TASK ID: thm_10_8_quantile_convergence
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_10_8_inverse_comparison

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

instance thm_10_8_unitIntervalMeasure_noAtoms :
    NoAtoms thm_10_8_unitIntervalMeasure := by
  rw [thm_10_8_unitIntervalMeasure]
  infer_instance

theorem thm_10_8_tendsto_of_liminf_limsup_sandwich
    (u : ℕ → ℝ) (a : ℝ)
    (hinf : a ≤ Filter.liminf u atTop)
    (hsup : Filter.limsup u atTop ≤ a)
    (hboundedAbove : atTop.IsBoundedUnder (· ≤ ·) u)
    (hboundedBelow : atTop.IsBoundedUnder (· ≥ ·) u) :
    Tendsto u atTop (nhds a) :=
  tendsto_of_le_liminf_of_limsup_le hinf hsup hboundedAbove hboundedBelow

theorem thm_10_8_lowerQuantile_le_upperQuantile
    (F : thm_10_8_ProbabilityCdf) {omega : ℝ}
    (homega0 : 0 < omega) (homega1 : omega < 1) :
    thm_10_8_lowerQuantile F omega ≤ thm_10_8_upperQuantile F omega := by
  have hupper_ne :
      (thm_10_8_upperQuantileSet F omega).Nonempty :=
    thm_10_8_upperQuantileSet_nonempty_of_lt_one F homega1
  refine le_csInf hupper_ne ?_
  intro y hy
  have hlower_ne :
      (thm_10_8_lowerQuantileSet F omega).Nonempty :=
    thm_10_8_lowerQuantileSet_nonempty_of_pos F homega0
  refine csSup_le hlower_ne ?_
  intro z hz
  by_contra hnot
  have hyz : y < z := not_le.mp hnot
  have hFy_le_Fz : F.stieltjes y ≤ F.stieltjes z :=
    (thm_10_8_probabilityCdf_monotone F) hyz.le
  have hzlt : F.stieltjes z < omega := hz
  have hygt : omega < F.stieltjes y := hy
  linarith

theorem thm_10_8_le_stieltjes_of_lowerQuantile_lt
    (F : thm_10_8_ProbabilityCdf) {omega x : ℝ}
    (_homega0 : 0 < omega) (homega1 : omega < 1)
    (hx : thm_10_8_lowerQuantile F omega < x) :
    omega ≤ F.stieltjes x := by
  by_contra hnot
  have hxlt : F.stieltjes x < omega := lt_of_not_ge hnot
  have hbdd := thm_10_8_lowerQuantileSet_bddAbove_of_lt_one F homega1
  have hx_le :
      x ≤ thm_10_8_lowerQuantile F omega := by
    simpa [thm_10_8_lowerQuantile, thm_10_8_lowerQuantileSet] using
      (le_csSup hbdd
        (show x ∈ thm_10_8_lowerQuantileSet F omega from hxlt))
  linarith

theorem thm_10_8_stieltjes_le_of_lt_upperQuantile
    (F : thm_10_8_ProbabilityCdf) {omega x : ℝ}
    (homega0 : 0 < omega) (_homega1 : omega < 1)
    (hx : x < thm_10_8_upperQuantile F omega) :
    F.stieltjes x ≤ omega := by
  by_contra hnot
  have hxgt : omega < F.stieltjes x := lt_of_not_ge hnot
  have hbdd := thm_10_8_upperQuantileSet_bddBelow_of_pos F homega0
  have hupper_le :
      thm_10_8_upperQuantile F omega ≤ x := by
    simpa [thm_10_8_upperQuantile, thm_10_8_upperQuantileSet] using
      (csInf_le hbdd
        (show x ∈ thm_10_8_upperQuantileSet F omega from hxgt))
  linarith

theorem thm_10_8_stieltjes_eq_of_between_quantiles
    (F : thm_10_8_ProbabilityCdf) {omega x : ℝ}
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hlower : thm_10_8_lowerQuantile F omega < x)
    (hupper : x < thm_10_8_upperQuantile F omega) :
    F.stieltjes x = omega := by
  have hle := thm_10_8_le_stieltjes_of_lowerQuantile_lt
    F homega0 homega1 hlower
  have hge := thm_10_8_stieltjes_le_of_lt_upperQuantile
    F homega0 homega1 hupper
  exact le_antisymm hge hle

theorem thm_10_8_stieltjes_lt_of_lt_lowerQuantile
    (F : thm_10_8_ProbabilityCdf) {omega x : ℝ}
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hx : x < thm_10_8_lowerQuantile F omega) :
    F.stieltjes x < omega := by
  have hne := thm_10_8_lowerQuantileSet_nonempty_of_pos F homega0
  have hbdd := thm_10_8_lowerQuantileSet_bddAbove_of_lt_one F homega1
  have hx' :
      x < sSup (thm_10_8_lowerQuantileSet F omega) := by
    simpa [thm_10_8_lowerQuantile, thm_10_8_lowerQuantileSet] using hx
  rcases (lt_csSup_iff hbdd hne).1 hx' with ⟨z, hz, hxz⟩
  have hFx_le_Fz : F.stieltjes x ≤ F.stieltjes z :=
    (thm_10_8_probabilityCdf_monotone F) hxz.le
  exact lt_of_le_of_lt hFx_le_Fz hz

theorem thm_10_8_stieltjes_gt_of_upperQuantile_lt
    (F : thm_10_8_ProbabilityCdf) {omega x : ℝ}
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hx : thm_10_8_upperQuantile F omega < x) :
    omega < F.stieltjes x := by
  have hne := thm_10_8_upperQuantileSet_nonempty_of_lt_one F homega1
  have hbdd := thm_10_8_upperQuantileSet_bddBelow_of_pos F homega0
  have hx' :
      sInf (thm_10_8_upperQuantileSet F omega) < x := by
    simpa [thm_10_8_upperQuantile, thm_10_8_upperQuantileSet] using hx
  rcases (csInf_lt_iff hbdd hne).1 hx' with ⟨z, hz, hzx⟩
  have hFz_le_Fx : F.stieltjes z ≤ F.stieltjes x :=
    (thm_10_8_probabilityCdf_monotone F) hzx.le
  exact lt_of_lt_of_le hz hFz_le_Fx

theorem thm_10_8_exists_continuity_point_between
    (F : thm_10_8_ProbabilityCdf) {a b : ℝ} (hab : a < b) :
    ∃ y : ℝ, a < y ∧ y < b ∧
      ContinuousAt (F.stieltjes : ℝ → ℝ) y := by
  have hdense :
      Dense ({x : ℝ | ¬ ContinuousAt (F.stieltjes : ℝ → ℝ) x}ᶜ) :=
    (thm_10_8_cdf_discontinuities_countable F).dense_compl ℝ
  rcases hdense.exists_between hab with ⟨y, hyc, hya, hyb⟩
  refine ⟨y, hya, hyb, ?_⟩
  simpa using hyc

theorem thm_10_8_bad_quantile_levels_countable
    (F : thm_10_8_ProbabilityCdf) :
    Set.Countable
      {omega : ℝ |
        0 < omega ∧ omega < 1 ∧
          thm_10_8_lowerQuantile F omega <
            thm_10_8_upperQuantile F omega} := by
  have hcount :
      Set.Countable
        {c : ℝ | ∃ x y : ℝ, x < y ∧
          (F.stieltjes : ℝ → ℝ) x = c ∧
          (F.stieltjes : ℝ → ℝ) y = c} :=
    (thm_10_8_probabilityCdf_monotone F).countable_setOf_two_preimages
  refine hcount.mono ?_
  intro omega homega
  rcases homega with ⟨homega0, homega1, hbad⟩
  let x := (2 * thm_10_8_lowerQuantile F omega +
    thm_10_8_upperQuantile F omega) / 3
  let y := (thm_10_8_lowerQuantile F omega +
    2 * thm_10_8_upperQuantile F omega) / 3
  have hx_lower : thm_10_8_lowerQuantile F omega < x := by
    dsimp [x]
    linarith
  have hxy : x < y := by
    dsimp [x, y]
    linarith
  have hy_upper : y < thm_10_8_upperQuantile F omega := by
    dsimp [y]
    linarith
  have hx_upper : x < thm_10_8_upperQuantile F omega := hxy.trans hy_upper
  have hy_lower : thm_10_8_lowerQuantile F omega < y := hx_lower.trans hxy
  refine ⟨x, y, hxy, ?_, ?_⟩
  · exact thm_10_8_stieltjes_eq_of_between_quantiles
      F homega0 homega1 hx_lower hx_upper
  · exact thm_10_8_stieltjes_eq_of_between_quantiles
      F homega0 homega1 hy_lower hy_upper

theorem thm_10_8_lower_upper_quantile_ae_eq
    (F : thm_10_8_ProbabilityCdf) :
    ∀ᵐ omega ∂thm_10_8_unitIntervalMeasure,
      0 < omega ∧ omega < 1 →
        thm_10_8_lowerQuantile F omega =
          thm_10_8_upperQuantile F omega := by
  have hbad_count := thm_10_8_bad_quantile_levels_countable F
  filter_upwards [hbad_count.ae_notMem thm_10_8_unitIntervalMeasure]
    with omega hnot_bad homega
  have hle := thm_10_8_lowerQuantile_le_upperQuantile F homega.1 homega.2
  exact le_antisymm hle
    (not_lt.mp fun hlt => hnot_bad ⟨homega.1, homega.2, hlt⟩)

theorem thm_10_8_lowerQuantile_tendsto_at_good_level
    (Fs : ℕ → thm_10_8_ProbabilityCdf) (F : thm_10_8_ProbabilityCdf)
    (hconv :
      ∀ x : ℝ, ContinuousAt (F.stieltjes : ℝ → ℝ) x →
        Tendsto (fun n : ℕ => (Fs n).stieltjes x) atTop
          (𝓝 (F.stieltjes x)))
    {omega : ℝ} (homega0 : 0 < omega) (homega1 : omega < 1)
    (heq :
      thm_10_8_lowerQuantile F omega =
        thm_10_8_upperQuantile F omega) :
    Tendsto (fun n : ℕ => thm_10_8_lowerQuantile (Fs n) omega) atTop
      (nhds (thm_10_8_lowerQuantile F omega)) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    rcases thm_10_8_exists_continuity_point_between F ha with
      ⟨y, hay, hyQ, hcont⟩
    have hylt : F.stieltjes y < omega :=
      thm_10_8_stieltjes_lt_of_lt_lowerQuantile F homega0 homega1 hyQ
    exact (thm_10_8_eventually_le_lowerQuantile_of_continuity
      Fs F hconv homega1 hcont hylt).mono fun n hyn =>
        hay.trans_le hyn
  · intro b hb
    have hupper_lt_b : thm_10_8_upperQuantile F omega < b := by
      simpa [heq.symm] using hb
    rcases thm_10_8_exists_continuity_point_between F hupper_lt_b with
      ⟨y, hQy, hyb, hcont⟩
    have hygt : omega < F.stieltjes y :=
      thm_10_8_stieltjes_gt_of_upperQuantile_lt F homega0 homega1 hQy
    have h_event_upper :
        ∀ᶠ n : ℕ in atTop,
          thm_10_8_upperQuantile (Fs n) omega ≤ y :=
      thm_10_8_eventually_upperQuantile_le_of_continuity
        Fs F hconv homega0 hcont hygt
    exact h_event_upper.mono fun n hn =>
      ((thm_10_8_lowerQuantile_le_upperQuantile
        (Fs n) homega0 homega1).trans hn).trans_lt hyb

theorem thm_10_8_almost_sure_lowerQuantile_tendsto
    (Fs : ℕ → thm_10_8_ProbabilityCdf) (F : thm_10_8_ProbabilityCdf)
    (hconv :
      ∀ x : ℝ, ContinuousAt (F.stieltjes : ℝ → ℝ) x →
        Tendsto (fun n : ℕ => (Fs n).stieltjes x) atTop
          (𝓝 (F.stieltjes x))) :
    ∀ᵐ omega ∂thm_10_8_unitIntervalMeasure,
      Tendsto
        (fun n : ℕ => thm_10_8_lowerQuantileVariable (Fs n) omega)
        atTop
        (nhds (thm_10_8_lowerQuantileVariable F omega)) := by
  have hIoc :
      ∀ᵐ omega ∂thm_10_8_unitIntervalMeasure,
        omega ∈ Ioc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioc
  have hne_one :
      ∀ᵐ omega ∂thm_10_8_unitIntervalMeasure,
        omega ≠ (1 : ℝ) :=
    (countable_singleton (1 : ℝ)).ae_notMem thm_10_8_unitIntervalMeasure
  filter_upwards
    [hIoc, hne_one, thm_10_8_lower_upper_quantile_ae_eq F]
    with omega homega_Ioc homega_ne_one heq
  have homega0 : 0 < omega := homega_Ioc.1
  have homega1 : omega < 1 :=
    lt_of_le_of_ne homega_Ioc.2 homega_ne_one
  have hunit : 0 < omega ∧ omega < 1 := ⟨homega0, homega1⟩
  have htendsto :=
    thm_10_8_lowerQuantile_tendsto_at_good_level
      Fs F hconv homega0 homega1 (heq hunit)
  simpa [thm_10_8_lowerQuantileVariable, hunit] using htendsto

theorem thm_10_8_lowerQuantile_tendsto_of_liminf_limsup_sandwich
    (Fs : ℕ → thm_10_8_ProbabilityCdf) (F : thm_10_8_ProbabilityCdf)
    (omega : ℝ)
    (hinf :
      thm_10_8_lowerQuantile F omega ≤
        Filter.liminf (fun n : ℕ => thm_10_8_lowerQuantile (Fs n) omega) atTop)
    (hsup :
      Filter.limsup (fun n : ℕ => thm_10_8_lowerQuantile (Fs n) omega) atTop ≤
        thm_10_8_lowerQuantile F omega)
    (hboundedAbove :
      atTop.IsBoundedUnder (· ≤ ·)
        (fun n : ℕ => thm_10_8_lowerQuantile (Fs n) omega))
    (hboundedBelow :
      atTop.IsBoundedUnder (· ≥ ·)
        (fun n : ℕ => thm_10_8_lowerQuantile (Fs n) omega)) :
    Tendsto (fun n : ℕ => thm_10_8_lowerQuantile (Fs n) omega) atTop
      (nhds (thm_10_8_lowerQuantile F omega)) :=
  thm_10_8_tendsto_of_liminf_limsup_sandwich
    (fun n : ℕ => thm_10_8_lowerQuantile (Fs n) omega)
    (thm_10_8_lowerQuantile F omega)
    hinf hsup hboundedAbove hboundedBelow
