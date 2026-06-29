/-
TASK ID: thm_10_8_inverse_comparison
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_10_4
import ToyApollo.Output.prob_3_5
import ToyApollo.Output.thm_10_8_quantile_defs

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

noncomputable section

theorem thm_10_8_cdf_discontinuities_countable
    (F : thm_10_8_ProbabilityCdf) :
    Set.Countable {x : ℝ | ¬ ContinuousAt (F.stieltjes : ℝ → ℝ) x} := by
  have htotal : F.stieltjes.measure Set.univ = 1 := by
    rw [StieltjesFunction.measure_univ
      F.stieltjes F.tendsto_atBot F.tendsto_atTop]
    norm_num
  simpa using prob_3_5 F.stieltjes htotal

theorem thm_10_8_upperQuantileSet_nonempty_of_lt_one
    (F : thm_10_8_ProbabilityCdf) {omega : ℝ} (homega : omega < 1) :
    (thm_10_8_upperQuantileSet F omega).Nonempty := by
  have hmid_gt : omega < (omega + 1) / 2 := by linarith
  have hmid_lt : (omega + 1) / 2 < 1 := by linarith
  have h_ev : ∀ᶠ x in atTop, (omega + 1) / 2 < F.stieltjes x :=
    F.tendsto_atTop (Ioi_mem_nhds hmid_lt)
  rw [eventually_atTop] at h_ev
  rcases h_ev with ⟨M, hM⟩
  exact ⟨M, by
    have hM' : (omega + 1) / 2 < F.stieltjes M := hM M le_rfl
    exact hmid_gt.trans hM'⟩

theorem thm_10_8_upperQuantileSet_bddBelow_of_pos
    (F : thm_10_8_ProbabilityCdf) {omega : ℝ} (homega : 0 < omega) :
    BddBelow (thm_10_8_upperQuantileSet F omega) := by
  have h_ev : ∀ᶠ x in atBot, F.stieltjes x < omega :=
    F.tendsto_atBot (Iio_mem_nhds homega)
  rw [eventually_atBot] at h_ev
  rcases h_ev with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro y hy
  by_contra hnot
  have hyM : y < M := not_le.mp hnot
  have hFy_le : F.stieltjes y ≤ F.stieltjes M :=
    (thm_10_8_probabilityCdf_monotone F) hyM.le
  have hFM : F.stieltjes M < omega := hM M le_rfl
  have hωFy : omega < F.stieltjes y := hy
  linarith

theorem thm_10_8_upperQuantile_le_of_stieltjes_gt
    (F : thm_10_8_ProbabilityCdf) {omega y : ℝ}
    (homega : 0 < omega) (hy : omega < F.stieltjes y) :
    thm_10_8_upperQuantile F omega ≤ y := by
  have hbdd := thm_10_8_upperQuantileSet_bddBelow_of_pos F homega
  simpa [thm_10_8_upperQuantile, thm_10_8_upperQuantileSet] using
    (csInf_le hbdd (show y ∈ thm_10_8_upperQuantileSet F omega from hy))

theorem thm_10_8_le_lowerQuantile_of_stieltjes_lt
    (F : thm_10_8_ProbabilityCdf) {omega y : ℝ}
    (homega : omega < 1) (hy : F.stieltjes y < omega) :
    y ≤ thm_10_8_lowerQuantile F omega := by
  have hbdd := thm_10_8_lowerQuantileSet_bddAbove_of_lt_one F homega
  simpa [thm_10_8_lowerQuantile, thm_10_8_lowerQuantileSet] using
    (le_csSup hbdd (show y ∈ thm_10_8_lowerQuantileSet F omega from hy))

theorem thm_10_8_eventually_upperQuantile_le_of_continuity
    (Fs : ℕ → thm_10_8_ProbabilityCdf) (F : thm_10_8_ProbabilityCdf)
    (hconv :
      CdfConvergesInDistribution
        (fun n x => (Fs n).stieltjes x) (F.stieltjes : ℝ → ℝ))
    {omega y : ℝ} (homega : 0 < omega)
    (hcont : ContinuousAt (F.stieltjes : ℝ → ℝ) y)
    (hy : omega < F.stieltjes y) :
    ∀ᶠ n : ℕ in atTop, thm_10_8_upperQuantile (Fs n) omega ≤ y := by
  have h_ev : ∀ᶠ n : ℕ in atTop, omega < (Fs n).stieltjes y :=
    (hconv y hcont).eventually (Ioi_mem_nhds hy)
  exact h_ev.mono fun n hn =>
    thm_10_8_upperQuantile_le_of_stieltjes_gt (Fs n) homega hn

theorem thm_10_8_eventually_le_lowerQuantile_of_continuity
    (Fs : ℕ → thm_10_8_ProbabilityCdf) (F : thm_10_8_ProbabilityCdf)
    (hconv :
      CdfConvergesInDistribution
        (fun n x => (Fs n).stieltjes x) (F.stieltjes : ℝ → ℝ))
    {omega y : ℝ} (homega : omega < 1)
    (hcont : ContinuousAt (F.stieltjes : ℝ → ℝ) y)
    (hy : F.stieltjes y < omega) :
    ∀ᶠ n : ℕ in atTop, y ≤ thm_10_8_lowerQuantile (Fs n) omega := by
  have h_ev : ∀ᶠ n : ℕ in atTop, (Fs n).stieltjes y < omega :=
    (hconv y hcont).eventually (Iio_mem_nhds hy)
  exact h_ev.mono fun n hn =>
    thm_10_8_le_lowerQuantile_of_stieltjes_lt (Fs n) homega hn

theorem thm_10_8_limsup_upperQuantile_le_of_continuity
    (Fs : ℕ → thm_10_8_ProbabilityCdf) (F : thm_10_8_ProbabilityCdf)
    (hconv :
      CdfConvergesInDistribution
        (fun n x => (Fs n).stieltjes x) (F.stieltjes : ℝ → ℝ))
    {omega y : ℝ} (homega : 0 < omega)
    (hcont : ContinuousAt (F.stieltjes : ℝ → ℝ) y)
    (hy : omega < F.stieltjes y)
    (hcobdd :
      Filter.IsCoboundedUnder (· ≤ ·) atTop
        (fun n : ℕ => thm_10_8_upperQuantile (Fs n) omega)) :
    Filter.limsup (fun n : ℕ => thm_10_8_upperQuantile (Fs n) omega) atTop ≤ y := by
  exact Filter.limsup_le_of_le hcobdd
    (thm_10_8_eventually_upperQuantile_le_of_continuity
      Fs F hconv homega hcont hy)

theorem thm_10_8_le_liminf_lowerQuantile_of_continuity
    (Fs : ℕ → thm_10_8_ProbabilityCdf) (F : thm_10_8_ProbabilityCdf)
    (hconv :
      CdfConvergesInDistribution
        (fun n x => (Fs n).stieltjes x) (F.stieltjes : ℝ → ℝ))
    {omega y : ℝ} (homega : omega < 1)
    (hcont : ContinuousAt (F.stieltjes : ℝ → ℝ) y)
    (hy : F.stieltjes y < omega)
    (hcobdd :
      Filter.IsCoboundedUnder (· ≥ ·) atTop
        (fun n : ℕ => thm_10_8_lowerQuantile (Fs n) omega)) :
    y ≤ Filter.liminf (fun n : ℕ => thm_10_8_lowerQuantile (Fs n) omega) atTop := by
  exact Filter.le_liminf_of_le hcobdd
    (thm_10_8_eventually_le_lowerQuantile_of_continuity
      Fs F hconv homega hcont hy)

theorem thm_10_8_upper_lower_inverse_comparison
    (Fs : ℕ → thm_10_8_ProbabilityCdf) (F : thm_10_8_ProbabilityCdf)
    (hconv :
      CdfConvergesInDistribution
        (fun n x => (Fs n).stieltjes x) (F.stieltjes : ℝ → ℝ)) :
    (∀ {omega y : ℝ}, 0 < omega →
      ContinuousAt (F.stieltjes : ℝ → ℝ) y →
      omega < F.stieltjes y →
      ∀ᶠ n : ℕ in atTop, thm_10_8_upperQuantile (Fs n) omega ≤ y) ∧
    (∀ {omega y : ℝ}, omega < 1 →
      ContinuousAt (F.stieltjes : ℝ → ℝ) y →
      F.stieltjes y < omega →
      ∀ᶠ n : ℕ in atTop, y ≤ thm_10_8_lowerQuantile (Fs n) omega) ∧
    (∀ {omega y : ℝ}, 0 < omega →
      ContinuousAt (F.stieltjes : ℝ → ℝ) y →
      omega < F.stieltjes y →
      Filter.IsCoboundedUnder (· ≤ ·) atTop
        (fun n : ℕ => thm_10_8_upperQuantile (Fs n) omega) →
      Filter.limsup (fun n : ℕ => thm_10_8_upperQuantile (Fs n) omega) atTop ≤ y) ∧
    (∀ {omega y : ℝ}, omega < 1 →
      ContinuousAt (F.stieltjes : ℝ → ℝ) y →
      F.stieltjes y < omega →
      Filter.IsCoboundedUnder (· ≥ ·) atTop
        (fun n : ℕ => thm_10_8_lowerQuantile (Fs n) omega) →
      y ≤ Filter.liminf (fun n : ℕ => thm_10_8_lowerQuantile (Fs n) omega) atTop) := by
  constructor
  · intro omega y homega hcont hy
    exact thm_10_8_eventually_upperQuantile_le_of_continuity
      Fs F hconv homega hcont hy
  · constructor
    · intro omega y homega hcont hy
      exact thm_10_8_eventually_le_lowerQuantile_of_continuity
        Fs F hconv homega hcont hy
    · constructor
      · intro omega y homega hcont hy hcobdd
        exact thm_10_8_limsup_upperQuantile_le_of_continuity
          Fs F hconv homega hcont hy hcobdd
      · intro omega y homega hcont hy hcobdd
        exact thm_10_8_le_liminf_lowerQuantile_of_continuity
          Fs F hconv homega hcont hy hcobdd
