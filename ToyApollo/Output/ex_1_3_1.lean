/-
TASK ID: ex_1_3_1
TYPE: Example_Proof
SOURCE PLAN: 38_chap1_riemann_stieltjes
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.rs_stieltjes_step_support

open MeasureTheory intervalIntegral Set Filter

noncomputable section

def singleJumpStep (c u₁ u₂ : ℝ) : ℝ → ℝ :=
  fun x => if x < c then u₁ else u₂

theorem singleJumpStep_monotone {c u₁ u₂ : ℝ} (hu : u₁ ≤ u₂) :
    Monotone (singleJumpStep c u₁ u₂) := by
  intro x y hxy
  by_cases hy : y < c
  · have hx : x < c := lt_of_le_of_lt hxy hy
    simp [singleJumpStep, hx, hy]
  · by_cases hx : x < c
    · simp [singleJumpStep, hx, hy, hu]
    · simp [singleJumpStep, hx, hy]

theorem singleJumpStep_rightLim_eq {c u₁ u₂ x : ℝ} :
    Function.rightLim (singleJumpStep c u₁ u₂) x = singleJumpStep c u₁ u₂ x := by
  by_cases hx : x < c
  · have hnhds : nhdsWithin x (Ioi x) ≠ ⊥ := (inferInstance : NeBot (nhdsWithin x (Ioi x))).ne
    have htendsto : Tendsto (singleJumpStep c u₁ u₂) (nhdsWithin x (Ioi x)) (nhds u₁) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioc_mem_nhdsGT (show x < (x + c) / 2 by nlinarith [hx])] with y hy
      have hyc : y < c := by
        nlinarith [hy.2, hx]
      simp [singleJumpStep, hyc]
    simpa [singleJumpStep, hx] using rightLim_eq_of_tendsto hnhds htendsto
  · have hxc : c ≤ x := le_of_not_gt hx
    have hnhds : nhdsWithin x (Ioi x) ≠ ⊥ := (inferInstance : NeBot (nhdsWithin x (Ioi x))).ne
    have htendsto : Tendsto (singleJumpStep c u₁ u₂) (nhdsWithin x (Ioi x)) (nhds u₂) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioc_mem_nhdsGT (show x < x + 1 by linarith)] with y hy
      have hcy : ¬ y < c := not_lt.mpr (hxc.trans (le_of_lt hy.1))
      simp [singleJumpStep, hcy]
    simpa [singleJumpStep, hx] using rightLim_eq_of_tendsto hnhds htendsto

theorem singleJumpStep_measure_eq {c u₁ u₂ : ℝ} (hu : u₁ ≤ u₂) :
    rsMeasureLocal (singleJumpStep c u₁ u₂) (singleJumpStep_monotone hu)
      = ENNReal.ofReal (u₂ - u₁) • Measure.dirac c := by
  let hmono : Monotone (singleJumpStep c u₁ u₂) := singleJumpStep_monotone hu
  have hsf : ∀ x, hmono.stieltjesFunction x = singleJumpStep c u₁ u₂ x := by
    intro x
    rw [Monotone.stieltjesFunction_eq]
    exact singleJumpStep_rightLim_eq
  refine Measure.ext_of_Ioc'
      (rsMeasureLocal (singleJumpStep c u₁ u₂) hmono)
      (ENNReal.ofReal (u₂ - u₁) • Measure.dirac c)
      (fun a b hab => by
        rw [rsMeasureLocal, StieltjesFunction.measure_Ioc]
        exact ENNReal.ofReal_ne_top)
      ?_
  intro a b hab
  rw [rsMeasureLocal, StieltjesFunction.measure_Ioc]
  rw [Measure.smul_apply, Measure.dirac_apply]
  rw [hsf a, hsf b]
  by_cases hca : c ≤ a
  · have hna : ¬ a < c := not_lt.mpr hca
    have hnb : ¬ b < c := by
      exact not_lt.mpr (hca.trans (le_of_lt hab))
    have hnotmem : c ∉ Ioc a b := by
      simp [hca]
    simp [singleJumpStep, hna, hnb, hnotmem]
  · by_cases hbc : b < c
    · have hna : ¬ c ∈ Ioc a b := by
        simp [hbc, hbc.not_ge]
      simp [singleJumpStep, hbc, lt_trans hab hbc, hna]
    · have hac : a < c := lt_of_not_ge hca
      have hcb : c ≤ b := le_of_not_gt hbc
      have hmem : c ∈ Ioc a b := ⟨hac, hcb⟩
      have hnb : ¬ b < c := hbc
      simp [singleJumpStep, hac, hnb, hmem]

theorem ex_1_3_1 {f : ℝ → ℝ} {a b c u₁ u₂ : ℝ}
    (hab : a ≤ b)
    (hac : a < c)
    (hcb : c ≤ b)
    (hu : u₁ < u₂)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hcont : ContinuousAt f c) :
    ∃ hRS : RSIntegrable f (singleJumpStep c u₁ u₂) a b,
      rsIntegral f (singleJumpStep c u₁ u₂) a b hRS = f c * (u₂ - u₁) := by
  change
    ∃ hRS : RSIntegrable f (fun x => if x < c then u₁ else u₂) a b,
      rsIntegral f (fun x => if x < c then u₁ else u₂) a b hRS = f c * (u₂ - u₁)
  exact rsIntegral_singleJumpStep_exists (f := f) (a := a) (b := b) (c := c)
    (u₁ := u₁) (u₂ := u₂) hab hac hcb hu hAbove hBelow hcont
