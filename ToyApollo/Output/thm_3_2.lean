/-
TASK ID: thm_3_2
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_3_4

open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal Topology

theorem distributionFunction_monotone
    (P : Measure ℝ) [IsProbabilityMeasure P] :
    Monotone (distributionFunction P) := by
  intro x y hxy
  unfold distributionFunction
  exact ENNReal.toReal_mono (measure_ne_top P (Iic y))
    (measure_mono (Iic_subset_Iic.mpr hxy))

noncomputable def thm32RightEndpoint (x : ℝ) (n : ℕ) : ℝ :=
  x + 1 / ((n : ℝ) + 1)

lemma thm32RightEndpoint_antitone (x : ℝ) :
    Antitone (thm32RightEndpoint x) := by
  intro m n hmn
  dsimp [thm32RightEndpoint]
  gcongr

lemma thm32RightEndpoint_tendsto (x : ℝ) :
    Tendsto (thm32RightEndpoint x) atTop (𝓝 x) := by
  change Tendsto (fun n : ℕ => x + 1 / ((n : ℝ) + 1)) atTop (𝓝 x)
  have hconst : Tendsto (fun _ : ℕ => x) atTop (𝓝 x) := tendsto_const_nhds
  simpa only [one_div, add_zero] using
    hconst.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma thm32_iInter_Iic_rightEndpoint (x : ℝ) :
    (⋂ n : ℕ, Iic (thm32RightEndpoint x n)) = Iic x := by
  ext y
  simp only [mem_iInter, mem_Iic]
  constructor
  · intro hy
    exact ge_of_tendsto' (thm32RightEndpoint_tendsto x) hy
  · intro hy n
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    dsimp [thm32RightEndpoint]
    linarith

lemma thm32_tendsto_measure_Iic_rightEndpoint
    (P : Measure ℝ) [IsProbabilityMeasure P] (x : ℝ) :
    Tendsto
      (fun n : ℕ => P (Iic (thm32RightEndpoint x n)))
      atTop (𝓝 (P (Iic x))) := by
  have hsets : Antitone (fun n : ℕ => Iic (thm32RightEndpoint x n)) := by
    intro m n hmn
    exact Iic_subset_Iic.mpr (thm32RightEndpoint_antitone x hmn)
  have h := tendsto_measure_iInter_atTop (μ := P)
    (s := fun n : ℕ => Iic (thm32RightEndpoint x n))
    (fun _ => measurableSet_Iic.nullMeasurableSet) hsets
    ⟨0, measure_ne_top P _⟩
  simpa [Function.comp_def, thm32_iInter_Iic_rightEndpoint x] using h

lemma thm32_tendsto_distributionFunction_rightEndpoint
    (P : Measure ℝ) [IsProbabilityMeasure P] (x : ℝ) :
    Tendsto
      (fun n : ℕ => distributionFunction P (thm32RightEndpoint x n))
      atTop (𝓝 (distributionFunction P x)) := by
  change Tendsto
    (fun n : ℕ => (P (Iic (thm32RightEndpoint x n))).toReal)
    atTop (𝓝 (P (Iic x)).toReal)
  simpa only [Function.comp_def] using
    (ENNReal.tendsto_toReal (measure_ne_top P (Iic x))).comp
      (thm32_tendsto_measure_Iic_rightEndpoint P x)

lemma monotone_continuousWithinAt_Ici_of_tendsto_add_inv_succ
    {g : ℝ → ℝ} (hg : Monotone g) (x : ℝ)
    (hseq : Tendsto
      (fun n : ℕ => g (x + 1 / ((n : ℝ) + 1)))
      atTop (𝓝 (g x))) :
    ContinuousWithinAt g (Ici x) x := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact ha.trans_le (hg hy)
  · intro b hb
    have hevent : ∀ᶠ n : ℕ in atTop,
        g (x + 1 / ((n : ℝ) + 1)) < b :=
      (tendsto_order.1 hseq).2 b hb
    obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
    have hxN : x < x + 1 / ((N : ℝ) + 1) := by
      have hpos : 0 < 1 / ((N : ℝ) + 1) := by positivity
      linarith
    filter_upwards [Ico_mem_nhdsGE hxN] with y hy
    exact (hg hy.2.le).trans_lt (hN N le_rfl)

lemma distributionFunction_right_continuous
    (P : Measure ℝ) [IsProbabilityMeasure P] (x : ℝ) :
    ContinuousWithinAt (distributionFunction P) (Ici x) x := by
  apply monotone_continuousWithinAt_Ici_of_tendsto_add_inv_succ
    (distributionFunction_monotone P) x
  simpa [thm32RightEndpoint] using
    thm32_tendsto_distributionFunction_rightEndpoint P x

lemma distributionFunction_tendsto_atTop
    (P : Measure ℝ) [IsProbabilityMeasure P] :
    Tendsto (distributionFunction P) atTop (𝓝 1) := by
  change Tendsto (fun x : ℝ => (P (Iic x)).toReal) atTop (𝓝 1)
  have h :=
    (ENNReal.tendsto_toReal (measure_ne_top P univ)).comp
      (tendsto_measure_Iic_atTop P)
  simpa only [Function.comp_def, IsProbabilityMeasure.measure_univ,
    ENNReal.toReal_one] using h

lemma distributionFunction_tendsto_atBot
    (P : Measure ℝ) [IsProbabilityMeasure P] :
    Tendsto (distributionFunction P) atBot (𝓝 0) := by
  have hInter : (⋂ x : ℝ, Iic x) = ∅ := by
    rw [iInter_Iic_eq_empty_iff, not_bddBelow_iff]
    intro x
    refine ⟨x - 1, ?_, by linarith⟩
    exact ⟨x - 1, rfl⟩
  have hmeasure : Tendsto (fun x : ℝ => P (Iic x)) atBot (𝓝 0) := by
    have h := tendsto_measure_iInter_atBot (μ := P)
      (s := fun x : ℝ => Iic x)
      (fun _ => measurableSet_Iic.nullMeasurableSet) monotone_Iic
      ⟨0, measure_ne_top P _⟩
    simpa [Function.comp_def, hInter] using h
  change Tendsto (fun x : ℝ => (P (Iic x)).toReal) atBot (𝓝 0)
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hmeasure

theorem thm_3_2 (P : Measure ℝ) [IsProbabilityMeasure P] :
    Monotone (distributionFunction P) ∧
    (∀ x, ContinuousWithinAt (distributionFunction P) (Ici x) x) ∧
    Tendsto (distributionFunction P) atTop (𝓝 1) ∧
    Tendsto (distributionFunction P) atBot (𝓝 0) :=
  ⟨distributionFunction_monotone P,
    distributionFunction_right_continuous P,
    distributionFunction_tendsto_atTop P,
    distributionFunction_tendsto_atBot P⟩
