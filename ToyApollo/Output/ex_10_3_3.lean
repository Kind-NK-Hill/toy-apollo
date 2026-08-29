/-
TASK ID: ex_10_3_3
TYPE: Example_Proof
SOURCE PLAN: chapter10-distribution-total-variation
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_10_2
import ToyApollo.Output.def_10_4

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set
open scoped ENNReal Topology

abbrev ex_10_3_3_SampleSpace := Bool × Bool

lemma ex_10_3_3_quarter_add_quarter : (4⁻¹ : ENNReal) + 4⁻¹ = 2⁻¹ := by
  change ((↑(4 : NNReal) : ENNReal)⁻¹ + (↑(4 : NNReal) : ENNReal)⁻¹ =
    (↑(2 : NNReal) : ENNReal)⁻¹)
  rw [← ENNReal.coe_inv' (r := (4 : NNReal))]
  rw [← ENNReal.coe_inv' (r := (2 : NNReal))]
  change (↑(((4 : NNReal)⁻¹ + (4 : NNReal)⁻¹)) : ENNReal) =
    ↑((2 : NNReal)⁻¹)
  congr
  exact NNReal.eq (by norm_num)

lemma ex_10_3_3_half_add_quarter_add_quarter :
    (2⁻¹ : ENNReal) + 4⁻¹ + 4⁻¹ = 2⁻¹ + 2⁻¹ := by
  rw [add_assoc, ex_10_3_3_quarter_add_quarter]

noncomputable def ex_10_3_3_mu : Measure ex_10_3_3_SampleSpace :=
  (1 / 4 : ENNReal) • Measure.dirac (true, true) +
  (1 / 4 : ENNReal) • Measure.dirac (true, false) +
  (1 / 4 : ENNReal) • Measure.dirac (false, true) +
  (1 / 4 : ENNReal) • Measure.dirac (false, false)

noncomputable instance ex_10_3_3_mu_isProbabilityMeasure :
    IsProbabilityMeasure ex_10_3_3_mu := by
  refine ⟨?_⟩
  simp [ex_10_3_3_mu, ex_10_3_3_quarter_add_quarter,
    ex_10_3_3_half_add_quarter_add_quarter]
  change ((↑(2 : NNReal) : ENNReal)⁻¹ + (↑(2 : NNReal) : ENNReal)⁻¹ =
    ↑(1 : NNReal))
  rw [← ENNReal.coe_inv' (r := (2 : NNReal))]
  change (↑(((2 : NNReal)⁻¹ + (2 : NNReal)⁻¹)) : ENNReal) = ↑(1 : NNReal)
  congr
  exact NNReal.eq (by norm_num)

def ex_10_3_3_X (ω : ex_10_3_3_SampleSpace) : ℝ :=
  if ω.1 then 1 else 0

def ex_10_3_3_Y (ω : ex_10_3_3_SampleSpace) : ℝ :=
  if ω.2 then 1 else 0

def ex_10_3_3_Xseq (_ : ℕ) : ex_10_3_3_SampleSpace → ℝ :=
  ex_10_3_3_X

noncomputable def ex_10_3_3_bernoulliHalf : Measure ℝ :=
  (1 / 2 : ENNReal) • Measure.dirac (1 : ℝ) +
  (1 / 2 : ENNReal) • Measure.dirac (0 : ℝ)

theorem ex_10_3_3_joint_atom_probability (a b : Bool) :
    ex_10_3_3_mu {ω : ex_10_3_3_SampleSpace | ω.1 = a ∧ ω.2 = b} =
      (1 / 4 : ENNReal) := by
  cases a <;> cases b <;> simp [ex_10_3_3_mu]

theorem ex_10_3_3_X_atom_probability (a : Bool) :
    ex_10_3_3_mu {ω : ex_10_3_3_SampleSpace | ω.1 = a} =
      (1 / 2 : ENNReal) := by
  cases a <;> simp [ex_10_3_3_mu, ex_10_3_3_quarter_add_quarter]

theorem ex_10_3_3_Y_atom_probability (b : Bool) :
    ex_10_3_3_mu {ω : ex_10_3_3_SampleSpace | ω.2 = b} =
      (1 / 2 : ENNReal) := by
  cases b <;> simp [ex_10_3_3_mu, ex_10_3_3_quarter_add_quarter]

theorem ex_10_3_3_X_law :
    Measure.map ex_10_3_3_X ex_10_3_3_mu = ex_10_3_3_bernoulliHalf := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (by measurability : Measurable ex_10_3_3_X) hs]
  simp only [ex_10_3_3_mu, ex_10_3_3_bernoulliHalf, Measure.add_apply,
    Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  unfold ex_10_3_3_X
  simp [Set.indicator]
  by_cases h0 : (0 : ℝ) ∈ s <;> by_cases h1 : (1 : ℝ) ∈ s <;>
    simp [h0, h1, ex_10_3_3_quarter_add_quarter,
      ex_10_3_3_half_add_quarter_add_quarter]

theorem ex_10_3_3_Y_law :
    Measure.map ex_10_3_3_Y ex_10_3_3_mu = ex_10_3_3_bernoulliHalf := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (by measurability : Measurable ex_10_3_3_Y) hs]
  simp only [ex_10_3_3_mu, ex_10_3_3_bernoulliHalf, Measure.add_apply,
    Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  unfold ex_10_3_3_Y
  simp [Set.indicator]
  by_cases h0 : (0 : ℝ) ∈ s <;> by_cases h1 : (1 : ℝ) ∈ s <;>
    simp [h0, h1, ex_10_3_3_quarter_add_quarter,
      ex_10_3_3_half_add_quarter_add_quarter]

theorem ex_10_3_3_equal_law :
    Measure.map ex_10_3_3_X ex_10_3_3_mu =
      Measure.map ex_10_3_3_Y ex_10_3_3_mu := by
  rw [ex_10_3_3_X_law, ex_10_3_3_Y_law]

theorem ex_10_3_3_unit_gap_probability (n : ℕ) :
    ex_10_3_3_mu
        {ω : ex_10_3_3_SampleSpace | |ex_10_3_3_Xseq n ω - ex_10_3_3_Y ω| = 1} =
      (1 / 2 : ENNReal) := by
  simp [ex_10_3_3_mu, ex_10_3_3_Xseq, ex_10_3_3_X, ex_10_3_3_Y,
    ex_10_3_3_quarter_add_quarter]

theorem ex_10_3_3_separation_probability (n : ℕ) :
    ex_10_3_3_mu
        (deviationEvent ex_10_3_3_Xseq ex_10_3_3_Y n ((99 : ℝ) / 100)) =
      (1 / 2 : ENNReal) := by
  simp [deviationEvent, ex_10_3_3_mu, ex_10_3_3_Xseq, ex_10_3_3_X,
    ex_10_3_3_Y, Set.indicator]
  norm_num
  exact ex_10_3_3_quarter_add_quarter

theorem ex_10_3_3_converges_in_distribution :
    RandomVariablesConvergeInDistribution
      (fun _ : ℕ => ex_10_3_3_mu) ex_10_3_3_Xseq
      ex_10_3_3_mu ex_10_3_3_Y := by
  refine MeasureTheory.tendstoInDistribution_of_identDistrib 0 (fun n => ?_) ?_
  · refine ⟨by fun_prop, by fun_prop, ?_⟩
    simp [ex_10_3_3_Xseq]
  · refine ⟨by fun_prop, by fun_prop, ?_⟩
    simpa [ex_10_3_3_Xseq] using ex_10_3_3_equal_law

theorem ex_10_3_3_not_converges_in_probability :
    ¬ ConvergesInProbability ex_10_3_3_mu ex_10_3_3_Xseq ex_10_3_3_Y := by
  intro hprob
  have hε : (0 : ℝ) < (99 : ℝ) / 100 := by norm_num
  have hzero := hprob.2.2 ((99 : ℝ) / 100) hε
  have hconst :
      Tendsto
        (fun n : ℕ =>
          ex_10_3_3_mu
            (deviationEvent ex_10_3_3_Xseq ex_10_3_3_Y n ((99 : ℝ) / 100)))
        atTop (nhds (1 / 2 : ENNReal)) := by
    simpa [ex_10_3_3_separation_probability] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 / 2 : ENNReal)) atTop (nhds (1 / 2 : ENNReal)))
  have huniq := tendsto_nhds_unique hzero hconst
  have hne : (1 / 2 : ENNReal) ≠ 0 := by norm_num
  exact hne huniq.symm

theorem ex_10_3_3 :
    RandomVariablesConvergeInDistribution
      (fun _ : ℕ => ex_10_3_3_mu) ex_10_3_3_Xseq
        ex_10_3_3_mu ex_10_3_3_Y ∧
      ¬ ConvergesInProbability ex_10_3_3_mu ex_10_3_3_Xseq ex_10_3_3_Y := by
  exact ⟨ex_10_3_3_converges_in_distribution,
    ex_10_3_3_not_converges_in_probability⟩
