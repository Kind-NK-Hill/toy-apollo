/-
TASK ID: ex_3_1_4
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.def_3_2
import ToyApollo.Output.thm_3_1
import ToyApollo.Output.ex_3_1_2
import ToyApollo.Output.def_3_3
import ToyApollo.Output.def_3_1
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic

open MeasureTheory Set ENNReal

theorem Example_3_1_2_sigmaFinite : IsSigmaFinite Example_3_1_2 := by
  refine ⟨fun n => Ioc (-(n : ℝ)) n, ?_, ?_, ?_⟩
  · intro n
    exact GeneratedField.basic _ (Or.inl ⟨-(n : ℝ), (n : ℝ), rfl⟩)
  · ext x
    constructor
    · intro _
      simp
    · intro _
      rcases exists_nat_gt |x| with ⟨n, hn⟩
      refine mem_iUnion.mpr ⟨n, ?_⟩
      rw [mem_Ioc]
      constructor
      · have hleft : -(n : ℝ) < -|x| := by linarith
        exact lt_of_lt_of_le hleft (neg_abs_le x)
      · have hright : x ≤ |x| := le_abs_self x
        linarith
  · intro n
    change volume (Ioc (-(n : ℝ)) n) < ⊤
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top

theorem generateFrom_B0_eq_borel : MeasurableSpace.generateFrom B0.carrier = borel ℝ := by
  apply le_antisymm
  · exact MeasurableSpace.generateFrom_le fun s hs => measurable_of_mem_B0 s hs
  · rw [borel_eq_generateFrom_Ioc]
    exact MeasurableSpace.generateFrom_mono fun s hs => by
      rcases hs with ⟨a, b, _, rfl⟩
      exact GeneratedField.basic _ (Or.inl ⟨a, b, rfl⟩)

theorem volume_extends_Example_3_1_2 (s : Set ℝ) (hs : s ∈ B0.carrier) :
    volume s = Example_3_1_2.μ₀ ⟨s, hs⟩ := by
  rfl

theorem borel_measure_extension_unique (μ : Measure ℝ)
    (h : ∀ a b, μ (Ioc a b) = ENNReal.ofReal (b - a)) :
    μ = volume := by
  haveI : IsLocallyFiniteMeasure μ := ⟨by
    intro x
    refine ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
    calc
      μ (Ioo (x - 1) (x + 1)) ≤ μ (Ioc (x - 1) (x + 1)) := measure_mono Ioo_subset_Ioc_self
      _ = ENNReal.ofReal ((x + 1) - (x - 1)) := h (x - 1) (x + 1)
      _ < ⊤ := ENNReal.ofReal_lt_top⟩
  apply Measure.ext_of_Ioc
  intro a b _
  rw [h a b, Real.volume_Ioc]
