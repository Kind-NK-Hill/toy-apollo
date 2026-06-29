import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.OfDigits
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Measure.Dirac
import ToyApollo.Output.ex_4_2_lebesgue_borel

open MeasureTheory Set
open scoped ENNReal

/-!
# Example 3.3.6: Cantor Distribution

We realize the Cantor distribution as the pushforward of the fair-coin product measure on
`ℕ → Bool` under the usual ternary `0/2` coding map. This gives a concrete singular continuous
distribution: all mass is concentrated on the Cantor set, the Cantor set has Lebesgue measure
zero, and every singleton has probability zero.
-/

/-- The fair Bernoulli measure on `Bool`. -/
noncomputable def fairCoin : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac false + (1 / 2 : ℝ≥0∞) • Measure.dirac true

@[simp] theorem fairCoin_apply_singleton (b : Bool) : fairCoin {b} = (1 / 2 : ℝ≥0∞) := by
  cases b <;> simp [fairCoin]

instance : IsProbabilityMeasure fairCoin := by
  refine ⟨by simpa [fairCoin] using ENNReal.inv_two_add_inv_two⟩

/-- The ternary `0/2` encoding of an infinite binary sequence. -/
noncomputable def cantorCode (f : ℕ → Bool) : ℝ :=
  Real.ofDigits (fun i ↦ cond (f i) (2 : Fin 3) 0)

lemma cantorCode_mem_cantorSet (f : ℕ → Bool) : cantorCode f ∈ cantorSet := by
  simpa [cantorCode] using ofDigits_bool_to_fin_three_mem_cantorSet f

theorem cantorCode_injective : Function.Injective cantorCode := by
  intro f g hfg
  have hdigits :
      (fun i ↦ cond (f i) (2 : Fin 3) 0) = fun i ↦ cond (g i) (2 : Fin 3) 0 := by
    apply ofDigits_zero_two_sequence_unique
    · intro i
      cases f i <;> simp
    · intro i
      cases g i <;> simp
    · simpa [cantorCode] using hfg
  funext i
  have hi := congrFun hdigits i
  cases hf : f i <;> cases hg : g i <;> simp [hf, hg] at hi ⊢

lemma measurable_cantorCode : Measurable cantorCode := by
  let digit : Bool → Fin 3 := fun b ↦ cond b 2 0
  have hdigit : Continuous digit := by fun_prop
  have hdigits : Continuous fun f : ℕ → Bool => fun i ↦ digit (f i) := by
    refine continuous_pi ?_
    intro i
    exact hdigit.comp (continuous_apply i)
  simpa [cantorCode, digit] using (Continuous.comp Real.continuous_ofDigits hdigits).measurable

/-- The fair-coin product measure on binary sequences. -/
noncomputable def cantorSequenceMeasure : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => fairCoin

instance : IsProbabilityMeasure cantorSequenceMeasure := by
  dsimp [cantorSequenceMeasure]
  infer_instance

/-- The Cantor distribution obtained by pushing the fair-coin product measure to `ℝ`. -/
noncomputable def cantorDistribution : Measure ℝ :=
  cantorSequenceMeasure.map cantorCode

instance : IsProbabilityMeasure cantorDistribution := by
  exact Measure.isProbabilityMeasure_map measurable_cantorCode.aemeasurable

theorem cantorDistribution_univ : cantorDistribution univ = 1 := by
  simpa using (measure_univ : cantorDistribution univ = 1)

theorem cantorDistribution_cantorSet_eq_one : cantorDistribution cantorSet = 1 := by
  rw [cantorDistribution, Measure.map_apply measurable_cantorCode isClosed_cantorSet.measurableSet]
  have hpre : cantorCode ⁻¹' cantorSet = univ := by
    ext f
    simp [cantorCode_mem_cantorSet]
  rw [hpre, measure_univ]

lemma tprod_half_eq_zero : (∏' _ : ℕ, (1 / 2 : ℝ≥0∞)) = 0 := by
  have hle : ∀ n : ℕ, (∏' _ : ℕ, (1 / 2 : ℝ≥0∞)) ≤
      ∏ i ∈ Finset.range n, (1 / 2 : ℝ≥0∞) := by
    intro n
    rw [ENNReal.tprod_eq_iInf_prod (by intro i; norm_num)]
    exact iInf_le (fun s : Finset ℕ => ∏ i ∈ s, (1 / 2 : ℝ≥0∞)) (Finset.range n)
  have hzero : Filter.Tendsto (fun n : ℕ => ∏ i ∈ Finset.range n, (1 / 2 : ℝ≥0∞))
      Filter.atTop (nhds 0) := by
    simpa using
      ENNReal.tendsto_ofReal
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1))
  exact le_antisymm
    (le_of_tendsto_of_tendsto' tendsto_const_nhds hzero hle)
    bot_le

theorem cantorSequenceMeasure_singleton_eq_zero (f : ℕ → Bool) :
    cantorSequenceMeasure {f} = 0 := by
  rw [cantorSequenceMeasure, Measure.infinitePi_singleton]
  rw [show (∏' i : ℕ, fairCoin {f i}) = (∏' _ : ℕ, (1 / 2 : ℝ≥0∞)) by
    congr with i
    simp [fairCoin_apply_singleton]]
  exact tprod_half_eq_zero

theorem cantorDistribution_singleton_eq_zero (x : ℝ) : cantorDistribution {x} = 0 := by
  by_cases hx : ∃ f : ℕ → Bool, cantorCode f = x
  · rcases hx with ⟨f, rfl⟩
    rw [cantorDistribution, Measure.map_apply measurable_cantorCode (measurableSet_singleton _)]
    have hpre : cantorCode ⁻¹' {cantorCode f} = {f} := by
      ext g
      constructor
      · intro hg
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hg
        exact cantorCode_injective hg
      · intro hg
        simp at hg
        simpa [hg]
    rw [hpre, cantorSequenceMeasure_singleton_eq_zero]
  · rw [cantorDistribution, Measure.map_apply measurable_cantorCode (measurableSet_singleton _)]
    have hpre : cantorCode ⁻¹' {x} = ∅ := by
      ext f
      constructor
      · intro hfx
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hfx
        exact False.elim (hx ⟨f, hfx⟩)
      · intro hfalse
        simp at hfalse
    rw [hpre, measure_empty]

/-- The Cantor distribution is singular and continuous: it is concentrated on a Lebesgue-null
Cantor set, and it has no atoms. -/
theorem ex_3_3_6 :
    ∃ C : Set ℝ, MeasurableSet C ∧ volume C = 0 ∧ cantorDistribution C = 1 ∧
      (∀ x : ℝ, cantorDistribution {x} = 0) := by
  refine ⟨cantorSet, isClosed_cantorSet.measurableSet, volume_cantorSet_eq_zero,
    cantorDistribution_cantorSet_eq_one, cantorDistribution_singleton_eq_zero⟩
