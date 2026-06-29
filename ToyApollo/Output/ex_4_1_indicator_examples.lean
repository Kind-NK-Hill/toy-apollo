/-
TASK ID: ex_4_1_indicator_examples
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.ex_4_2_lebesgue_borel
import ToyApollo.Output.thm_4_1

open MeasureTheory Set

def rationalSet : Set ℝ := ((↑) : ℚ → ℝ) '' univ

theorem rationalSet_countable : rationalSet.Countable := by
  simpa [rationalSet] using Set.Countable.image Set.countable_univ ((↑) : ℚ → ℝ)

theorem rationalSet_measurable : MeasurableSet rationalSet := by
  exact rationalSet_countable.measurableSet

theorem measurable_indicator_rationalSet :
    Measurable (Set.indicator rationalSet (fun _ => (1 : ℝ))) := by
  exact (thm_4_1 rationalSet).2 rationalSet_measurable

theorem measurable_indicator_cantorSet :
    Measurable (Set.indicator cantorSet (fun _ => (1 : ℝ))) := by
  exact (thm_4_1 cantorSet).2 isClosed_cantorSet.measurableSet

open Classical in

noncomputable def nonBorelIndicatorWitness : Set ℝ :=
  Classical.choose ex_4_2_lebesgue_borel

theorem nonBorelIndicatorWitness_not_measurableSet :
    ¬ MeasurableSet nonBorelIndicatorWitness := by
  have h := Classical.choose_spec ex_4_2_lebesgue_borel
  exact h.2.2.2.1

theorem not_measurable_indicator_nonBorelIndicatorWitness :
    ¬ Measurable (Set.indicator nonBorelIndicatorWitness (fun _ => (1 : ℝ))) := by
  intro h
  exact nonBorelIndicatorWitness_not_measurableSet ((thm_4_1 nonBorelIndicatorWitness).1 h)

theorem ex_4_1_indicator_examples :
    Measurable (Set.indicator rationalSet (fun _ => (1 : ℝ))) ∧
      Measurable (Set.indicator cantorSet (fun _ => (1 : ℝ))) ∧
      ¬ Measurable (Set.indicator nonBorelIndicatorWitness (fun _ => (1 : ℝ))) := by
  exact ⟨measurable_indicator_rationalSet, measurable_indicator_cantorSet,
    not_measurable_indicator_nonBorelIndicatorWitness⟩
