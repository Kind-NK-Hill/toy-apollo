/-
TASK ID: prob_2_2
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_02.def_2_5
import ProbabilityTheory.chapter_02.thm_2_4
import ProbabilityTheory.chapter_02.thm_2_5

open MeasureTheory Set



theorem prob_2_2 {α : Type} [MeasurableSpace α] :
    (∀ (μ : Measure α) (A : ℕ → Set α), (∀ i, MeasurableSet (A i)) → (∀ i, μ (A i) = 0) → μ (⋃ i, A i) = 0) ∧
    (∀ (μ : Measure α) [IsProbabilityMeasure μ] (B : ℕ → Set α), (∀ i, MeasurableSet (B i)) → (∀ i, μ (B i) = 1) → μ (⋂ i, B i) = 1) := by
      constructor;
      · aesop;
      · intro μ hμ B hB hB';
        rw [ MeasureTheory.measure_congr, MeasureTheory.IsProbabilityMeasure.measure_univ ];
        simp_all +decide [ Set.compl_iInter ]
