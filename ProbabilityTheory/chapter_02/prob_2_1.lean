/-
TASK ID: prob_2_1
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_02.def_2_5

open MeasureTheory Set Function

theorem prob_2_1 (α : Type _) [MeasurableSpace α] (μ : Set α → ENNReal) :
    ((∀ (f : ℕ → Set α), (∀ i, MeasurableSet (f i)) → Pairwise (Disjoint on f) → μ (⋃ i, f i) = ∑' i, μ (f i)) ∧
      ∃ A, MeasurableSet A ∧ μ A < ⊤) ↔
    ∃ (μ' : Measure α), ∀ s, MeasurableSet s → μ' s = μ s := by
  constructor
  · rintro ⟨hσ, A, hA_meas, hA_fin⟩
    have h_empty : μ ∅ = 0 := by
      contrapose! hσ;
      refine' ⟨ fun i => if i = 0 then A else ∅, _, _, _ ⟩ <;> simp_all +decide [ Pairwise ];
      · aesop;
      · intro i j hij; by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp_all +decide [ Set.disjoint_left ] ;
      · rw [ show ( ⋃ i : ℕ, if i = 0 then A else ∅ ) = A by ext x; aesop ];
        rw [ ENNReal.tsum_eq_iSup_nat ];
        refine' ne_of_lt ( lt_of_lt_of_le _ ( le_ciSup _ 2 ) );
        · simp +decide [ Finset.sum_range_succ ];
          exact ENNReal.lt_add_right hA_fin.ne hσ;
        · simp +decide
    refine ⟨Measure.ofMeasurable (fun s _ => μ s) h_empty (fun f hf hd => hσ f hf hd), ?_⟩
    intro s hs
    exact Measure.ofMeasurable_apply s hs
  · rintro ⟨μ', hμ'⟩
    constructor
    · intro f hf hd
      rw [← hμ' _ (MeasurableSet.iUnion hf)]
      simp_rw [← hμ' _ (hf _)]
      exact μ'.m_iUnion hf hd
    · exact ⟨∅, MeasurableSet.empty, by rw [← hμ' ∅ MeasurableSet.empty, measure_empty]; exact ENNReal.zero_lt_top⟩
