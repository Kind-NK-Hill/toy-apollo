/-
TASK ID: prob_6_6
TYPE: Problem
SOURCE PLAN: 24_chap6_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Filter Topology

theorem prob_6_6 (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) :
    Tendsto (fun (n : ℕ) => ∫ ω in {ω | (n : ℝ) ≤ |X ω|}, X ω ∂P) atTop (𝓝 0) := by
  convert hX.tendsto_setIntegral_nhds_zero;
  rotate_left;
  exact ℕ;
  exact Filter.atTop;
  exact fun n => { ω | (n : ℝ) ≤ |X ω| };
  refine' ⟨fun h => fun _ => h, fun h => h _⟩;
  convert MeasureTheory.tendsto_measure_iInter_atTop _ _ _;
  · rw [show (⋂ n : ℕ, {ω : Ω | (n : ℝ) ≤ |X ω|}) = ∅ from
        Set.eq_empty_iff_forall_notMem.2 fun ω hω => by
          rcases exists_nat_gt (|X ω|) with ⟨n, hn⟩
          exact not_lt_of_ge (Set.mem_iInter.1 hω n) hn]
    norm_num
  · infer_instance
  · intro n
    exact hX.1.norm.aemeasurable.nullMeasurable measurableSet_Ici
  · exact fun n m hnm => Set.setOf_subset_setOf.2 fun ω hω => le_trans (mod_cast hnm) hω
  · exact ⟨0, ne_of_lt (MeasureTheory.measure_lt_top _ _)⟩
