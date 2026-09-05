/-
TASK ID: thm_2_7
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Tactic
import ProbabilityTheory.chapter_02.def_2_8








-- WRITE FINAL LEAN CODE BELOW

open Set MeasureTheory

 
def realStrictClosedIntervals : Set (Set ℝ) :=
  {S | ∃ a b : ℝ, a < b ∧ Set.Icc a b = S}



def thm_2_7_closedApprox (a b : ℝ) (n : ℕ) : Set ℝ :=
  let δ : ℝ := 1 / ((n : ℝ) + 1)
  if _h : a + δ < b - δ then Set.Icc (a + δ) (b - δ) else ∅

theorem thm_2_7_closedApprox_mem_generateFrom_strictClosed
    (a b : ℝ) (n : ℕ) :
    @MeasurableSet ℝ (MeasurableSpace.generateFrom realStrictClosedIntervals)
      (thm_2_7_closedApprox a b n) := by
  dsimp [thm_2_7_closedApprox]
  split_ifs with h
  · exact MeasurableSpace.measurableSet_generateFrom
      (show Set.Icc (a + 1 / ((n : ℝ) + 1)) (b - 1 / ((n : ℝ) + 1)) ∈
          realStrictClosedIntervals from
        ⟨a + 1 / ((n : ℝ) + 1), b - 1 / ((n : ℝ) + 1), h, rfl⟩)
  · exact @MeasurableSet.empty ℝ
      (MeasurableSpace.generateFrom realStrictClosedIntervals)

theorem thm_2_7_iUnion_closedApprox_eq_Ioo {a b : ℝ} (_hab : a < b) :
    (⋃ n : ℕ, thm_2_7_closedApprox a b n) = Set.Ioo a b := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
    dsimp [thm_2_7_closedApprox] at hn
    split_ifs at hn with hstrict
    · have hδpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      exact ⟨by linarith [hn.1], by linarith [hn.2]⟩
    · simp at hn

  · intro hx
    have hleft_pos : 0 < x - a := by linarith [hx.1]
    have hright_pos : 0 < b - x := by linarith [hx.2]
    have hmin_pos : 0 < min (x - a) (b - x) := lt_min hleft_pos hright_pos
    rcases exists_nat_one_div_lt hmin_pos with ⟨n, hn⟩
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    have hn_left : 1 / ((n : ℝ) + 1) < x - a :=
      lt_of_lt_of_le hn (min_le_left _ _)
    have hn_right : 1 / ((n : ℝ) + 1) < b - x :=
      lt_of_lt_of_le hn (min_le_right _ _)
    have hstrict :
        a + 1 / ((n : ℝ) + 1) < b - 1 / ((n : ℝ) + 1) := by
      linarith
    dsimp [thm_2_7_closedApprox]
    simpa [hstrict] using
      (show
          a + 1 / ((n : ℝ) + 1) < b - 1 / ((n : ℝ) + 1) ∧
            a + 1 / ((n : ℝ) + 1) ≤ x ∧
              x ≤ b - 1 / ((n : ℝ) + 1) from
        ⟨hstrict, by linarith, by linarith⟩)

theorem thm_2_7_closedIntervals_borel_inclusion :
    MeasurableSpace.generateFrom realStrictClosedIntervals ≤ borelAlgebraReal := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro S ⟨a, b, _hab, rfl⟩
  exact closedInterval_mem_borelAlgebraReal a b

theorem thm_2_7_openInterval_mem_generateFrom_strictClosed
    {a b : ℝ} (hab : a < b) :
    @MeasurableSet ℝ (MeasurableSpace.generateFrom realStrictClosedIntervals)
      (Set.Ioo a b) := by
  rw [← thm_2_7_iUnion_closedApprox_eq_Ioo hab]
  exact MeasurableSet.iUnion
    (fun n => thm_2_7_closedApprox_mem_generateFrom_strictClosed a b n)

theorem thm_2_7_borelAlgebraReal_le_generateFrom_strictClosed :
    borelAlgebraReal ≤ MeasurableSpace.generateFrom realStrictClosedIntervals := by
  change MeasurableSpace.generateFrom realOpenIntervals ≤
    MeasurableSpace.generateFrom realStrictClosedIntervals
  refine MeasurableSpace.generateFrom_le ?_
  rintro S ⟨a, b, hab, rfl⟩
  exact thm_2_7_openInterval_mem_generateFrom_strictClosed hab



theorem thm_2_7 :
    MeasurableSpace.generateFrom realStrictClosedIntervals = borelAlgebraReal :=
  le_antisymm thm_2_7_closedIntervals_borel_inclusion
    thm_2_7_borelAlgebraReal_le_generateFrom_strictClosed



theorem thm_2_7_mathlib_borel :
    MeasurableSpace.generateFrom realStrictClosedIntervals = borel ℝ := by
  rw [thm_2_7, borelAlgebraReal_eq_borel]
