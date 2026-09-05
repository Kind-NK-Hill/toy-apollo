/-
TASK ID: def_2_8
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import ProbabilityTheory.chapter_02.def_2_7








open Set MeasureTheory

 
def realOpenIntervals : Set (Set ℝ) :=
  {S | ∃ a b : ℝ, a < b ∧ S = Set.Ioo a b}

 
@[reducible]
def borelAlgebraReal : MeasurableSpace ℝ :=
  generatedSigmaField realOpenIntervals

 
def euclideanOpenBalls (d : ℕ) : Set (Set (EuclideanSpace ℝ (Fin d))) :=
  {S | ∃ c : EuclideanSpace ℝ (Fin d), ∃ r : ℝ, 0 < r ∧ S = Metric.ball c r}

 
@[reducible]
def borelAlgebraEuclidean (d : ℕ) : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
  generatedSigmaField (euclideanOpenBalls d)

theorem borelAlgebraReal_eq_borel :
    borelAlgebraReal = borel ℝ := by
  change MeasurableSpace.generateFrom realOpenIntervals = borel ℝ
  apply le_antisymm
  · refine MeasurableSpace.generateFrom_le ?_
    rintro S ⟨a, b, _hab, rfl⟩
    exact measurableSet_Ioo
  · rw [Real.borel_eq_generateFrom_Ioo_rat]
    refine MeasurableSpace.generateFrom_mono ?_
    intro S hS
    simp only [mem_iUnion, mem_singleton_iff] at hS
    rcases hS with ⟨a, b, hab, rfl⟩
    exact ⟨(a : ℝ), (b : ℝ), by exact_mod_cast hab, rfl⟩

theorem closedInterval_mem_borelAlgebraReal (a b : ℝ) :
    @MeasurableSet ℝ borelAlgebraReal (Set.Icc a b) := by
  rw [borelAlgebraReal_eq_borel]
  exact measurableSet_Icc

theorem leftClosedInfinite_mem_borelAlgebraReal (b : ℝ) :
    @MeasurableSet ℝ borelAlgebraReal (Set.Iic b) := by
  rw [borelAlgebraReal_eq_borel]
  exact measurableSet_Iic

theorem rightClosedInfinite_mem_borelAlgebraReal (a : ℝ) :
    @MeasurableSet ℝ borelAlgebraReal (Set.Ici a) := by
  rw [borelAlgebraReal_eq_borel]
  exact measurableSet_Ici

theorem rightOpenInfinite_mem_borelAlgebraReal (a : ℝ) :
    @MeasurableSet ℝ borelAlgebraReal (Set.Ioi a) := by
  rw [borelAlgebraReal_eq_borel]
  exact measurableSet_Ioi

theorem leftOpenInfinite_mem_borelAlgebraReal (b : ℝ) :
    @MeasurableSet ℝ borelAlgebraReal (Set.Iio b) := by
  rw [borelAlgebraReal_eq_borel]
  exact measurableSet_Iio

theorem leftOpenRightClosed_mem_borelAlgebraReal (a b : ℝ) :
    @MeasurableSet ℝ borelAlgebraReal (Set.Ioc a b) := by
  rw [borelAlgebraReal_eq_borel]
  exact measurableSet_Ioc

theorem leftClosedRightOpen_mem_borelAlgebraReal (a b : ℝ) :
    @MeasurableSet ℝ borelAlgebraReal (Set.Ico a b) := by
  rw [borelAlgebraReal_eq_borel]
  exact measurableSet_Ico



@[reducible]
def def_2_8 : MeasurableSpace ℝ :=
  borelAlgebraReal
