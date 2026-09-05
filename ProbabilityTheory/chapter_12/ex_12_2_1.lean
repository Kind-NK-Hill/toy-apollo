/-
TASK ID: ex_12_2_1
TYPE: Example_Proof
SOURCE PLAN: chapter12-closed-subspace-projection
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_12.ex_12_1_2




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory
open Filter

open scoped BigOperators InnerProductSpace Topology symmDiff

noncomputable section



local instance : IsProbabilityMeasure ex_12_1_2_measure where
  measure_univ := ex_12_1_2_measure_univ

 
abbrev ex_12_2_1_L2 :=
  ex_12_1_2_space →₂[ex_12_1_2_measure] ℂ

 
def ex_12_2_1_initialSet (k : ℕ) : Set ex_12_1_2_space :=
  ↑(Finset.range k)

theorem ex_12_2_1_initialSet_measurable (k : ℕ) :
    MeasurableSet (ex_12_2_1_initialSet k) := by
  exact (Finset.range k).measurableSet

 
def ex_12_2_1_partialOnes (k : ℕ) : ex_12_1_2_space → ℂ :=
  (ex_12_2_1_initialSet k).indicator (fun _ => 1)

@[simp]
theorem ex_12_2_1_partialOnes_apply (k n : ℕ) :
    ex_12_2_1_partialOnes k n = if n < k then 1 else 0 := by
  by_cases hn : n < k
  · simp [ex_12_2_1_partialOnes, ex_12_2_1_initialSet, hn]
  · simp [ex_12_2_1_partialOnes, ex_12_2_1_initialSet, hn]

 
def ex_12_2_1_allOnes : ex_12_1_2_space → ℂ :=
  (Set.univ : Set ex_12_1_2_space).indicator (fun _ => 1)

@[simp]
theorem ex_12_2_1_allOnes_apply (n : ex_12_1_2_space) :
    ex_12_2_1_allOnes n = 1 := by
  simp [ex_12_2_1_allOnes]

 
theorem ex_12_2_1_partialOnes_memLp (k : ℕ) :
    MemLp (ex_12_2_1_partialOnes k) (2 : ENNReal)
      ex_12_1_2_measure := by
  simpa [ex_12_2_1_partialOnes] using
    (memLp_const (μ := ex_12_1_2_measure) (p := (2 : ENNReal)) (1 : ℂ)).indicator
      (ex_12_2_1_initialSet_measurable k)

 
theorem ex_12_2_1_allOnes_memLp :
    MemLp ex_12_2_1_allOnes (2 : ENNReal) ex_12_1_2_measure := by
  simpa [ex_12_2_1_allOnes] using
    (memLp_const (μ := ex_12_1_2_measure) (p := (2 : ENNReal)) (1 : ℂ)).indicator
      MeasurableSet.univ

 
noncomputable def ex_12_2_1_partialOnesLp (k : ℕ) : ex_12_2_1_L2 :=
  (ex_12_2_1_partialOnes_memLp k).toLp (ex_12_2_1_partialOnes k)

 
noncomputable def ex_12_2_1_allOnesLp : ex_12_2_1_L2 :=
  ex_12_2_1_allOnes_memLp.toLp ex_12_2_1_allOnes

theorem ex_12_2_1_partialOnesLp_eq_indicatorConstLp (k : ℕ) :
    ex_12_2_1_partialOnesLp k =
      indicatorConstLp (μ := ex_12_1_2_measure) 2
        (ex_12_2_1_initialSet_measurable k) (by finiteness) (1 : ℂ) := by
  unfold ex_12_2_1_partialOnesLp ex_12_2_1_partialOnes indicatorConstLp
  rfl

theorem ex_12_2_1_allOnesLp_eq_indicatorConstLp :
    ex_12_2_1_allOnesLp =
      indicatorConstLp (μ := ex_12_1_2_measure) 2
        MeasurableSet.univ (by finiteness) (1 : ℂ) := by
  unfold ex_12_2_1_allOnesLp ex_12_2_1_allOnes indicatorConstLp
  rfl

 
noncomputable def ex_12_2_1_coordinateLp (n : ℕ) : ex_12_2_1_L2 :=
  indicatorConstLp (μ := ex_12_1_2_measure) 2
    (measurableSet_singleton n) (by finiteness) (1 : ℂ)



noncomputable def ex_12_2_1_W : Submodule ℂ ex_12_2_1_L2 :=
  Submodule.span ℂ (Set.range ex_12_2_1_coordinateLp)

theorem ex_12_2_1_zero_mem :
    (0 : ex_12_2_1_L2) ∈ ex_12_2_1_W :=
  (ex_12_2_1_W).zero_mem

theorem ex_12_2_1_linear_combination
    {X Y : ex_12_2_1_L2}
    (hX : X ∈ ex_12_2_1_W) (hY : Y ∈ ex_12_2_1_W)
    (α β : ℂ) :
    α • X + β • Y ∈ ex_12_2_1_W := by
  exact (ex_12_2_1_W).add_mem
    ((ex_12_2_1_W).smul_mem α hX)
    ((ex_12_2_1_W).smul_mem β hY)

theorem ex_12_2_1_initialSet_succ (k : ℕ) :
    ex_12_2_1_initialSet (k + 1) =
      ex_12_2_1_initialSet k ∪ ({k} : Set ℕ) := by
  ext n
  simp [ex_12_2_1_initialSet]

 
theorem ex_12_2_1_partialOnesLp_mem (k : ℕ) :
    ex_12_2_1_partialOnesLp k ∈ ex_12_2_1_W := by
  induction k with
  | zero =>
      simpa [ex_12_2_1_partialOnesLp_eq_indicatorConstLp,
        ex_12_2_1_initialSet] using ex_12_2_1_zero_mem
  | succ k ih =>
      have hdisj : Disjoint (ex_12_2_1_initialSet k) ({k} : Set ℕ) := by
        refine Set.disjoint_left.2 ?_
        intro n hn hn'
        have hnlt : n < k := by
          simpa [ex_12_2_1_initialSet] using hn
        have hneq : n = k := by
          simpa using hn'
        subst n
        exact (Nat.lt_irrefl k hnlt)
      have hsplit :
          ex_12_2_1_partialOnesLp (k + 1) =
            ex_12_2_1_partialOnesLp k + ex_12_2_1_coordinateLp k := by
        rw [ex_12_2_1_partialOnesLp_eq_indicatorConstLp,
          ex_12_2_1_partialOnesLp_eq_indicatorConstLp,
          ex_12_2_1_coordinateLp, ex_12_2_1_initialSet_succ]
        exact indicatorConstLp_disjoint_union
          (ex_12_2_1_initialSet_measurable k)
          (measurableSet_singleton k) (by finiteness) (by finiteness)
          hdisj (1 : ℂ)
      rw [hsplit]
      exact (ex_12_2_1_W).add_mem ih
        (Submodule.subset_span ⟨k, rfl⟩)

theorem ex_12_2_1_measure_singleton (n : ℕ) :
    ex_12_1_2_measure {n} = ex_12_1_2_weight n := by
  simpa [ex_12_1_2_measure] using
    (Measure.sum_smul_dirac_singleton
      (f := ex_12_1_2_weight) (a := n))

theorem ex_12_2_1_measureReal_singleton (n : ℕ) :
    ex_12_1_2_measure.real {n} = ex_12_1_2_realWeight n := by
  rw [measureReal_def, ex_12_2_1_measure_singleton]
  rfl

theorem ex_12_2_1_realWeight_pos (n : ℕ) :
    0 < ex_12_1_2_realWeight n := by
  rw [ex_12_1_2_realWeight_eq]
  positivity

theorem ex_12_2_1_inner_coordinate (m n : ℕ) :
    ⟪ex_12_2_1_coordinateLp m, ex_12_2_1_coordinateLp n⟫_ℂ =
      if m = n then (ex_12_1_2_realWeight m : ℂ) else 0 := by
  rw [ex_12_2_1_coordinateLp, ex_12_2_1_coordinateLp,
    L2.inner_indicatorConstLp_one_indicatorConstLp_one]
  by_cases h : m = n
  · subst n
    simp [ex_12_2_1_measureReal_singleton]
  · have hinter : ({m} : Set ℕ) ∩ {n} = ∅ := by
      ext x
      simp [h]
    simp [h, hinter]

theorem ex_12_2_1_inner_coordinate_allOnes (n : ℕ) :
    ⟪ex_12_2_1_coordinateLp n, ex_12_2_1_allOnesLp⟫_ℂ =
      (ex_12_1_2_realWeight n : ℂ) := by
  rw [ex_12_2_1_coordinateLp,
    ex_12_2_1_allOnesLp_eq_indicatorConstLp,
    L2.inner_indicatorConstLp_one_indicatorConstLp_one]
  simpa using ex_12_2_1_measureReal_singleton n



theorem ex_12_2_1_allOnesLp_not_mem :
    ex_12_2_1_allOnesLp ∉ ex_12_2_1_W := by
  classical
  intro hmem
  rw [ex_12_2_1_W, Finsupp.mem_span_range_iff_exists_finsupp] at hmem
  obtain ⟨c, hc⟩ := hmem
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset c.support
  have hinner := congrArg
    (fun X : ex_12_2_1_L2 => ⟪ex_12_2_1_coordinateLp n, X⟫_ℂ) hc
  have hzero :
      ⟪ex_12_2_1_coordinateLp n,
        c.sum (fun i a => a • ex_12_2_1_coordinateLp i)⟫_ℂ = 0 := by
    rw [Finsupp.inner_sum]
    simp [inner_smul_right, ex_12_2_1_inner_coordinate, hn]
  rw [hzero, ex_12_2_1_inner_coordinate_allOnes] at hinner
  have hne : (ex_12_1_2_realWeight n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ex_12_2_1_realWeight_pos n).ne'
  exact hne hinner.symm

theorem ex_12_2_1_initialSet_symmDiff_univ (k : ℕ) :
    ex_12_2_1_initialSet k ∆ (Set.univ : Set ℕ) = Set.Ici k := by
  ext n
  simp [ex_12_2_1_initialSet, Set.symmDiff_def, not_lt]

theorem ex_12_2_1_measure_tail_tendsto_zero :
    Tendsto (fun k : ℕ => ex_12_1_2_measure (Set.Ici k))
      atTop (nhds 0) := by
  have hinter : (⋂ k : ℕ, Set.Ici k) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro n hn
    have hle := Set.mem_iInter.mp hn (n + 1)
    have : n + 1 ≤ n := by
      simpa using hle
    omega
  have h := tendsto_measure_iInter_atTop
    (μ := ex_12_1_2_measure)
    (s := fun k : ℕ => Set.Ici k)
    (fun k => (measurableSet_Ici : MeasurableSet (Set.Ici k)).nullMeasurableSet)
    antitone_Ici ⟨0, measure_ne_top _ _⟩
  rw [hinter] at h
  simpa [Function.comp_def] using h

theorem ex_12_2_1_measure_symmDiff_tendsto_zero :
    Tendsto
      (fun k : ℕ => ex_12_1_2_measure
        (ex_12_2_1_initialSet k ∆ (Set.univ : Set ℕ)))
      atTop (nhds 0) := by
  simpa [ex_12_2_1_initialSet_symmDiff_univ] using
    ex_12_2_1_measure_tail_tendsto_zero



theorem ex_12_2_1_partialOnesLp_tendsto_allOnesLp :
    Tendsto ex_12_2_1_partialOnesLp atTop (nhds ex_12_2_1_allOnesLp) := by
  rw [show ex_12_2_1_partialOnesLp = fun k =>
      indicatorConstLp (μ := ex_12_1_2_measure) 2
        (ex_12_2_1_initialSet_measurable k) (by finiteness) (1 : ℂ) by
    funext k
    exact ex_12_2_1_partialOnesLp_eq_indicatorConstLp k]
  rw [ex_12_2_1_allOnesLp_eq_indicatorConstLp]
  exact tendsto_indicatorConstLp_set (by norm_num)
    ex_12_2_1_measure_symmDiff_tendsto_zero

theorem ex_12_2_1_partialOnesLp_norm_tendsto_zero :
    Tendsto (fun k =>
      ‖ex_12_2_1_partialOnesLp k - ex_12_2_1_allOnesLp‖)
      atTop (nhds 0) := by
  exact tendsto_iff_norm_sub_tendsto_zero.mp
    ex_12_2_1_partialOnesLp_tendsto_allOnesLp



def ex_12_2_1_L2Error (k : ℕ) : ℝ :=
  ‖ex_12_2_1_partialOnesLp k - ex_12_2_1_allOnesLp‖ ^ 2

theorem ex_12_2_1_L2Error_tendsto_zero :
    Tendsto ex_12_2_1_L2Error atTop (nhds 0) := by
  change Tendsto (fun k =>
    ‖ex_12_2_1_partialOnesLp k - ex_12_2_1_allOnesLp‖ ^ 2) atTop (nhds 0)
  simpa only [pow_two, zero_mul] using
    ex_12_2_1_partialOnesLp_norm_tendsto_zero.mul
      ex_12_2_1_partialOnesLp_norm_tendsto_zero



theorem ex_12_2_1_W_not_closed :
    ¬ IsClosed ((ex_12_2_1_W : Submodule ℂ ex_12_2_1_L2) :
      Set ex_12_2_1_L2) := by
  intro hclosed
  exact ex_12_2_1_allOnesLp_not_mem
    (hclosed.mem_of_tendsto ex_12_2_1_partialOnesLp_tendsto_allOnesLp
      (Filter.Eventually.of_forall ex_12_2_1_partialOnesLp_mem))

 
theorem ex_12_2_1 :
    (0 : ex_12_2_1_L2) ∈ ex_12_2_1_W ∧
      (∀ X Y : ex_12_2_1_L2, X ∈ ex_12_2_1_W → Y ∈ ex_12_2_1_W →
        ∀ α β : ℂ, α • X + β • Y ∈ ex_12_2_1_W) ∧
      (∀ k, ex_12_2_1_partialOnesLp k ∈ ex_12_2_1_W) ∧
      Tendsto ex_12_2_1_partialOnesLp atTop (nhds ex_12_2_1_allOnesLp) ∧
      ex_12_2_1_allOnesLp ∉ ex_12_2_1_W ∧
      ¬ IsClosed ((ex_12_2_1_W : Submodule ℂ ex_12_2_1_L2) :
        Set ex_12_2_1_L2) := by
  exact ⟨ex_12_2_1_zero_mem,
    (fun X Y hX hY α β => ex_12_2_1_linear_combination hX hY α β),
    ex_12_2_1_partialOnesLp_mem,
    ex_12_2_1_partialOnesLp_tendsto_allOnesLp,
    ex_12_2_1_allOnesLp_not_mem,
    ex_12_2_1_W_not_closed⟩
