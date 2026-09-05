/-
TASK ID: ex_12_2_2
TYPE: Example_Proof
SOURCE PLAN: chapter12-closed-subspace-projection
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_12.def_12_4




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory
open Filter

open scoped BigOperators InnerProductSpace

noncomputable section



structure ex_12_2_2_Partition (Ω : Type*) [MeasurableSpace Ω] (d : ℕ) where
  atom : Fin d → Set Ω
  measurable : ∀ i, MeasurableSet (atom i)
  cover : ∀ ω, ∃ i, ω ∈ atom i
  disjoint : ∀ i j, i ≠ j → Disjoint (atom i) (atom j)

 
def ex_12_2_2_indicator {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (π : ex_12_2_2_Partition Ω d) (i : Fin d) : Ω → ℝ :=
  (π.atom i).indicator (fun _ => 1)

theorem ex_12_2_2_indicator_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ}
    (π : ex_12_2_2_Partition Ω d) (i : Fin d) :
    MemLp (ex_12_2_2_indicator π i) (2 : ENNReal) P := by
  exact (memLp_const (μ := P) (p := (2 : ENNReal)) (1 : ℝ)).indicator
    (π.measurable i)

 
noncomputable def ex_12_2_2_indicatorLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ}
    (π : ex_12_2_2_Partition Ω d) (i : Fin d) : Ω →₂[P] ℝ :=
  (ex_12_2_2_indicator_memLp P π i).toLp (ex_12_2_2_indicator π i)



noncomputable def ex_12_2_2_W {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ}
    (π : ex_12_2_2_Partition Ω d) : Submodule ℝ (Ω →₂[P] ℝ) :=
  Submodule.span ℝ (Set.range (ex_12_2_2_indicatorLp P π))

instance ex_12_2_2_W_finiteDimensional {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ}
    (π : ex_12_2_2_Partition Ω d) :
    FiniteDimensional ℝ (ex_12_2_2_W P π) := by
  exact Module.Finite.of_fg
    (Submodule.fg_span (Set.finite_range (ex_12_2_2_indicatorLp P π)))



noncomputable def ex_12_2_2_simpleFromCoeffs {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ}
    (π : ex_12_2_2_Partition Ω d) (c : Fin d → ℝ) : Ω →₂[P] ℝ :=
  ∑ i : Fin d, c i • ex_12_2_2_indicatorLp P π i

theorem ex_12_2_2_simpleFromCoeffs_mem {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ}
    (π : ex_12_2_2_Partition Ω d) (c : Fin d → ℝ) :
    ex_12_2_2_simpleFromCoeffs P π c ∈ ex_12_2_2_W P π := by
  classical
  unfold ex_12_2_2_simpleFromCoeffs ex_12_2_2_W
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ (c i) (Submodule.subset_span ⟨i, rfl⟩)

 
theorem ex_12_2_2_indicatorLp_inner_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ}
    (π : ex_12_2_2_Partition Ω d) {i j : Fin d} (hij : i ≠ j) :
    ⟪ex_12_2_2_indicatorLp P π i, ex_12_2_2_indicatorLp P π j⟫_ℝ = 0 := by
  rw [L2.inner_def]
  refine integral_eq_zero_of_ae ?_
  have hi :
      (fun ω => ex_12_2_2_indicatorLp P π i ω) =ᵐ[P]
        ex_12_2_2_indicator π i := by
    simpa [ex_12_2_2_indicatorLp] using
      (ex_12_2_2_indicator_memLp P π i).coeFn_toLp
  have hj :
      (fun ω => ex_12_2_2_indicatorLp P π j ω) =ᵐ[P]
        ex_12_2_2_indicator π j := by
    simpa [ex_12_2_2_indicatorLp] using
      (ex_12_2_2_indicator_memLp P π j).coeFn_toLp
  filter_upwards [hi, hj] with ω hiω hjω
  rw [hiω, hjω]
  by_cases hωi : ω ∈ π.atom i
  · have hωj : ω ∉ π.atom j :=
      Set.disjoint_left.mp (π.disjoint i j hij) hωi
    simp [ex_12_2_2_indicator, hωi, hωj]
  · simp [ex_12_2_2_indicator, hωi]



noncomputable def ex_12_2_2_canonicalCoeffCLM {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ}
    (π : ex_12_2_2_Partition Ω d) (i : Fin d) :
    (Ω →₂[P] ℝ) →L[ℝ] ℝ :=
  (‖ex_12_2_2_indicatorLp P π i‖ ^ 2)⁻¹ •
    innerSL ℝ (ex_12_2_2_indicatorLp P π i)

noncomputable def ex_12_2_2_canonicalCoeff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ}
    (π : ex_12_2_2_Partition Ω d) (i : Fin d) (X : Ω →₂[P] ℝ) : ℝ :=
  ex_12_2_2_canonicalCoeffCLM P π i X

theorem ex_12_2_2_canonicalCoeff_eq_zero_of_indicatorLp_eq_zero
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ}
    (π : ex_12_2_2_Partition Ω d) (i : Fin d) (X : Ω →₂[P] ℝ)
    (hi : ex_12_2_2_indicatorLp P π i = 0) :
    ex_12_2_2_canonicalCoeff P π i X = 0 := by
  simp [ex_12_2_2_canonicalCoeff, ex_12_2_2_canonicalCoeffCLM, hi]

private theorem ex_12_2_2_simpleFromCanonicalCoeffs_indicatorLp
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ}
    (π : ex_12_2_2_Partition Ω d) (j : Fin d) :
    ex_12_2_2_simpleFromCoeffs P π
        (fun i => ex_12_2_2_canonicalCoeff P π i
          (ex_12_2_2_indicatorLp P π j)) =
      ex_12_2_2_indicatorLp P π j := by
  by_cases hj : ex_12_2_2_indicatorLp P π j = 0
  · simp [ex_12_2_2_simpleFromCoeffs, ex_12_2_2_canonicalCoeff,
      ex_12_2_2_canonicalCoeffCLM, hj]
  · classical
    unfold ex_12_2_2_simpleFromCoeffs
    rw [Finset.sum_eq_single j]
    · have hnorm : ‖ex_12_2_2_indicatorLp P π j‖ ≠ 0 :=
        norm_ne_zero_iff.mpr hj
      simp [ex_12_2_2_canonicalCoeff, ex_12_2_2_canonicalCoeffCLM,
        innerSL_apply_apply, hnorm]
    · intro i _hi hij
      have hortho :
          ⟪ex_12_2_2_indicatorLp P π i,
            ex_12_2_2_indicatorLp P π j⟫_ℝ = 0 :=
        ex_12_2_2_indicatorLp_inner_eq_zero P π hij
      simp [ex_12_2_2_canonicalCoeff, ex_12_2_2_canonicalCoeffCLM,
        innerSL_apply_apply, hortho]
    · intro hjnot
      exact (hjnot (Finset.mem_univ j)).elim



theorem ex_12_2_2_simpleFromCanonicalCoeffs_eq_of_mem
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ}
    (π : ex_12_2_2_Partition Ω d) {X : Ω →₂[P] ℝ}
    (hX : X ∈ ex_12_2_2_W P π) :
    ex_12_2_2_simpleFromCoeffs P π
        (fun i => ex_12_2_2_canonicalCoeff P π i X) = X := by
  change X ∈ Submodule.span ℝ
    (Set.range (ex_12_2_2_indicatorLp P π)) at hX
  refine Submodule.span_induction (p := fun X _ =>
    ex_12_2_2_simpleFromCoeffs P π
      (fun i => ex_12_2_2_canonicalCoeff P π i X) = X) ?_ ?_ ?_ ?_ hX
  · intro x hx
    rcases hx with ⟨i, rfl⟩
    exact ex_12_2_2_simpleFromCanonicalCoeffs_indicatorLp P π i
  · simp [ex_12_2_2_simpleFromCoeffs, ex_12_2_2_canonicalCoeff]
  · intro x y _hx _hy hx hy
    calc
      ex_12_2_2_simpleFromCoeffs P π
          (fun i => ex_12_2_2_canonicalCoeff P π i (x + y)) =
          ex_12_2_2_simpleFromCoeffs P π
            (fun i => ex_12_2_2_canonicalCoeff P π i x) +
          ex_12_2_2_simpleFromCoeffs P π
            (fun i => ex_12_2_2_canonicalCoeff P π i y) := by
              simp [ex_12_2_2_simpleFromCoeffs, ex_12_2_2_canonicalCoeff,
                add_smul, Finset.sum_add_distrib]
      _ = x + y := by rw [hx, hy]
  · intro r x _hx hx
    calc
      ex_12_2_2_simpleFromCoeffs P π
          (fun i => ex_12_2_2_canonicalCoeff P π i (r • x)) =
          r • ex_12_2_2_simpleFromCoeffs P π
            (fun i => ex_12_2_2_canonicalCoeff P π i x) := by
              simp [ex_12_2_2_simpleFromCoeffs, ex_12_2_2_canonicalCoeff,
                Finset.smul_sum, smul_smul]
      _ = r • x := by rw [hx]



theorem ex_12_2_2_canonicalCoeff_cauchySeq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ}
    (π : ex_12_2_2_Partition Ω d) (X : ℕ → Ω →₂[P] ℝ)
    (hX : CauchySeq X) (i : Fin d) :
    CauchySeq (fun n => ex_12_2_2_canonicalCoeff P π i (X n)) := by
  simpa [ex_12_2_2_canonicalCoeff, Function.comp_def] using
    (ex_12_2_2_canonicalCoeffCLM P π i).lipschitz.cauchySeq_comp hX



theorem ex_12_2_2_cauchySequence_sourceRoute
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ}
    (π : ex_12_2_2_Partition Ω d) (X : ℕ → Ω →₂[P] ℝ)
    (hXmem : ∀ n, X n ∈ ex_12_2_2_W P π) (hXcauchy : CauchySeq X) :
    ∃ c : Fin d → ℝ,
      (∀ n, ex_12_2_2_simpleFromCoeffs P π
        (fun i => ex_12_2_2_canonicalCoeff P π i (X n)) = X n) ∧
      (∀ i, Tendsto (fun n => ex_12_2_2_canonicalCoeff P π i (X n))
        atTop (nhds (c i))) ∧
      Tendsto X atTop (nhds (ex_12_2_2_simpleFromCoeffs P π c)) ∧
      ex_12_2_2_simpleFromCoeffs P π c ∈ ex_12_2_2_W P π := by
  choose c hc using fun i : Fin d =>
    cauchySeq_tendsto_of_complete
      (ex_12_2_2_canonicalCoeff_cauchySeq P π X hXcauchy i)
  have hrepr : ∀ n, ex_12_2_2_simpleFromCoeffs P π
      (fun i => ex_12_2_2_canonicalCoeff P π i (X n)) = X n :=
    fun n => ex_12_2_2_simpleFromCanonicalCoeffs_eq_of_mem P π (hXmem n)
  have hsum : Tendsto
      (fun n => ex_12_2_2_simpleFromCoeffs P π
        (fun i => ex_12_2_2_canonicalCoeff P π i (X n)))
      atTop (nhds (ex_12_2_2_simpleFromCoeffs P π c)) := by
    unfold ex_12_2_2_simpleFromCoeffs
    exact tendsto_finsetSum (s := (Finset.univ : Finset (Fin d)))
      (fun i _hi => (hc i).smul_const (ex_12_2_2_indicatorLp P π i))
  refine ⟨c, hrepr, hc, ?_, ex_12_2_2_simpleFromCoeffs_mem P π c⟩
  simpa only [hrepr] using hsum



theorem ex_12_2_2_W_closed {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ}
    (π : ex_12_2_2_Partition Ω d) :
    IsClosed ((ex_12_2_2_W P π : Submodule ℝ (Ω →₂[P] ℝ)) :
      Set (Ω →₂[P] ℝ)) := by
  apply IsSeqClosed.isClosed
  intro X Xlim hXmem hXlim
  rcases ex_12_2_2_cauchySequence_sourceRoute P π X hXmem hXlim.cauchySeq with
    ⟨c, _hrepr, _hcoeff, hroute, hroute_mem⟩
  have hEq : Xlim = ex_12_2_2_simpleFromCoeffs P π c :=
    tendsto_nhds_unique hXlim hroute
  rw [hEq]
  exact hroute_mem

theorem ex_12_2_2_linear_combination {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ}
    (π : ex_12_2_2_Partition Ω d) {X Y : Ω →₂[P] ℝ}
    (hX : X ∈ ex_12_2_2_W P π) (hY : Y ∈ ex_12_2_2_W P π)
    (α β : ℝ) :
    α • X + β • Y ∈ ex_12_2_2_W P π := by
  exact (ex_12_2_2_W P π).add_mem
    ((ex_12_2_2_W P π).smul_mem α hX)
    ((ex_12_2_2_W P π).smul_mem β hY)



theorem ex_12_2_2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ}
    (π : ex_12_2_2_Partition Ω d) :
    (∀ c : Fin d → ℝ, ex_12_2_2_simpleFromCoeffs P π c ∈ ex_12_2_2_W P π) ∧
      (∀ X Y : Ω →₂[P] ℝ, X ∈ ex_12_2_2_W P π →
        Y ∈ ex_12_2_2_W P π → ∀ α β : ℝ,
          α • X + β • Y ∈ ex_12_2_2_W P π) ∧
      IsClosed ((ex_12_2_2_W P π : Submodule ℝ (Ω →₂[P] ℝ)) :
        Set (Ω →₂[P] ℝ)) := by
  exact ⟨ex_12_2_2_simpleFromCoeffs_mem P π,
    (fun X Y hX hY α β => ex_12_2_2_linear_combination P π hX hY α β),
    ex_12_2_2_W_closed P π⟩
