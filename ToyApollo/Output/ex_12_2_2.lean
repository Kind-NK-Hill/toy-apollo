import Mathlib
import ToyApollo.Output.def_12_4

/-
TASK ID: ex_12_2_2
TYPE: Example_Proof
SOURCE PLAN: chapter12-closed-subspace-projection
TASK CONTENT:
\textbf{Example 12.2.2 (Simple Random Variables Associated with a Fixed Partition of the} \\

Sample Space)

Let .(\Omega, \mathcal{F},P) be a probability space and let A1, A2,...,A d be a partition of the sample space

\Omega Let W denote the set consisting of random variables that are constant on each Ak ,f o r k =

1, 2,...,d It is clear that W is a linear subspace of L2(P) .

To show that W is closed, consider a Cauchy sequence .(Xn)\infty

n=1 in W For each index

k = 1, 2,...,d , we can write Xn()1Ak () = cnk 1Ak () for some constant cnk The sequence

(cnk)\infty

n=1 is a Cauchy sequence of real numbers and thus is converging to some constant, say k ,a s

n \to\infty .

Define a random variable X in W by.

\sumd

k=1 k 1Ak S i n c eXk \to X inL2(P) , we see that W is

a closed subspace.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory
open Filter

open scoped BigOperators

noncomputable section

/-- A finite measurable partition `A₁,...,A_d` of the sample space from
Example 12.2.2. -/
structure ex_12_2_2_Partition (Ω : Type*) [MeasurableSpace Ω] (d : ℕ) where
  atom : Fin d → Set Ω
  measurable : ∀ i, MeasurableSet (atom i)
  cover : ∀ ω, ∃ i, ω ∈ atom i
  disjoint : ∀ i j, i ≠ j → Disjoint (atom i) (atom j)

/-- The indicator of one cell of the fixed finite partition. -/
def ex_12_2_2_indicator {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (π : ex_12_2_2_Partition Ω d) (i : Fin d) : Ω → ℝ :=
  (π.atom i).indicator (fun _ => 1)

theorem ex_12_2_2_indicator_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ}
    (π : ex_12_2_2_Partition Ω d) (i : Fin d) :
    MemLp (ex_12_2_2_indicator π i) (2 : ENNReal) P := by
  exact (memLp_const (μ := P) (p := (2 : ENNReal)) (1 : ℝ)).indicator
    (π.measurable i)

/-- The `L²(P)` element represented by a partition-cell indicator. -/
noncomputable def ex_12_2_2_indicatorLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ}
    (π : ex_12_2_2_Partition Ω d) (i : Fin d) : Ω →₂[P] ℝ :=
  (ex_12_2_2_indicator_memLp P π i).toLp (ex_12_2_2_indicator π i)

/-- The closed subspace `W`: finite linear combinations of the partition-cell
indicators. This is the `L²` quotient-space version of variables constant on
each atom of the finite partition. -/
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

/-- The finite-partition subspace is closed because it is finite-dimensional. -/
theorem ex_12_2_2_W_closed {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ}
    (π : ex_12_2_2_Partition Ω d) :
    IsClosed ((ex_12_2_2_W P π : Submodule ℝ (Ω →₂[P] ℝ)) :
      Set (Ω →₂[P] ℝ)) := by
  exact finiteDimensional_submodule_isClosed (ex_12_2_2_W P π)

/-- The simple random variable determined by coefficients on the fixed
partition cells. -/
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

theorem ex_12_2_2_linear_combination {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {d : ℕ}
    (π : ex_12_2_2_Partition Ω d) {X Y : Ω →₂[P] ℝ}
    (hX : X ∈ ex_12_2_2_W P π) (hY : Y ∈ ex_12_2_2_W P π)
    (α β : ℝ) :
    α • X + β • Y ∈ ex_12_2_2_W P π := by
  exact (ex_12_2_2_W P π).add_mem
    ((ex_12_2_2_W P π).smul_mem α hX)
    ((ex_12_2_2_W P π).smul_mem β hY)

/-- Example 12.2.2: random variables constant on a fixed finite partition form
a finite-dimensional, hence closed, subspace of `L²(P)`. -/
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
