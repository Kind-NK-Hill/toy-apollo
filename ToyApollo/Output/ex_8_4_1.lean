import Mathlib
import ToyApollo.Output.ex_3_3_4

/-
TASK ID: ex_8_4_1
TYPE: Example_Proof
SOURCE PLAN: 34_chap8_total_variation_distance
TASK CONTENT:
\textbf{Example 8.4.1 (Total Variation Distance Between Two Dirac Measures)} \\
Let $\mu_x$ denote the Dirac measure on $\mathbb{R}$ that is concentrated at the point $x$, i.e., $\mu_x(A)=1$ if $x\in A$ and $\mu_x(A)=0$ if $x\notin A$ (See Example 3.3.4). For $x\neq y$, the total variation distance between $\mu_x$ and $\mu_y$ is equal to 1. It is because for any measurable set $A$ that contains $x$ but not $y$, we have $\mu_x(A)-\mu_y(A)=1-0=1$.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set

noncomputable def ex841TotalVariationDistance
    {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) : ℝ :=
  sSup {d : ℝ | ∃ A : Set Ω, MeasurableSet A ∧ d = |P.real A - Q.real A|}

/-- Example 8.4.1: two distinct Dirac measures on `ℝ` are at total variation distance `1`. -/
theorem ex_8_4_1 {x y : ℝ} (hxy : x ≠ y) :
    ex841TotalVariationDistance (Measure.dirac x) (Measure.dirac y) = 1 := by
  let S : Set ℝ :=
    {d : ℝ |
      ∃ A : Set ℝ,
        MeasurableSet A ∧ d = |(Measure.dirac x).real A - (Measure.dirac y).real A|}
  have hupper : ∀ d ∈ S, d ≤ 1 := by
    intro d hd
    rcases hd with ⟨A, hA, rfl⟩
    by_cases hxA : x ∈ A <;> by_cases hyA : y ∈ A
    · rw [Measure.real_def, Measure.real_def, Measure.dirac_apply_of_mem hxA,
        Measure.dirac_apply_of_mem hyA]
      norm_num
    · have hy0 : Measure.dirac y A = 0 := by
        rw [Measure.dirac_apply' y hA]
        simp [hyA]
      rw [Measure.real_def, Measure.real_def, Measure.dirac_apply_of_mem hxA, hy0]
      norm_num
    · have hx0 : Measure.dirac x A = 0 := by
        rw [Measure.dirac_apply' x hA]
        simp [hxA]
      rw [Measure.real_def, Measure.real_def, hx0, Measure.dirac_apply_of_mem hyA]
      norm_num
    · have hx0 : Measure.dirac x A = 0 := by
        rw [Measure.dirac_apply' x hA]
        simp [hxA]
      have hy0 : Measure.dirac y A = 0 := by
        rw [Measure.dirac_apply' y hA]
        simp [hyA]
      rw [Measure.real_def, Measure.real_def, hx0, hy0]
      norm_num
  have hbounded : BddAbove S := ⟨1, hupper⟩
  have hone_mem : 1 ∈ S := by
    refine ⟨{x}, measurableSet_singleton x, ?_⟩
    have hx_mem : x ∈ ({x} : Set ℝ) := by simp
    have hy_not_mem : y ∉ ({x} : Set ℝ) := by
      simpa [Set.mem_singleton_iff] using hxy.symm
    have hy0 : Measure.dirac y ({x} : Set ℝ) = 0 := by
      rw [Measure.dirac_apply' y (measurableSet_singleton x)]
      simp [hy_not_mem]
    rw [Measure.real_def, Measure.real_def, Measure.dirac_apply_of_mem hx_mem, hy0]
    norm_num
  have hnonempty : S.Nonempty := ⟨1, hone_mem⟩
  unfold ex841TotalVariationDistance
  change sSup S = 1
  apply le_antisymm
  · exact csSup_le hnonempty hupper
  · exact le_csSup hbounded hone_mem
