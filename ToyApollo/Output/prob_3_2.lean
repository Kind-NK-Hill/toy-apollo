import Mathlib

/-
TASK ID: prob_3_2
TYPE: Problem
SOURCE PLAN: 07_chap3_problems
TASK CONTENT:
\textbf{3.2.} Let $P$ be a Lebesgue--Stieltjes measure on $\mathbb{R}$ corresponding to a continuous distribution function, i.e., $P$ is a set function on $\mathcal{B}(\mathbb{R})$ and there exists a continuous function $F(x)$ such that $P([a, b]) = F(b) - F(a)$ for all $a < b$, and $P(\mathbb{R}) = 1$:
\begin{enumerate}
    \item Show that $P(A) = 0$ for all countable subsets $A$ of $\mathbb{R}$.
    \item If $P(A) = 1$, can we deduce that $A$ is a dense subset of $\mathbb{R}$?
\end{enumerate}
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set ENNReal

/-
Part 1: A continuous Stieltjes measure assigns zero measure to every countable set.
-/
theorem prob_3_2_part1 :
    ∀ (F : StieltjesFunction ℝ) (hF_cont : Continuous F)
        (hF_total : F.measure Set.univ = 1) (A : Set ℝ) (hA : Countable A),
        F.measure A = 0 := by
  intro F hF_cont _hF_total A hA_countable
  have h_singleton_zero : ∀ x, F.measure {x} = 0 := by
    intro x
    have h_singleton_formula :
        F.measure {x} = ENNReal.ofReal (F x - Function.leftLim (↑F) x) := by
      exact StieltjesFunction.measure_singleton F x
    rw [h_singleton_formula, ENNReal.ofReal_eq_zero]
    refine sub_nonpos_of_le ?_
    exact le_of_eq <| by
      simpa using
        tendsto_nhds_unique hF_cont.continuousWithinAt (F.mono.tendsto_leftLim x)
  exact (measure_null_iff_singleton hA_countable).mpr fun x _hx => h_singleton_zero x

/-
Part 2: There exists a continuous Stieltjes measure with F.measure A = 1
    but A is not dense.
-/
theorem prob_3_2_part2 :
    ∃ (F : StieltjesFunction ℝ) (hF_cont : Continuous F)
        (hF_total : F.measure Set.univ = 1) (A : Set ℝ),
        F.measure A = 1 ∧ ¬ Dense A := by
  use StieltjesFunction.mk (fun x => max 0 (min x 1))
    (by
      intro x y hxy
      exact max_le_max le_rfl (min_le_min hxy le_rfl))
    (by
      intro x
      exact Continuous.continuousWithinAt
        (by apply_rules [Continuous.max, Continuous.min] <;> continuity))
  all_goals generalize_proofs at *
  refine ⟨?_, ?_, Set.Icc 0 1, ?_, ?_⟩
  · exact Continuous.max continuous_const (Continuous.min continuous_id continuous_const)
  · erw [StieltjesFunction.measure_univ]
    norm_num
    rotate_left
    · exact 0
    · exact 1
    · exact tendsto_const_nhds.congr' (by
        filter_upwards [Filter.eventually_lt_atBot 0] with x hx
        simp +decide [hx.le])
    · exact tendsto_const_nhds.congr' (by
        filter_upwards [Filter.eventually_ge_atTop 1] with x hx
        aesop)
    · norm_num
  · erw [StieltjesFunction.measure_Icc]
    norm_num
    rw [leftLim_eq_of_tendsto]
    · exact Filter.NeBot.ne'
    · exact tendsto_const_nhds.congr' (by
        filter_upwards [self_mem_nhdsWithin] with x hx
        cases max_cases (0 : ℝ) (min x 1) <;> cases min_cases x 1 <;> linarith [hx.out])
  · exact fun h => absurd (h.exists_gt 1) (by norm_num)

/--
PROBLEM: Let P be a Lebesgue-Stieltjes measure on ℝ corresponding to a continuous
distribution function. Show that:
1. P(A) = 0 for all countable subsets A of ℝ.
2. If P(A) = 1, can we deduce that A is dense? (Answer: not necessarily)
-/
theorem prob_3_2 :
    (∀ (F : StieltjesFunction ℝ) (hF_cont : Continuous F)
        (hF_total : F.measure Set.univ = 1) (A : Set ℝ) (hA : Countable A),
        F.measure A = 0) ∧
    (∃ (F : StieltjesFunction ℝ) (hF_cont : Continuous F)
        (hF_total : F.measure Set.univ = 1) (A : Set ℝ),
        F.measure A = 1 ∧ ¬ Dense A) :=
  ⟨prob_3_2_part1, prob_3_2_part2⟩
