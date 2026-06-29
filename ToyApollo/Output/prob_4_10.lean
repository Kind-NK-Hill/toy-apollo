import Mathlib

/-
TASK ID: prob_4_10
TYPE: Problem
SOURCE PLAN: 12_chap4_problems
TASK CONTENT:
\textbf{4.10.} Show that for any numerical sequence $(a_k)_{k=1}^{\infty}$,
\[
\liminf_k a_k \le \limsup_k a_k.
\]
-/

open Filter

theorem prob_4_10 (a : ℕ → ℝ) :
    liminf (fun n => (a n : EReal)) atTop ≤ limsup (fun n => (a n : EReal)) atTop := by
  simp +decide [liminf, limsup]
  simp +decide [Filter.limsInf, Filter.limsSup]
  exact fun b x hx y z hy =>
    le_trans (hy _ (le_max_left _ _)) (hx _ (le_max_right _ _))
