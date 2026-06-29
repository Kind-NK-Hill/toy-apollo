import Mathlib

/-
TASK ID: prob_4_9
TYPE: Problem
SOURCE PLAN: 12_chap4_problems
TASK CONTENT:
\textbf{4.9.} Suppose $a_k$ and $b_k$ are real numbers satisfying $a_k \le b_k$ for $k = 1, 2, 3, \dots$. Prove:
\begin{enumerate}[label=(\alph*)]
    \item $\liminf_k a_k \le \liminf_k b_k$.
    \item $\limsup_k a_k \le \limsup_k b_k$.
\end{enumerate}
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter

theorem prob_4_9 (a b : ℕ → ℝ) (hab : ∀ k, a k ≤ b k) :
    liminf (fun n => (a n : EReal)) atTop ≤ liminf (fun n => (b n : EReal)) atTop ∧
    limsup (fun n => (a n : EReal)) atTop ≤ limsup (fun n => (b n : EReal)) atTop := by
  by_contra h_contra
  simp_all +decide [Filter.limsup, Filter.liminf]
  simp_all +decide [Filter.limsInf, Filter.limsSup]
  refine' h_contra _ |> not_le_of_gt <| le_csInf _ _ <;> norm_num
  · intro b x hx
    exact le_csSup
      ⟨⊤, by rintro a ⟨y, hy⟩; exact le_top⟩
      ⟨x, fun y hy => hx y hy |> le_trans <| mod_cast hab _⟩
  · exact ⟨⊤, ⟨0, fun _ _ => le_top⟩⟩
  · exact fun x n hn =>
      csInf_le
        ⟨⊥, by rintro x ⟨m, hm⟩; exact le_trans (by norm_num) (hm _ le_rfl)⟩
        ⟨n, fun m hm => le_trans (mod_cast hab _) (hn _ hm)⟩
