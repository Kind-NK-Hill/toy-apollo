import Mathlib

/-
TASK ID: prob_3_3
TYPE: Problem
SOURCE PLAN: 07_chap3_problems
TASK CONTENT:
\textbf{3.3.} For $i = 1, 2, 3, \dots$, let $p_i$ be a nonnegative real number such that $\sum_{i=1}^\infty p_i$ is finite. We define a function $\mu$ on $2^{\mathbb{N}}$ by

\[
\mu(A) \triangleq \begin{cases} 
\sum_{i \in A} p_i & \text{if } A \text{ has finite cardinality} \\ 
\infty & \text{if } A \text{ is an infinite set,} 
\end{cases}
\]
for $A \subseteq \mathbb{N}$:
\begin{enumerate}[label=(\alph*)]
    \item Determine whether $\mu$ is finitely additive.
    \item Determine whether $\mu$ is $\sigma$-additive.
\end{enumerate}
-/

-- WRITE FINAL LEAN CODE BELOW

open Set Classical
open scoped ENNReal NNReal

theorem prob_3_3 (p : ℕ → ℝ≥0) (hp : Summable p) :
    let μ : Set ℕ → ℝ≥0∞ := fun A =>
      if hA : A.Finite then (hA.toFinset.sum fun x => (p x : ℝ≥0∞)) else ⊤
    (∀ A B : Set ℕ, Disjoint A B → μ (A ∪ B) = μ A + μ B) ∧
    (∃ (f : ℕ → Set ℕ), (∀ i j, i ≠ j → Disjoint (f i) (f j)) ∧
        μ (⋃ i, f i) ≠ ∑' i, μ (f i)) := by
  refine' ⟨_, _⟩
  · intro A B hAB
    by_cases hA : A.Finite <;> by_cases hB : B.Finite <;> simp +decide [hA, hB, hAB]
    rw [← Finset.sum_union]
    congr
    ext
    simp +decide [Set.disjoint_left] at *
    aesop
  · refine' ⟨fun i => {i}, _, _⟩ <;> simp +decide [Set.disjoint_singleton]
    split_ifs <;> simp_all +decide [Set.iUnion_of_singleton]
    · exact absurd ‹_› (Set.infinite_univ.mono fun x _ => by simp +decide)
    · rw [eq_comm]
      exact ENNReal.tsum_coe_ne_top_iff_summable.mpr hp
