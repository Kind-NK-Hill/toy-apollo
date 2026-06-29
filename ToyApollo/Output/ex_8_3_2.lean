import Mathlib
import ToyApollo.Output.ex_3_3_4

/-
TASK ID: ex_8_3_2
TYPE: Example_Proof
SOURCE PLAN: 33_chap8_monge_kantorovich
TASK CONTENT:
\textbf{Example 8.3.2 (A Finite Version of Monge's Problem)} \\
Let $\delta_x$ denote the Dirac measure of a point $x\in \mathbb{R}$ (See Example 3.3.4). Suppose there is one unit of sand located at point $x_i$, for $i=1,2,\dots,n$. The input measure $\mu$ is
\[
\mu=\sum_{i=1}^{n} \delta_{x_i}.
\]

We want to move the sands to $n$ other points $y_i$, $i=1,2,\dots,n$, such that each point $y_i$ receives exactly one unit of sand. The output measure $\nu$ is thus
\[
\nu=\sum_{i=1}^{n} \delta_{y_i}.
\]

With this data, Monge's problem becomes a combinatorial problem, which is to find the optimal permutation $\pi:\{1,2,\dots,n\}\to \{1,2,\dots,n\}$ that minimizes the transportation cost given by
\[
\sum_{i=1}^{n} (x_i-y_{\pi(i)})^2.
\]

In other words, we want to find the optimal way to move each unit of sand from its initial position $x_i$ to its final position $y_{\pi(i)}$ such that the total transport cost is minimized.
-/

-- WRITE FINAL LEAN CODE BELOW

open scoped BigOperators

/-- The finite Monge transport cost attached to a permutation of the targets. -/
def finiteMongeCost {n : ℕ} (x y : Fin n → ℝ) (π : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i : Fin n, (x i - y (π i)) ^ 2

/-- Example 8.3.2: in the finite discrete setting, Monge's problem reduces to minimizing the
transport cost over permutations. Since the permutation space is finite, an optimal permutation
exists. -/
theorem ex_8_3_2 {n : ℕ} [NeZero n] (x y : Fin n → ℝ) :
    ∃ π : Equiv.Perm (Fin n), ∀ σ : Equiv.Perm (Fin n),
      finiteMongeCost x y π ≤ finiteMongeCost x y σ := by
  classical
  let cost : Equiv.Perm (Fin n) → ℝ := finiteMongeCost x y
  obtain ⟨π, hπ⟩ := Finite.exists_min cost
  exact ⟨π, hπ⟩
