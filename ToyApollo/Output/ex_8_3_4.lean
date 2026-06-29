import Mathlib

/-
TASK ID: ex_8_3_4
TYPE: Example_Proof
SOURCE PLAN: 33_chap8_monge_kantorovich
TASK CONTENT:
\textbf{Example 8.3.4 (A Discrete Kantorovich Problem)} \\
Suppose $\mathcal{X}=\{a,b\}$ is a set with size $2$, and $\mathcal{Y}=\{1,2,3\}$ is a set with size $3$. Let $P$ be the probability measure on $\mathcal{X}$ defined by $P(\{a\})=1/3$ and $P(\{b\})=2/3$, and let $Q$ be the probability measure on $\mathcal{Y}$ defined by $Q(\{1\})=Q(\{2\})=1/5$ and $Q(\{3\})=3/5$. The Kantorovich problem is to find a transport plan between $P$ and $Q$ that minimizes the total transport cost, where the cost of transporting mass from $i\in \mathcal{X}$ to $j\in \mathcal{Y}$ is given by the cost function $c:\mathcal{X}\times \mathcal{Y}\to \mathbb{R}$.

The transport plan can be represented by a $2\times 3$ matrix $T=[t_{ij}]$, where $t_{ij}$ represents the amount of mass transported from $i\in \mathcal{X}$ to $j\in \mathcal{Y}$. The cost of transporting mass from $i$ to $j$ is given by $c_{ij}=c(i,j)$. The Kantorovich problem can be formulated as a linear programming problem with variables $t_{ij}$. The objective function to be minimized is
\[
\sum_{i\in \{a,b\}}\sum_{j\in \{1,2,3\}} c_{ij}t_{ij}.
\]

The constraints are the marginal constraints that ensure that the total mass transported from each source equals the total mass received at each target:
\[
t_{a1}+t_{b1}=1/5, \qquad t_{a1}+t_{a2}+t_{a3}=1/3,
\]
\[
t_{a2}+t_{b2}=1/5, \qquad t_{b1}+t_{b2}+t_{b3}=2/3,
\]
\[
t_{a3}+t_{b3}=3/5,
\]
\[
t_{ij}\ge 0 \qquad \text{for } i\in \{a,b\},\ j\in \{1,2,3\}.
\]

Solving this linear programming problem gives the optimal transport plan between $P$ and $Q$.

In the Kantorovich problem, if $\mathcal{X}$ is the same as $\mathcal{Y}$ and is equipped with a metric $d(x,y)$, we can take $d(x,y)^p$ as the cost function, for some real number $p\ge 1$. The $p$-th root of the minimal transport cost is called the $p$-\textit{Wasserstein distance} between $P$ and $Q$
\[
W_p(P,Q)\triangleq \left( \min_{\mu\in \Pi(P,Q)} \int_{\mathcal{X}\times \mathcal{X}} d(x,y)^p\, d\mu(x,y) \right)^{1/p}.
\]

The optimal transport problem with Wasserstein distance is an emerging method in computer vision, statistics, and data science [6].
-/

-- WRITE FINAL LEAN CODE BELOW

open scoped BigOperators

noncomputable section

/-- `false`/`true` encode the two source atoms `a` and `b`. -/
abbrev Ex834Source := Bool

/-- `0,1,2` encode the three target atoms `1,2,3`. -/
abbrev Ex834Target := Fin 3

/-- An explicit feasible transport plan for the marginal constraints in Example 8.3.4. -/
def ex834Plan : Ex834Source → Ex834Target → ℝ
  | false, 0 => 1 / 5
  | false, 1 => 1 / 15
  | false, 2 => 1 / 15
  | true, 0 => 0
  | true, 1 => 2 / 15
  | true, 2 => 8 / 15

/-- The linear-programming objective associated to a cost matrix `c`. -/
def ex834TransportCost (c : Ex834Source → Ex834Target → ℝ)
    (T : Ex834Source → Ex834Target → ℝ) : ℝ :=
  ∑ i, ∑ j, c i j * T i j

/-- Predicate expressing the marginal constraints of the discrete Kantorovich problem. -/
def IsEx834FeasiblePlan (T : Ex834Source → Ex834Target → ℝ) : Prop :=
  (∀ i j, 0 ≤ T i j) ∧
    (∑ j, T false j = 1 / 3) ∧
    (∑ j, T true j = 2 / 3) ∧
    (∑ i, T i 0 = 1 / 5) ∧
    (∑ i, T i 1 = 1 / 5) ∧
    (∑ i, T i 2 = 3 / 5)

/-- Example 8.3.4: the discrete Kantorovich problem is a linear program with marginal
constraints, and the explicit matrix `ex834Plan` is a feasible transport plan for those
constraints. -/
theorem ex_8_3_4 :
    IsEx834FeasiblePlan ex834Plan ∧
      ∀ c : Ex834Source → Ex834Target → ℝ,
        ex834TransportCost c ex834Plan =
          ∑ i, ∑ j, c i j * ex834Plan i j := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j
      fin_cases j <;> cases i <;> norm_num [ex834Plan]
    · rw [Fin.sum_univ_three]
      norm_num [ex834Plan]
    · rw [Fin.sum_univ_three]
      norm_num [ex834Plan]
    · norm_num [ex834Plan, Fintype.sum_bool]
    · norm_num [ex834Plan, Fintype.sum_bool]
    · norm_num [ex834Plan, Fintype.sum_bool]
  · intro c
    rfl
