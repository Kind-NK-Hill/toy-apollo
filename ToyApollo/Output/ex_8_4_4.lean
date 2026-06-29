import Mathlib
import ToyApollo.Output.ch8_bernoulli_bool_core
import ToyApollo.Output.def_8_5

/-
TASK ID: ex_8_4_4
TYPE: Example_Proof
SOURCE PLAN: 34_chap8_total_variation_distance
TASK CONTENT:
\textbf{Example 8.4.4 (An Example of Maximal Coupling)} \\
Suppose $\Omega=\{1,2\}$ and we define two probability measures $P$ and $Q$ on $\mathcal{X}$ by
\[
P(\{1\})=1/3,\quad P(\{2\})=2/3,
\qquad \text{and} \qquad
Q(\{1\})=3/4,\quad P(\{2\})=1/4.
\]

The total variation distance between $P$ and $Q$ is $2/3-1/4=5/12$.

The corresponding Kantorovich problem is to minimize $x_{12}+x_{21}$, subject to the constraints
\[
x_{11}+x_{12}=1/3,\qquad x_{11}+x_{21}=3/4,
\]
\[
x_{21}+x_{22}=2/3,\qquad x_{12}+x_{22}=1/4,
\]
\[
x_{11},x_{12},x_{21},x_{22}\ge 0.
\]

We want to take the variables $x_{12}$ and $x_{21}$ to be as small as possible. In other words, we want $x_{11}$ and $x_{22}$ to be as large as possible, while satisfying the constraints. Because all variables are nonnegative, we must have $x_{11}\le 1/3$ and $x_{22}\le 1/4$. If we set $x_{11}=1/3$ and $x_{22}=1/4$, then the other constraints imply that we must have $x_{12}=0$ and $x_{21}=2/3-1/4=5/12$. We can visualize the transport plan as a $2\times 2$ array
\[
\begin{bmatrix}
x_{11} & x_{12}\\
x_{21} & x_{22}
\end{bmatrix}
=
\begin{bmatrix}
1/3 & 0\\
5/12 & 1/4
\end{bmatrix}.
\]

This is indeed the optimal solution to the linear program. It agrees with the total variation distance $5/12$ of $P$ and $Q$ and hence is a maximal coupling.

The total variation distance can be interpreted as a solution to the Kantorovich problem with cost function
\[
c_0(x,y)=
\begin{cases}
1 & \text{if } x\neq y,\\
0 & \text{if } x=y.
\end{cases}
\]

For any coupling $(\mathcal{X}\times \mathcal{X},\mathcal{F}\times \mathcal{F},\mu)$ of $P$ and $Q$, the probability $\mu(\{X\neq Y\})$ can be written as
\[
\int_{\mathcal{X}\times \mathcal{X}} c_0(x,y)\, d\mu(x,y).
\]

Let $\Pi(P,Q)$ denote the set of all probability measures $\mu$ on the product space $(\mathcal{X}\times \mathcal{X},\mathcal{F}\times \mathcal{F})$ such that $X_{\#}\mu=P$ and $Y_{\#}\mu=Q$. The coupling inequality implies that
\begin{equation}
d_{TV}(P,Q)
=
\inf_{\mu\in \Pi(P,Q)}
\left\{
\int_{\mathcal{X}\times \mathcal{X}} c_0(x,y)\, d\mu(x,y)
\right\}.
\tag{8.4}
\end{equation}

The infimum is taken over all probability measures $\mu\in \Pi(P,Q)$ and when the measurable space $(\mathcal{X},\mathcal{F})$ is Polish, it can be achieved by a maximal coupling. The existence of a maximal coupling illustrates the close connection between the total variation distance and coupling.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set
open Ch8BernoulliBoolCore
open scoped ENNReal

noncomputable section

lemma oneThird_le_one : ((1 : NNReal) / 3) ≤ 1 := by
  exact_mod_cast (show (1 : ℝ) / 3 ≤ 1 by norm_num)

lemma threeQuarters_le_one : ((3 : NNReal) / 4) ≤ 1 := by
  exact_mod_cast (show (3 : ℝ) / 4 ≤ 1 by norm_num)

noncomputable def ex844PPMF : PMF Bool :=
  PMF.bernoulli ((1 : NNReal) / 3) oneThird_le_one

noncomputable def ex844QPMF : PMF Bool :=
  PMF.bernoulli ((3 : NNReal) / 4) threeQuarters_le_one

noncomputable def ex844PMeasure : Measure Bool := ex844PPMF.toMeasure

noncomputable def ex844QMeasure : Measure Bool := ex844QPMF.toMeasure

lemma ex844PPMF_eq_bernoulli :
    ex844PPMF = PMF.bernoulli ((1 : NNReal) / 3) oneThird_le_one := by
  rfl

lemma ex844QPMF_eq_bernoulli :
    ex844QPMF = PMF.bernoulli ((3 : NNReal) / 4) threeQuarters_le_one := by
  rfl

noncomputable def ex844JointWeight (p : Bool × Bool) : ℝ≥0∞ :=
  match p with
  | (true, true) => (1 : ℝ≥0∞) / 3
  | (true, false) => 0
  | (false, true) => (5 : ℝ≥0∞) / 12
  | (false, false) => (1 : ℝ≥0∞) / 4

noncomputable def ex844JointPMF : PMF (Bool × Bool) :=
  PMF.ofFintype ex844JointWeight (by
    rw [Fintype.sum_prod_type]
    repeat rw [Fintype.sum_bool]
    have h :
        (1 : ℝ≥0∞) / 3 + ((5 : ℝ≥0∞) / 12 + (1 : ℝ≥0∞) / 4) = 1 := by
      have h13 : (1 : ℝ≥0∞) / 3 ≠ ∞ := ENNReal.div_ne_top (by simp) (by norm_num)
      have h512 : (5 : ℝ≥0∞) / 12 ≠ ∞ := ENNReal.div_ne_top (by simp) (by norm_num)
      have h14 : (1 : ℝ≥0∞) / 4 ≠ ∞ := ENNReal.div_ne_top (by simp) (by norm_num)
      have hinner : (5 : ℝ≥0∞) / 12 + (1 : ℝ≥0∞) / 4 ≠ ∞ :=
        ENNReal.add_ne_top.2 ⟨h512, h14⟩
      have hleft :
          (1 : ℝ≥0∞) / 3 + ((5 : ℝ≥0∞) / 12 + (1 : ℝ≥0∞) / 4) ≠ ∞ :=
        ENNReal.add_ne_top.2 ⟨h13, hinner⟩
      apply (ENNReal.toReal_eq_toReal_iff' hleft (by simp)).1
      rw [ENNReal.toReal_add h13 hinner, ENNReal.toReal_div,
        ENNReal.toReal_add h512 h14, ENNReal.toReal_div, ENNReal.toReal_div]
      norm_num
    simpa [ex844JointWeight] using h)

lemma ex844JointPMF_map_fst :
    ex844JointPMF.map Prod.fst = ex844PPMF := by
  ext b
  cases b <;> rw [PMF.map_apply]
  · norm_num [ex844JointPMF, ex844JointWeight, ex844PPMF, PMF.ofFintype_apply,
      PMF.bernoulli_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool]
    have h : (5 : ℝ≥0∞) / 12 + (1 : ℝ≥0∞) / 4 = 1 - (1 : ℝ≥0∞) / 3 := by
      have h512 : (5 : ℝ≥0∞) / 12 ≠ ∞ := ENNReal.div_ne_top (by simp) (by norm_num)
      have h14 : (1 : ℝ≥0∞) / 4 ≠ ∞ := ENNReal.div_ne_top (by simp) (by norm_num)
      have hleft : (5 : ℝ≥0∞) / 12 + (1 : ℝ≥0∞) / 4 ≠ ∞ :=
        ENNReal.add_ne_top.2 ⟨h512, h14⟩
      apply (ENNReal.toReal_eq_toReal_iff' hleft (by simp)).1
      rw [ENNReal.toReal_add h512 h14, ENNReal.toReal_div, ENNReal.toReal_div,
        ENNReal.toReal_sub_of_le]
      · norm_num
      · norm_num
      · simp
    simpa using h
  · norm_num [ex844JointPMF, ex844JointWeight, ex844PPMF, PMF.ofFintype_apply,
      PMF.bernoulli_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool]

lemma ex844JointPMF_map_snd :
    ex844JointPMF.map Prod.snd = ex844QPMF := by
  ext b
  cases b <;> rw [PMF.map_apply]
  · norm_num [ex844JointPMF, ex844JointWeight, ex844QPMF, PMF.ofFintype_apply,
      PMF.bernoulli_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool]
    have h : (1 : ℝ≥0∞) / 4 = 1 - (3 : ℝ≥0∞) / 4 := by
      have h14 : (1 : ℝ≥0∞) / 4 ≠ ∞ := ENNReal.div_ne_top (by simp) (by norm_num)
      have h34 : (3 : ℝ≥0∞) / 4 ≠ ∞ := ENNReal.div_ne_top (by simp) (by norm_num)
      apply (ENNReal.toReal_eq_toReal_iff' h14 (by simp)).1
      rw [ENNReal.toReal_div, ENNReal.toReal_sub_of_le]
      · norm_num
      · exact (ENNReal.toReal_le_toReal h34 (by simp)).1 (by rw [ENNReal.toReal_div]; norm_num)
      · simp
    simpa using h
  · norm_num [ex844JointPMF, ex844JointWeight, ex844QPMF, PMF.ofFintype_apply,
      PMF.bernoulli_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool]
    have h : (1 : ℝ≥0∞) / 3 + (5 : ℝ≥0∞) / 12 = (3 : ℝ≥0∞) / 4 := by
      have h13 : (1 : ℝ≥0∞) / 3 ≠ ∞ := ENNReal.div_ne_top (by simp) (by norm_num)
      have h512 : (5 : ℝ≥0∞) / 12 ≠ ∞ := ENNReal.div_ne_top (by simp) (by norm_num)
      have h34 : (3 : ℝ≥0∞) / 4 ≠ ∞ := ENNReal.div_ne_top (by simp) (by norm_num)
      have hleft : (1 : ℝ≥0∞) / 3 + (5 : ℝ≥0∞) / 12 ≠ ∞ :=
        ENNReal.add_ne_top.2 ⟨h13, h512⟩
      apply (ENNReal.toReal_eq_toReal_iff' hleft h34).1
      rw [ENNReal.toReal_add h13 h512, ENNReal.toReal_div, ENNReal.toReal_div,
        ENNReal.toReal_div]
      norm_num
    simpa using h

lemma ex844JointPMF_mismatch :
    ex844JointPMF.toMeasure {p : Bool × Bool | p.1 ≠ p.2} = 5 / 12 := by
  have hset :
      {p : Bool × Bool | p.1 ≠ p.2} =
        (({(true, false), (false, true)} : Finset (Bool × Bool)) : Set (Bool × Bool)) := by
    ext p
    cases p with
    | mk a b =>
        cases a <;> cases b <;> simp
  rw [hset, PMF.toMeasure_apply_finset]
  norm_num [ex844JointPMF, ex844JointWeight, PMF.ofFintype_apply,
    Fintype.sum_prod_type, Fintype.sum_bool]

/-- Example 8.4.4: the explicit 2×2 coupling has the correct marginals, mismatch probability
`5/12`, and therefore realizes the total variation distance. -/
theorem ex_8_4_4 :
    ex844JointPMF.map Prod.fst = ex844PPMF ∧
      ex844JointPMF.map Prod.snd = ex844QPMF ∧
      ex844JointPMF.toMeasure {p : Bool × Bool | p.1 ≠ p.2} = 5 / 12 ∧
      totalVariationDistance ex844PMeasure ex844QMeasure = 5 / 12 := by
  refine ⟨ex844JointPMF_map_fst, ex844JointPMF_map_snd, ex844JointPMF_mismatch, ?_⟩
  calc
    totalVariationDistance ex844PMeasure ex844QMeasure
        = |(1 : ℝ) / 3 - 3 / 4| := by
            simpa [ex844PMeasure, ex844QMeasure, ex844PPMF_eq_bernoulli, ex844QPMF_eq_bernoulli] using
              boolBernoulli_totalVariationDistance_eq_abs ((1 : NNReal) / 3) ((3 : NNReal) / 4)
                oneThird_le_one threeQuarters_le_one
    _ = 5 / 12 := by norm_num
