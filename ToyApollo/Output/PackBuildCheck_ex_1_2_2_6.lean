import Mathlib

/-
TASK ID: ex_1_2_2
TYPE: Example_Proof
SOURCE PLAN: 37_chap1_mixed_singular
TASK CONTENT:
\textbf{Example 1.2.2 (Dirichlet Distribution)} \\
Consider a positive constant $\beta$ and $n$ positive constants $\alpha_1,\dots,\alpha_n$. For $i=1,2,\dots,n$, let $X_i$ be independent Gamma distributed random variables with shape parameter $\alpha_i$ and scale parameter $\beta$, which we denote by $\Gamma(\alpha_i,\beta)$. The pdf of $X_i$ is given by (1.2).

Define
\[
V\triangleq X_1+X_2+\cdots +X_n
\]
as the sum of these Gamma random variables. The components of the random vector
\[
\mathbf{Y}=(Y_1,Y_2,\dots,Y_n)\triangleq (X_1/V,X_2/V,\dots,X_n/V)
\]
are distributed according to the Dirichlet distribution with parameters $\alpha_1,\dots,\alpha_n$. The random vector $\mathbf{Y}$ lies in the region defined by $y_1+y_2+\cdots +y_n=1$ and $y_i\ge 0$ for all $i$ with probability $1$. The Dirichlet distribution is singular because this region has zero volume in $\mathbb{R}^n$. A sample scatter plot is shown in Fig. 1.2.

\textbf{Figure 1.2.} A scatter plot of Dirichlet distribution in Example 1.2.2, with parameters $\alpha_1=\alpha_3=1$ and $\alpha_2=2$. All sample points are on the plane $x+y+z=1$.

The Dirichlet distribution plays a prominent role in the method of latent Dirichlet allocation, a popular technique in natural language processing. Although the Dirichlet distribution does not have a pdf, we can project the random variables to an $(n-1)$-dimensional subspace and describe the probability distribution in the lower-dimensional space. Since the $n$ random values must sum to $1$, we can consider the first $n-1$ components only. The pdf of $Y_1,\dots,Y_{n-1}$ is given by
\begin{equation}
f(y_1,\dots,y_{n-1})
=
\frac{\Gamma(\alpha_1+\cdots +\alpha_n)}{\prod_{k=1}^{n}\Gamma(\alpha_k)}
\left(\prod_{k=1}^{n-1} y_k^{\alpha_k-1}\right)
(1-y_1-\cdots -y_{n-1})^{\alpha_n-1},
\tag{1.4}
\end{equation}
for $(y_1,y_2,\dots,y_{n-1})$ with $y_1+y_2+\cdots +y_{n-1}\le 1$ and $y_k\ge 0$ for $k=1,\dots,n-1$. We can compute probabilities pertaining to this distribution using this lower-dimensional pdf. When $n=2$, the pdf of $Y_1$ reduces to a Beta distribution,
\[
f(y)=
\frac{\Gamma(\alpha_1+\alpha_2)}{\Gamma(\alpha_1)\Gamma(\alpha_2)}
y^{\alpha_1-1}(1-y)^{\alpha_2-1}
\]
for $0\le y\le 1$.

In Python, we can use the \texttt{dirichlet} function in the \texttt{numpy.random} module to generate a Dirichlet-distributed random vector. The following is an example of drawing a number of samples from a Dirichlet distribution with parameters $(1,1,2)$ using the default random number generator.
\begin{verbatim}
from numpy import random
rng = random.default_rng()      # default random number generator
X = rng.dirichlet((1, 1, 2), 8) # draw 8 samples
print(X)                        # print the random samples as an array
\end{verbatim}

A sample run of this program yields the following output:
\begin{verbatim}
[[0.1844921  0.51764633 0.29786156]
 [0.1943196  0.18637496 0.61930544]
 [0.06687522 0.28048234 0.65264245]
 [0.50722478 0.14452905 0.34824617]
 [0.22316573 0.05919519 0.71763908]
 [0.28439455 0.22016395 0.4954415 ]
 [0.18963489 0.13846004 0.67190507]
 [0.20121907 0.28116356 0.51761736]]
\end{verbatim}

Each row of this array represents a sample from the Dirichlet distribution. Note that the sum of the numbers in each row is equal to $1$, as required by the Dirichlet distribution. In this example, we observe that the third component of each sample is often the largest, due to its high weight in the parameter vector $(1,1,2)$.

In each of the previous examples, there are sets with zero length or area that occur with strictly positive probability. As a result, the probability distributions associated with these examples cannot be represented by probability density functions.

We formally define a singular random variable as follows.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Sum of the positive Gamma variables before normalization. -/
def ex122GammaTotal {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, x i

/-- The simplex where the normalized Dirichlet vector lives. -/
def ex122DirichletSimplex (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) = 1}

/-- The simplex is contained in the affine hyperplane whose coordinates sum to one,
so it has zero ambient volume. -/
theorem ex122DirichletSimplex_volume_zero (n : ℕ) :
    (volume : Measure (Fin (n + 1) → ℝ)) (ex122DirichletSimplex n) = 0 := by
  refine measure_mono_null ?_
    (Measure.addHaar_affineSubspace volume (fintypeAffineCoords (Fin (n + 1)) ℝ) ?_)
  · intro y hy
    exact (mem_fintypeAffineCoords_iff_sum).2 hy.2
  · intro htop
    have hzero_mem :
        (0 : Fin (n + 1) → ℝ) ∈ (⊤ : AffineSubspace ℝ (Fin (n + 1) → ℝ)) := by
      simp
    have hzero_mem' :
        (0 : Fin (n + 1) → ℝ) ∈ fintypeAffineCoords (Fin (n + 1)) ℝ := by
      simpa [htop] using hzero_mem
    have hsum : (∑ i : Fin (n + 1), (0 : Fin (n + 1) → ℝ) i) = (1 : ℝ) :=
      (mem_fintypeAffineCoords_iff_sum).1 hzero_mem'
    simp at hsum

/-- The Dirichlet normalization map `Y_i = X_i / (∑ j, X_j)`. -/
def ex122NormalizedVector {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i / ex122GammaTotal x

theorem ex122_normalized_sum {n : ℕ} (x : Fin n → ℝ) (hV : ex122GammaTotal x ≠ 0) :
    (∑ i, ex122NormalizedVector x i) = 1 := by
  calc
    (∑ i, ex122NormalizedVector x i) = (∑ i, x i) / ex122GammaTotal x := by
      simp [ex122NormalizedVector, Finset.sum_div]
    _ = 1 := by
      have hsum : (∑ i, x i) ≠ 0 := by simpa [ex122GammaTotal] using hV
      simp [ex122GammaTotal, div_self hsum]

theorem ex122_normalized_nonneg {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hV : 0 < ex122GammaTotal x) :
    ∀ i, 0 ≤ ex122NormalizedVector x i := by
  intro i
  exact div_nonneg (hx i) hV.le

theorem ex122_normalized_mem_simplex {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hV : 0 < ex122GammaTotal x) :
    ex122NormalizedVector x ∈ ex122DirichletSimplex n := by
  refine ⟨ex122_normalized_nonneg x hx hV, ?_⟩
  exact ex122_normalized_sum x (ne_of_gt hV)

/-- Last coordinate after projecting the Dirichlet simplex to the first `n` coordinates. -/
def ex122ProjectedLastCoord {n : ℕ} (y : Fin n → ℝ) : ℝ := 1 - ∑ i, y i

/-- Normalizing constant in the projected Dirichlet density formula. -/
def ex122DirichletNormalizer {n : ℕ} (α : Fin (n + 1) → ℝ) : ℝ :=
  Real.Gamma (∑ i, α i) / ∏ i, Real.Gamma (α i)

/-- The lower-dimensional Dirichlet density on the first `n` coordinates. -/
def ex122DirichletProjectedDensity {n : ℕ} (α : Fin (n + 1) → ℝ)
    (y : Fin n → ℝ) : ℝ :=
  ex122DirichletNormalizer α *
    (∏ i : Fin n, (y i) ^ (α (Fin.castSucc i) - 1)) *
      (ex122ProjectedLastCoord y) ^ (α (Fin.last n) - 1)

theorem ex122_dirichletProjectedDensity_formula {n : ℕ} (α : Fin (n + 1) → ℝ)
    (y : Fin n → ℝ) :
    ex122DirichletProjectedDensity α y =
      ex122DirichletNormalizer α *
        (∏ i : Fin n, (y i) ^ (α (Fin.castSucc i) - 1)) *
          (ex122ProjectedLastCoord y) ^ (α (Fin.last n) - 1) := rfl

/-- The `n = 2` special case, i.e. the Beta density formula. -/
def ex122BetaDensity (α₁ α₂ y : ℝ) : ℝ :=
  Real.Gamma (α₁ + α₂) / (Real.Gamma α₁ * Real.Gamma α₂) *
    y ^ (α₁ - 1) * (1 - y) ^ (α₂ - 1)

theorem ex122_beta_density_formula (α₁ α₂ y : ℝ) :
    ex122BetaDensity α₁ α₂ y =
      Real.Gamma (α₁ + α₂) / (Real.Gamma α₁ * Real.Gamma α₂) *
        y ^ (α₁ - 1) * (1 - y) ^ (α₂ - 1) := rfl

/-- The theorem-backed package for Example 1.2.2. -/
structure DirichletExample where
  parameter_count : ℕ
  simplex : Set (Fin parameter_count → ℝ)
  projectedDensity : (Fin (parameter_count - 1) → ℝ) → ℝ
  betaDensity : ℝ → ℝ
  normalized_mem_simplex :
    ∀ x : Fin parameter_count → ℝ,
      (∀ i, 0 ≤ x i) →
      0 < ex122GammaTotal x →
      ex122NormalizedVector x ∈ simplex
  simplex_volume_zero :
    (volume : Measure (Fin parameter_count → ℝ)) simplex = 0

/-- Exported declaration for Example 1.2.2, specialized to the displayed `(1,1,2)` sample. -/
def ex_1_2_2 : DirichletExample where
  parameter_count := 3
  simplex := ex122DirichletSimplex 2
  projectedDensity := ex122DirichletProjectedDensity
    (fun i : Fin 3 =>
      if i = 0 then (1 : ℝ) else if i = 1 then (1 : ℝ) else (2 : ℝ))
  betaDensity := ex122BetaDensity 1 1
  normalized_mem_simplex := by
    intro x hx hV
    exact ex122_normalized_mem_simplex x hx hV
  simplex_volume_zero := ex122DirichletSimplex_volume_zero 2
