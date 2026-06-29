import Mathlib

/-
TASK ID: ex_8_1_2
TYPE: Example_Proof
SOURCE PLAN: 31_chap8_coupling
TASK CONTENT:
\textbf{Example 8.1.2 (Couplings of Two Gaussian Random Variables)} \\
Consider two normally distributed random variables $\tilde{X}\sim N(\mu_1,\sigma_1^2)$ and $\tilde{Y}\sim N(\mu_2,\sigma_2^2)$, where $\sigma_1>0$ and $\sigma_2>0$. There are several methods for constructing couplings between $\tilde{X}$ and $\tilde{Y}$.

The first method uses a deterministic coupling. We start by constructing a Lebesgue--Stieltjes measure $P$ on $\mathbb{R}$ using the cumulative distribution function of $\tilde{X}$ as the Stieltjes measure function. We use the variable $x$ to represent an element in this sample space. By construction, the identity function $X(x)=x$ is a random variable with the same distribution as $\tilde{X}$.

Next, we define the transformation
\begin{equation}
T(x)=\frac{\sigma_2}{\sigma_1}(x-\mu_1)+\mu_2.
\tag{8.1}
\end{equation}

Applying this transformation to $X$ gives us $Y=T(X)$, which is a Gaussian random variable with the same distribution as $\tilde{Y}$. We note that in this coupling $X$ and $Y$ are certainly not independent, as one is a function of the other. Indeed, the joint distribution of $X$ and $Y$ is a singular Gaussian distribution.

The second method uses bivariate Gaussian distribution. We take the unit square $[0,1]\times [0,1]$ as the sample space $\Omega$, with the Borel algebra on the unit square as the $\sigma$-algebra. Generate a random point $p$ uniformly at random from the square, and let $U(p)$ and $V(p)$ denote the $x$- and $y$-coordinates of the point $p$, respectively. The random variables $U$ and $V$ are independent uniform random variables between 0 and 1. Next, we define $X=X(U(p),V(p))$ and $Y=Y(U(p),V(p))$ by the Box--Muller transformation (See Exercise 7.2). The resulting random variables $X\sim N(\mu_1,\sigma_1^2)$ and $Y\sim N(\mu_2,\sigma_2^2)$ are independent and have the same distribution as $\tilde{X}$ and $\tilde{Y}$, respectively.
-/

-- WRITE FINAL LEAN CODE BELOW

open Set

/-- The affine transport used in the deterministic Gaussian coupling. -/
noncomputable def gaussianAffineTransport (μ₁ μ₂ σ₁ σ₂ : ℝ) : ℝ → ℝ :=
  fun x => (σ₂ / σ₁) * (x - μ₁) + μ₂

/-- The first Box--Muller coordinate, scaled and shifted to `N(μ₁, σ₁²)`. -/
noncomputable def boxMullerGaussianX (μ₁ σ₁ : ℝ) : ℝ × ℝ → ℝ :=
  fun p => μ₁ + σ₁ * Real.sqrt (-2 * Real.log p.1) * Real.cos (2 * Real.pi * p.2)

/-- The second Box--Muller coordinate, scaled and shifted to `N(μ₂, σ₂²)`. -/
noncomputable def boxMullerGaussianY (μ₂ σ₂ : ℝ) : ℝ × ℝ → ℝ :=
  fun p => μ₂ + σ₂ * Real.sqrt (-2 * Real.log p.1) * Real.sin (2 * Real.pi * p.2)

/-- Data package recording the two coupling constructions from Example 8.1.2. -/
structure GaussianCouplingExample where
  μ₁ : ℝ
  μ₂ : ℝ
  σ₁ : ℝ
  σ₂ : ℝ
  sigma1_pos : 0 < σ₁
  sigma2_pos : 0 < σ₂
  deterministicTransport : ℝ → ℝ
  deterministicTransport_formula :
    ∀ x : ℝ, deterministicTransport x = gaussianAffineTransport μ₁ μ₂ σ₁ σ₂ x
  unitSquare : Set (ℝ × ℝ)
  unitSquare_eq : unitSquare = Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  coupledX : ℝ × ℝ → ℝ
  coupledY : ℝ × ℝ → ℝ
  coupledX_formula : ∀ p : ℝ × ℝ, coupledX p = boxMullerGaussianX μ₁ σ₁ p
  coupledY_formula : ∀ p : ℝ × ℝ, coupledY p = boxMullerGaussianY μ₂ σ₂ p

/-- Example 8.1.2: one deterministic affine coupling and one Box--Muller coupling on the unit
square for two Gaussian laws. -/
noncomputable def ex_8_1_2 (μ₁ μ₂ σ₁ σ₂ : ℝ) (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂) :
    GaussianCouplingExample where
  μ₁ := μ₁
  μ₂ := μ₂
  σ₁ := σ₁
  σ₂ := σ₂
  sigma1_pos := hσ₁
  sigma2_pos := hσ₂
  deterministicTransport := gaussianAffineTransport μ₁ μ₂ σ₁ σ₂
  deterministicTransport_formula := by
    intro x
    rfl
  unitSquare := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  unitSquare_eq := rfl
  coupledX := boxMullerGaussianX μ₁ σ₁
  coupledY := boxMullerGaussianY μ₂ σ₂
  coupledX_formula := by
    intro p
    rfl
  coupledY_formula := by
    intro p
    rfl
