import Mathlib
import ToyApollo.Output.thm_11_1

/-
TASK ID: def_12_1
TYPE: Definition
SOURCE PLAN: chapter12-l2-norm-inner-product
TASK CONTENT:
\begin{defbox}{12.1}
\end{defbox}

Given a measure space (\Omega, \mathcal{F},\mu ), we denote the set of all \mathcal{F}-measurable

functions X with finite second moment by L2(\mu)More generally, for any

positive integer p, we define Lp (\mu) as the set of all \mathcal{F}-measurable functions

with finite

\int

\vertX\vertp d\mu.

In this chapter, we will focus on the study of L2(P) for a probability measure P .

We note that any square-integrable random variable necessarily has a finite mean,

implying that L2(P) is a subset of L1(P) Using Cauchy-Schwarz inequality

(Theorem 11.1), we can define an inner product for two square-integrable random

variables.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory
open scoped InnerProductSpace

/-- Textbook `L^p(μ)` membership for real random variables, kept as a
predicate on raw functions so it composes with the earlier random-variable and
expectation outputs. -/
def LpFunction {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ENNReal) (X : Ω → ℝ) : Prop :=
  MemLp X p μ

/-- The same `L^p` membership indexed by a natural exponent, matching the
chapter's "positive integer p" wording. -/
def LpFunctionNat {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℕ) (hp : 0 < p) (X : Ω → ℝ) : Prop :=
  LpFunction μ (p : ENNReal) X

/-- Textbook `L²(μ)`: measurable real functions with finite second moment. -/
def L2Function {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  LpFunction μ (2 : ENNReal) X

/-- Move a raw square-integrable random variable into Mathlib's a.e.-quotiented
`L²` Hilbert-space object when Hilbert-space tools are needed. -/
noncomputable def L2Function.toLp {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : L2Function μ X) : Ω →₂[μ] ℝ :=
  (show MemLp X (2 : ENNReal) μ from hX).toLp X

/-- On a finite measure space, and hence on a probability space, `L²` membership
implies `L¹` membership. -/
theorem L2Function.memLp_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : L2Function μ X) :
    LpFunction μ (1 : ENNReal) X := by
  exact (show MemLp X (2 : ENNReal) μ from hX).mono_exponent (by norm_num)

/-- The previous statement in the textbook's integrability language. -/
theorem L2Function.integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : L2Function μ X) :
    Integrable X μ := by
  exact (show MemLp X (2 : ENNReal) μ from hX).integrable (by norm_num)

/-- Cauchy-Schwarz for the a.e.-quotiented `L²` representatives associated
to raw square-integrable functions.  This is the Chapter 11 theorem landing
used by the product-integrability bridge below. -/
theorem L2Function.cauchySchwarz_inner_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X Y : Ω → ℝ}
    (hX : L2Function μ X) (hY : L2Function μ Y) :
    ‖⟪L2Function.toLp hX, L2Function.toLp hY⟫_ℝ‖ ≤
      ‖L2Function.toLp hX‖ * ‖L2Function.toLp hY‖ := by
  exact thm_11_1 (L2Function.toLp hX) (L2Function.toLp hY)

/-- The Cauchy-Schwarz support needed before Definition 12.2 can form
`E[XY]`: the quotient-space Cauchy-Schwarz bound from Theorem 11.1 together
with the product-integrability step for raw representatives. -/
structure L2Function.CauchySchwarzProductSupport {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X Y : Ω → ℝ}
    (hX : L2Function μ X) (hY : L2Function μ Y) : Prop where
  inner_bound :
    ‖⟪L2Function.toLp hX, L2Function.toLp hY⟫_ℝ‖ ≤
      ‖L2Function.toLp hX‖ * ‖L2Function.toLp hY‖
  product_integrable : Integrable (fun ω => X ω * Y ω) μ

/-- The theorem-level Cauchy-Schwarz support bridge for raw `L²` functions. -/
theorem L2Function.cauchySchwarz_product_support {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} (hX : L2Function μ X) (hY : L2Function μ Y) :
    L2Function.CauchySchwarzProductSupport hX hY := by
  have hX2 : Integrable (fun ω => ‖X ω‖ ^ (2 : ℕ)) μ := by
    exact MemLp.integrable_norm_pow
      (show MemLp X ((2 : ℕ) : ENNReal) μ from by simpa using hX)
      (by norm_num)
  have hY2 : Integrable (fun ω => ‖Y ω‖ ^ (2 : ℕ)) μ := by
    exact MemLp.integrable_norm_pow
      (show MemLp Y ((2 : ℕ) : ENNReal) μ from by simpa using hY)
      (by norm_num)
  have hquad :
      Integrable
        (fun ω => (‖X ω‖ ^ (2 : ℕ) + ‖Y ω‖ ^ (2 : ℕ)) / (2 : ℝ)) μ :=
    (hX2.add hY2).div_const 2
  have hmeas : AEStronglyMeasurable (fun ω => X ω * Y ω) μ :=
    (show MemLp X (2 : ENNReal) μ from hX).aestronglyMeasurable.mul
      (show MemLp Y (2 : ENNReal) μ from hY).aestronglyMeasurable
  have hintegrable : Integrable (fun ω => X ω * Y ω) μ := by
    refine Integrable.mono' hquad hmeas ?_
    filter_upwards with ω
    have hineq :
        ‖X ω‖ * ‖Y ω‖ ≤
          (‖X ω‖ ^ (2 : ℕ) + ‖Y ω‖ ^ (2 : ℕ)) / (2 : ℝ) := by
      nlinarith [sq_nonneg (‖X ω‖ - ‖Y ω‖)]
    simpa [norm_mul] using hineq
  exact
    { inner_bound := L2Function.cauchySchwarz_inner_bound hX hY
      product_integrable := hintegrable }

/-- Cauchy-Schwarz supplies integrability of the product of two `L²` functions,
which is the bridge needed to define the `L²` inner product in Definition 12.2. -/
theorem L2Function.integrable_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} (hX : L2Function μ X) (hY : L2Function μ Y) :
    Integrable (fun ω => X ω * Y ω) μ :=
  (L2Function.cauchySchwarz_product_support hX hY).product_integrable

/-- Exported definition for Definition 12.1. -/
def def_12_1 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℕ) (hp : 0 < p) (X : Ω → ℝ) : Prop :=
  LpFunctionNat μ p hp X
