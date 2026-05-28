import Mathlib
import ToyApollo.Phase2.DensityIntegralBridge
import ToyApollo.Phase2.VectorMeasureBorelBridge

/-
TASK ID: thm_13_14
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-continuous-random-variable
TASK CONTENT:
\begin{thmbox}{13.14}
\end{thmbox}

Suppose .(R2,\mathcal{B}(R2), P) is a probability space on R2, and X and Y denote

the x - and y -coordinates, respectively. Let g(x) denote a Borel function in

L1(P) .

Suppose the joint probability density function of X and Y is denoted by

fXY (x, y), ie., for any Borel set B in\mathcal{B}(R2), we have

P(B) =

\int

B

fXY (x,y)d\lambda(x,y),

where. \lambda is the Lebesgue measure on R2. Then, we have

E[g(X)\vertY]=

\int

R

g(x)fX\vertY (x\verty) d\lambda(x), (13.13)

where

fX\vertY (x\verty)\coloneqq fXY (x, y)

fY (y)

and

fY (y)\coloneqq

\int

R

fXY (x, y) d\lambda(x). (13.14)

In particular , if X is integrable, we can compute the conditional expecta-

tionE[X\vertY] by

E[X\vertY]=

\int

R

xfX\vertY (x, y) d\lambda(y).

We may assumefY (y)/=0 for simplicity so that we do not need to worry about

division by zero. We note that the conditional expectation E[g(X)\vertY] in (13.13) is

a\sigma(Y) -measurable function and hence is a function of y .

\textit{Proof} Let h(y)=

\int

R g(x)fX\vertY (x\verty)d\lambda(x) be the candidate function for the

conditional expectation. Our goal is to prove that, for any \sigma(Y) -measurable set B ,

the following equation holds:

\int

B

g(x)dP(x,y) =

\int

B

h(y) dP(x, y). (13.15)

Consider a special type of \sigma(Y) -measurable set of the form B= R \times[ a,b] for

some a<b Assuming we can apply Fubini's theorem to evaluate the integrals by

iterated integration, we will show that Eq. (13.15) holds for this type of set. When

B is of the form R\times[ a,b], we can express the right-hand side of (13.15) as

\int

[a,b]

\int

R

h(y)fXY (x, y) d\lambda(x)d\lambda(y)=

\int

[a,b]

h(y)

\int

R

fXY (x, y) d\lambda(x)d\lambda(y)

=

\int

[a,b]

h(y)fY (y) d\lambda(y)

=

\int

[a,b]

\int

R

g(x)fXY (x, y) d\lambda(x)d\lambda(y).

The last line is the same as the left-hand side of (13.15).

We can justify the application of Fubini's theorem by assuming that \vertg(x)\vert is

integrable, as

\int

R\times[a,b]

\vertg(x)\vertfXY (x,y)d\lambda(x,y) \leq

\int

R\timesR

\vertg(x)\vertfXY (x,y)d\lambda(x,y) < \infty .

We obtain the following equation for all closed intervals I in R:

E[g(X) 1R\timesI ]= E[h(Y) 1R\timesI ]. (13.16)

We can extend (13.16) to all Borel sets B\in \mathcal{B} (R) by appealing to the \pi-\lambda

theorem. First, we observe that the collection of all closed intervals in R form a

\pi-system P. Next, we consider the collection L consisting of subsets S of \Omega that

satisfies

E[g(X) 1R\timesS]= E[h(Y) 1R\timesS].

By what we have proved above, we know that P\subset L We can prove that L is

indeed a \lambda-system, which implies that L contains all Borel sets in R. Therefore,

(13.16) holds for all Borel sets B\in \mathcal{B} (R).

Consequently, we have E[g(X) 1C]= E[h(Y) 1C] for all \sigma(Y) -measurable

sets C This implies that h(Y) is indeed a version of the conditional expectation

E[g(X)\vertY] , as it satisfies the defining properties of the conditional expectation. \hfill $\square$

The second part of the theorem establishes the equivalence between the measure-

theoretic definition of conditional expectation and the definition typically presented

in a first course of probability for continuous random variables. By establishing this

equivalence, we demonstrate that the abstract definition of conditional expectation

generalizes the familiar notion from introductory probability theory.

While the classical approach to conditional expectation is well-suited for dealing

with continuous or discrete random variables, it is not capable of handling the case

where we wish to compute the conditional expectation of a discrete random variable

given a continuous random variable, or vice versa. In such cases, the measure-

theoretic definition provides a more general and rigorous framework for defining

conditional expectation.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The x-coordinate random variable on `ℝ × ℝ`. -/
def thm_13_14_X (z : ℝ × ℝ) : ℝ :=
  z.1

/-- The y-coordinate random variable on `ℝ × ℝ`. -/
def thm_13_14_Y (z : ℝ × ℝ) : ℝ :=
  z.2

/-- The statement that `fXY` is a joint density for the probability measure
`P` with respect to two-dimensional Lebesgue measure. -/
def thm_13_14_jointDensityLaw
    (P : Measure (ℝ × ℝ)) (fXY : ℝ × ℝ → ℝ) : Prop :=
  ∀ B : Set (ℝ × ℝ), MeasurableSet B →
    P B = ∫⁻ z in B, ENNReal.ofReal (fXY z) ∂volume

/-- The marginal density `f_Y(y) = ∫ f_{XY}(x,y) dx`. -/
def thm_13_14_marginalDensity (fXY : ℝ × ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ x : ℝ, fXY (x, y) ∂volume

/-- The conditional density `f_{X|Y}(x|y) = f_{XY}(x,y) / f_Y(y)`. -/
def thm_13_14_conditionalDensity
    (fXY : ℝ × ℝ → ℝ) (x y : ℝ) : ℝ :=
  fXY (x, y) / thm_13_14_marginalDensity fXY y

/-- The candidate function
`h(y) = ∫ g(x) f_{X|Y}(x|y) dx`. -/
def thm_13_14_conditionalExpectationKernel
    (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ x : ℝ, g x * thm_13_14_conditionalDensity fXY x y ∂volume

/-- The special case used for `E[X|Y]`. -/
def thm_13_14_identityConditionalExpectationKernel
    (fXY : ℝ × ℝ → ℝ) (y : ℝ) : ℝ :=
  thm_13_14_conditionalExpectationKernel fXY (fun x : ℝ => x) y

/-- The cylinder `ℝ × S`, i.e. a set measurable with respect to the
y-coordinate observation. -/
def thm_13_14_verticalCylinder (S : Set ℝ) : Set (ℝ × ℝ) :=
  {z | z.2 ∈ S}

/-- The closed-interval cylinders used as the generating family in the
textbook proof. -/
def thm_13_14_closedIntervalCylinder (a b : ℝ) : Set (ℝ × ℝ) :=
  thm_13_14_verticalCylinder (Set.Icc a b)

theorem thm_13_14_verticalCylinder_eq_prod (S : Set ℝ) :
    thm_13_14_verticalCylinder S = (Set.univ : Set ℝ) ×ˢ S := by
  ext z
  simp [thm_13_14_verticalCylinder]

theorem thm_13_14_closedIntervalCylinder_eq_prod (a b : ℝ) :
    thm_13_14_closedIntervalCylinder a b =
      (Set.univ : Set ℝ) ×ˢ (Set.Icc a b) := by
  rw [thm_13_14_closedIntervalCylinder, thm_13_14_verticalCylinder_eq_prod]

theorem thm_13_14_verticalCylinder_measurable
    {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurableSet (thm_13_14_verticalCylinder S) := by
  change MeasurableSet (Prod.snd ⁻¹' S)
  exact hS.preimage measurable_snd

theorem thm_13_14_closedIntervalCylinder_measurable (a b : ℝ) :
    MeasurableSet (thm_13_14_closedIntervalCylinder a b) := by
  exact thm_13_14_verticalCylinder_measurable measurableSet_Icc

/-- A set in the sigma-field generated by the y-coordinate, represented as a
vertical cylinder over a Borel set of the y-axis. -/
def thm_13_14_sigmaYMeasurableSet (C : Set (ℝ × ℝ)) : Prop :=
  ∃ S : Set ℝ, MeasurableSet S ∧ C = thm_13_14_verticalCylinder S

/-- Equality of the defining conditional-expectation integrals on a given
set. -/
def thm_13_14_integralIdentity
    (P : Measure (ℝ × ℝ)) (g h : ℝ → ℝ) (C : Set (ℝ × ℝ)) : Prop :=
  (∫ z in C, g z.1 ∂P) = ∫ z in C, h z.2 ∂P

/-- Support for the Fubini computation on closed-interval cylinders
`ℝ × [a,b]`. This is the analytic calculation displayed before (13.16). -/
def thm_13_14_intervalFubiniSupport
    (P : Measure (ℝ × ℝ)) (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, a ≤ b →
    thm_13_14_integralIdentity P g
      (thm_13_14_conditionalExpectationKernel fXY g)
      (thm_13_14_closedIntervalCylinder a b)

/-- Support for the π-λ extension step: if the identity holds on all
closed-interval cylinders, then it holds on every y-cylinder over a Borel set. -/
def thm_13_14_piLambdaExtensionSupport
    (P : Measure (ℝ × ℝ)) (g h : ℝ → ℝ) : Prop :=
  (∀ a b : ℝ, a ≤ b →
    thm_13_14_integralIdentity P g h
      (thm_13_14_closedIntervalCylinder a b)) →
    ∀ S : Set ℝ, MeasurableSet S →
      thm_13_14_integralIdentity P g h
        (thm_13_14_verticalCylinder S)

/-- The defining set-integral criterion for the candidate `h(Y)` to be a
version of `E[g(X)|Y]`, specialized to the coordinate observation `Y`. -/
def thm_13_14_isConditionalExpectationVersion
    (P : Measure (ℝ × ℝ)) (g h : ℝ → ℝ) : Prop :=
  Measurable h ∧
    Integrable (fun z : ℝ × ℝ => g z.1) P ∧
    Integrable (fun z : ℝ × ℝ => h z.2) P ∧
    ∀ C : Set (ℝ × ℝ), thm_13_14_sigmaYMeasurableSet C →
      thm_13_14_integralIdentity P g h C

theorem thm_13_14_marginalDensity_eq
    (fXY : ℝ × ℝ → ℝ) (y : ℝ) :
    thm_13_14_marginalDensity fXY y =
      ∫ x : ℝ, fXY (x, y) ∂volume := by
  rfl

theorem thm_13_14_conditionalDensity_eq
    (fXY : ℝ × ℝ → ℝ) (x y : ℝ) :
    thm_13_14_conditionalDensity fXY x y =
      fXY (x, y) / thm_13_14_marginalDensity fXY y := by
  rfl

/-- The task-local joint-density law is exactly a `withDensity` statement. -/
theorem thm_13_14_measure_eq_withDensity
    (P : Measure (ℝ × ℝ)) (fXY : ℝ × ℝ → ℝ)
    (hDensity : thm_13_14_jointDensityLaw P fXY) :
    P = volume.withDensity (fun z : ℝ × ℝ => ENNReal.ofReal (fXY z)) := by
  exact phase2_measure_eq_withDensity_of_forall_measurable P volume
    (fun z : ℝ × ℝ => ENNReal.ofReal (fXY z)) hDensity

/-- Rewrite set integrals under the joint-density law. -/
theorem thm_13_14_setIntegral_jointDensity_eq
    (P : Measure (ℝ × ℝ)) (fXY : ℝ × ℝ → ℝ) (φ : ℝ × ℝ → ℝ)
    (C : Set (ℝ × ℝ)) (hC : MeasurableSet C)
    (hDensity : thm_13_14_jointDensityLaw P fXY)
    (hDensityAEMeas :
      AEMeasurable (fun z : ℝ × ℝ => ENNReal.ofReal (fXY z)) volume)
    (hDensityNonneg : ∀ᵐ z ∂volume, 0 ≤ fXY z) :
    (∫ z in C, φ z ∂P) = ∫ z in C, fXY z * φ z ∂volume := by
  exact phase2_setIntegral_withDensity_ofReal_eq P volume fXY φ C hC
    (thm_13_14_measure_eq_withDensity P fXY hDensity)
    hDensityAEMeas hDensityNonneg

/-- Weighted integrability under the density gives ordinary integrability
under the probability measure `P`. -/
theorem thm_13_14_integrable_under_jointDensity
    (P : Measure (ℝ × ℝ)) (fXY : ℝ × ℝ → ℝ) (φ : ℝ × ℝ → ℝ)
    (hDensity : thm_13_14_jointDensityLaw P fXY)
    (hDensityAEMeas :
      AEMeasurable (fun z : ℝ × ℝ => ENNReal.ofReal (fXY z)) volume)
    (hDensityNonneg : ∀ᵐ z ∂volume, 0 ≤ fXY z)
    (hWeighted : Integrable (fun z : ℝ × ℝ => fXY z * φ z) volume) :
    Integrable φ P := by
  exact phase2_integrable_withDensity_ofReal_of_weighted P volume fXY φ
    (thm_13_14_measure_eq_withDensity P fXY hDensity)
    hDensityAEMeas hDensityNonneg hWeighted

/-- A probability joint-density law plus nonnegativity gives ordinary
integrability of the density itself. -/
theorem thm_13_14_jointDensity_integrable
    (P : Measure (ℝ × ℝ)) [IsProbabilityMeasure P]
    (fXY : ℝ × ℝ → ℝ)
    (hDensity : thm_13_14_jointDensityLaw P fXY)
    (hDensityAEMeas :
      AEMeasurable (fun z : ℝ × ℝ => ENNReal.ofReal (fXY z)) volume)
    (hDensityNonneg : ∀ᵐ z ∂volume, 0 ≤ fXY z) :
    Integrable fXY volume := by
  have hlin :
      (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (fXY z) ∂volume) ≠ ∞ := by
    have h := hDensity Set.univ MeasurableSet.univ
    rw [Measure.restrict_univ] at h
    rw [← h, IsProbabilityMeasure.measure_univ]
    norm_num
  have hToRealInt := integrable_toReal_of_lintegral_ne_top
    hDensityAEMeas hlin
  refine hToRealInt.congr ?_
  filter_upwards [hDensityNonneg] with z hz
  simp [ENNReal.toReal_ofReal hz]

/-- Fubini on a vertical closed-interval cylinder, with the y-coordinate as
the outer integral. -/
theorem thm_13_14_setIntegral_verticalCylinder_prod_symm
    (F : ℝ × ℝ → ℝ) (a b : ℝ)
    (hInt : IntegrableOn F (thm_13_14_closedIntervalCylinder a b) volume) :
    (∫ z in thm_13_14_closedIntervalCylinder a b, F z ∂volume) =
      ∫ y in Set.Icc a b, ∫ x : ℝ, F (x, y) ∂volume ∂volume := by
  have hInt' : IntegrableOn F ((Set.univ : Set ℝ) ×ˢ Set.Icc a b)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    simpa [thm_13_14_closedIntervalCylinder_eq_prod, Measure.volume_eq_prod] using hInt
  have hInt'' :
      Integrable F
        ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Icc a b))) := by
    rw [IntegrableOn, ← Measure.prod_restrict] at hInt'
    simpa [Measure.restrict_univ] using hInt'
  rw [thm_13_14_closedIntervalCylinder_eq_prod, Measure.volume_eq_prod]
  rw [← Measure.prod_restrict, Measure.restrict_univ]
  exact integral_prod_symm (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ).restrict (Set.Icc a b)) F hInt''

/-- Algebraic kernel identity:
`h(y) fY(y) = ∫ g(x) fXY(x,y) dx`. -/
theorem thm_13_14_kernel_mul_marginal_eq_integral
    (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ) (y : ℝ)
    (hFY_ne_zero : thm_13_14_marginalDensity fXY y ≠ 0) :
    thm_13_14_conditionalExpectationKernel fXY g y *
        thm_13_14_marginalDensity fXY y =
      ∫ x : ℝ, g x * fXY (x, y) ∂volume := by
  unfold thm_13_14_conditionalExpectationKernel thm_13_14_conditionalDensity
  have hfun :
      (fun x : ℝ => g x * (fXY (x, y) / thm_13_14_marginalDensity fXY y)) =
        fun x : ℝ => (g x * fXY (x, y)) /
          thm_13_14_marginalDensity fXY y := by
    funext x
    ring
  rw [hfun, integral_div]
  field_simp [hFY_ne_zero]

/-- Measurability of the textbook candidate
`h(y) = ∫ g(x) f_{X|Y}(x|y) dx`, obtained by rewriting it as a quotient of
fiber integrals. -/
theorem thm_13_14_kernel_stronglyMeasurable
    (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ)
    (hGMeas : Measurable g)
    (hDensityMeas : Measurable fXY) :
    StronglyMeasurable (thm_13_14_conditionalExpectationKernel fXY g) := by
  have hGFStrong : StronglyMeasurable (fun z : ℝ × ℝ => g z.1 * fXY z) :=
    (hGMeas.comp measurable_fst).stronglyMeasurable.mul
      hDensityMeas.stronglyMeasurable
  have hNStrong : StronglyMeasurable
      (fun y : ℝ => ∫ x : ℝ, g x * fXY (x, y) ∂volume) := by
    simpa using hGFStrong.integral_prod_left'
  have hFYStrong : StronglyMeasurable
      (fun y : ℝ => thm_13_14_marginalDensity fXY y) := by
    simpa [thm_13_14_marginalDensity] using
      hDensityMeas.stronglyMeasurable.integral_prod_left'
  have hK_eq :
      thm_13_14_conditionalExpectationKernel fXY g =
        fun y : ℝ =>
          (∫ x : ℝ, g x * fXY (x, y) ∂volume) /
            thm_13_14_marginalDensity fXY y := by
    funext y
    unfold thm_13_14_conditionalExpectationKernel thm_13_14_conditionalDensity
    have hfun :
        (fun x : ℝ => g x * (fXY (x, y) / thm_13_14_marginalDensity fXY y)) =
          fun x : ℝ => (g x * fXY (x, y)) /
            thm_13_14_marginalDensity fXY y := by
      funext x
      ring
    rw [hfun, integral_div]
  rw [hK_eq]
  exact hNStrong.div hFYStrong

/-- The weighted `L¹` assumption for `g(X)` also gives integrability of the
absolute weighted density. This is the first formal step needed for the
textbook kernel-integrability argument. -/
theorem thm_13_14_gWeighted_abs_integrable
    (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ)
    (hDensityNonneg : ∀ z : ℝ × ℝ, 0 ≤ fXY z)
    (hGWeightedInt : Integrable (fun z : ℝ × ℝ => fXY z * g z.1) volume) :
    Integrable (fun z : ℝ × ℝ => |g z.1| * fXY z) volume := by
  refine hGWeightedInt.norm.congr ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hDensityNonneg z)]
  ring

/-- A pointwise nonnegative fiber with a nonzero marginal has positive
marginal density. -/
theorem thm_13_14_marginalDensity_pos_of_nonneg_ne_zero
    (fXY : ℝ × ℝ → ℝ) (y : ℝ)
    (hFiberNonneg : ∀ x : ℝ, 0 ≤ fXY (x, y))
    (hFY_ne_zero : thm_13_14_marginalDensity fXY y ≠ 0) :
    0 < thm_13_14_marginalDensity fXY y := by
  have hnonneg : 0 ≤ thm_13_14_marginalDensity fXY y := by
    unfold thm_13_14_marginalDensity
    exact integral_nonneg hFiberNonneg
  exact lt_of_le_of_ne' hnonneg hFY_ne_zero

/-- Pointwise kernel domination for a fixed `y`: multiplying the conditional
kernel by the marginal density is bounded by the fiberwise absolute
`g`-weighted joint density. Integrating this inequality over `y` is the
remaining analytic step needed to remove the public kernel-weighted
integrability premise. -/
theorem thm_13_14_kernel_abs_mul_marginal_le_integral_abs
    (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ) (y : ℝ)
    (hFiberNonneg : ∀ x : ℝ, 0 ≤ fXY (x, y))
    (hFY_pos : 0 < thm_13_14_marginalDensity fXY y) :
    |thm_13_14_conditionalExpectationKernel fXY g y| *
        thm_13_14_marginalDensity fXY y ≤
      ∫ x : ℝ, |g x| * fXY (x, y) ∂volume := by
  let m : ℝ := thm_13_14_marginalDensity fXY y
  have hm_pos : 0 < m := hFY_pos
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have hnorm := norm_integral_le_integral_norm
    (μ := (volume : Measure ℝ))
    (f := fun x : ℝ => g x * thm_13_14_conditionalDensity fXY x y)
  have hnorm₁ :
      |thm_13_14_conditionalExpectationKernel fXY g y| ≤
        ∫ x : ℝ, |g x| * (|fXY (x, y)| / m) ∂volume := by
    simpa [Real.norm_eq_abs, thm_13_14_conditionalExpectationKernel,
      thm_13_14_conditionalDensity, m, abs_mul, abs_div,
      abs_of_pos hm_pos]
      using hnorm
  have hright :
      (∫ x : ℝ, |g x| * (|fXY (x, y)| / m) ∂volume) =
        ∫ x : ℝ, |g x| * fXY (x, y) / m ∂volume := by
    apply integral_congr_ae
    filter_upwards with x
    rw [abs_of_nonneg (hFiberNonneg x)]
    ring
  have hnorm' :
      |thm_13_14_conditionalExpectationKernel fXY g y| ≤
        ∫ x : ℝ, |g x| * fXY (x, y) / m ∂volume := by
    exact hnorm₁.trans_eq hright
  rw [integral_div] at hnorm'
  have hmul := mul_le_mul_of_nonneg_right hnorm' hm_pos.le
  simpa [div_mul_cancel₀ _ hm_ne, m] using hmul

/-- The textbook Fubini integrability condition for the right-hand side is
derived from the same `|g|`-weighted density integrability used for the
left-hand side. This removes the former public proof-step premise asking for
kernel-weighted integrability directly. -/
theorem thm_13_14_kernelWeighted_integrable_from_gWeighted
    (P : Measure (ℝ × ℝ)) [IsProbabilityMeasure P]
    (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ)
    (hDensity : thm_13_14_jointDensityLaw P fXY)
    (hGMeas : Measurable g)
    (hDensityMeas : Measurable fXY)
    (hDensityNonneg : ∀ z : ℝ × ℝ, 0 ≤ fXY z)
    (hGWeightedInt : Integrable (fun z : ℝ × ℝ => fXY z * g z.1) volume)
    (hFY_ne_zero : ∀ y : ℝ, thm_13_14_marginalDensity fXY y ≠ 0) :
    Integrable
      (fun z : ℝ × ℝ =>
        fXY z * thm_13_14_conditionalExpectationKernel fXY g z.2) volume := by
  let K : ℝ → ℝ := thm_13_14_conditionalExpectationKernel fXY g
  let F : ℝ × ℝ → ℝ := fun z => fXY z * K z.2
  let A : ℝ → ℝ := fun y => ∫ x : ℝ, |g x| * fXY (x, y) ∂volume
  have hDensityAEMeas :
      AEMeasurable (fun z : ℝ × ℝ => ENNReal.ofReal (fXY z)) volume :=
    hDensityMeas.ennreal_ofReal.aemeasurable
  have hDensityNonnegAE : ∀ᵐ z ∂volume, 0 ≤ fXY z :=
    ae_of_all _ hDensityNonneg
  have hfxyInt : Integrable fXY volume :=
    thm_13_14_jointDensity_integrable P fXY hDensity
      hDensityAEMeas hDensityNonnegAE
  have hfxyInt_prod : Integrable fXY
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    simpa [Measure.volume_eq_prod] using hfxyInt
  have hAbsInt : Integrable (fun z : ℝ × ℝ => |g z.1| * fXY z) volume :=
    thm_13_14_gWeighted_abs_integrable fXY g hDensityNonneg hGWeightedInt
  have hAbsInt_prod : Integrable (fun z : ℝ × ℝ => |g z.1| * fXY z)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    simpa [Measure.volume_eq_prod] using hAbsInt
  have hGFStrong : StronglyMeasurable (fun z : ℝ × ℝ => g z.1 * fXY z) :=
    (hGMeas.comp measurable_fst).stronglyMeasurable.mul
      hDensityMeas.stronglyMeasurable
  have hNStrong : StronglyMeasurable
      (fun y : ℝ => ∫ x : ℝ, g x * fXY (x, y) ∂volume) := by
    simpa using hGFStrong.integral_prod_left'
  have hFYStrong : StronglyMeasurable
      (fun y : ℝ => thm_13_14_marginalDensity fXY y) := by
    simpa [thm_13_14_marginalDensity] using
      hDensityMeas.stronglyMeasurable.integral_prod_left'
  have hK_eq :
      K =
        fun y : ℝ =>
          (∫ x : ℝ, g x * fXY (x, y) ∂volume) /
            thm_13_14_marginalDensity fXY y := by
    funext y
    dsimp [K]
    unfold thm_13_14_conditionalExpectationKernel thm_13_14_conditionalDensity
    have hfun :
        (fun x : ℝ => g x * (fXY (x, y) / thm_13_14_marginalDensity fXY y)) =
          fun x : ℝ => (g x * fXY (x, y)) /
            thm_13_14_marginalDensity fXY y := by
      funext x
      ring
    rw [hfun, integral_div]
  have hKStrong : StronglyMeasurable K := by
    rw [hK_eq]
    exact hNStrong.div hFYStrong
  have hFStrong : StronglyMeasurable F := by
    dsimp [F]
    exact hDensityMeas.stronglyMeasurable.mul
      (hKStrong.comp_measurable measurable_snd)
  have hAInt : Integrable A volume := by
    refine hAbsInt_prod.integral_norm_prod_right.congr ?_
    filter_upwards with y
    dsimp [A]
    apply integral_congr_ae
    filter_upwards with x
    rw [abs_mul, abs_of_nonneg (abs_nonneg (g x)),
      abs_of_nonneg (hDensityNonneg (x, y))]
  have hBInt :
      Integrable (fun y : ℝ => ∫ x : ℝ, ‖F (x, y)‖ ∂volume) volume := by
    refine hAInt.mono'
      (hFStrong.norm.integral_prod_left'.aestronglyMeasurable) ?_
    filter_upwards [hfxyInt_prod.prod_left_ae] with y hy
    have hB_nonneg : 0 ≤ ∫ x : ℝ, ‖F (x, y)‖ ∂volume :=
      integral_nonneg (fun x => norm_nonneg _)
    have hB_eq :
        (∫ x : ℝ, ‖F (x, y)‖ ∂volume) =
          |K y| * thm_13_14_marginalDensity fXY y := by
      dsimp [F]
      calc
        (∫ x : ℝ, ‖fXY (x, y) * K y‖ ∂volume)
            = ∫ x : ℝ, |K y| * fXY (x, y) ∂volume := by
              apply integral_congr_ae
              filter_upwards with x
              rw [Real.norm_eq_abs, abs_mul,
                abs_of_nonneg (hDensityNonneg (x, y))]
              ring
        _ = |K y| * ∫ x : ℝ, fXY (x, y) ∂volume := by
              rw [integral_const_mul]
        _ = |K y| * thm_13_14_marginalDensity fXY y := by
              rfl
    have hFY_pos : 0 < thm_13_14_marginalDensity fXY y :=
      thm_13_14_marginalDensity_pos_of_nonneg_ne_zero fXY y
        (fun x : ℝ => hDensityNonneg (x, y)) (hFY_ne_zero y)
    have hdom :
        |K y| * thm_13_14_marginalDensity fXY y ≤ A y := by
      dsimp [K, A]
      exact thm_13_14_kernel_abs_mul_marginal_le_integral_abs
        fXY g y (fun x : ℝ => hDensityNonneg (x, y)) hFY_pos
    rw [Real.norm_eq_abs, abs_of_nonneg hB_nonneg]
    exact hB_eq.trans_le hdom
  have hFib : ∀ᵐ y ∂volume, Integrable (fun x : ℝ => F (x, y)) volume := by
    filter_upwards [hfxyInt_prod.prod_left_ae] with y hy
    dsimp [F]
    exact hy.mul_const (K y)
  have hFInt_prod : Integrable F
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    exact (integrable_prod_iff' hFStrong.aestronglyMeasurable).mpr
      ⟨hFib, hBInt⟩
  simpa [F, Measure.volume_eq_prod] using hFInt_prod

/-- The density-weighted closed-interval calculation after applying Fubini. -/
theorem thm_13_14_interval_weighted_identity
    (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ) (a b : ℝ)
    (hLeftInt : IntegrableOn (fun z : ℝ × ℝ => fXY z * g z.1)
      (thm_13_14_closedIntervalCylinder a b) volume)
    (hRightInt : IntegrableOn
      (fun z : ℝ × ℝ =>
        fXY z * thm_13_14_conditionalExpectationKernel fXY g z.2)
      (thm_13_14_closedIntervalCylinder a b) volume)
    (hFY_ne_zero : ∀ y : ℝ, thm_13_14_marginalDensity fXY y ≠ 0) :
    (∫ z in thm_13_14_closedIntervalCylinder a b, fXY z * g z.1 ∂volume) =
      ∫ z in thm_13_14_closedIntervalCylinder a b,
        fXY z * thm_13_14_conditionalExpectationKernel fXY g z.2 ∂volume := by
  rw [thm_13_14_setIntegral_verticalCylinder_prod_symm _ a b hLeftInt]
  rw [thm_13_14_setIntegral_verticalCylinder_prod_symm _ a b hRightInt]
  apply setIntegral_congr_fun measurableSet_Icc
  intro y _hy
  calc
    (∫ x : ℝ, fXY (x, y) * g x ∂volume)
        = ∫ x : ℝ, g x * fXY (x, y) ∂volume := by
          apply integral_congr_ae
          filter_upwards with x
          ring
    _ = thm_13_14_conditionalExpectationKernel fXY g y *
          thm_13_14_marginalDensity fXY y :=
          (thm_13_14_kernel_mul_marginal_eq_integral
            fXY g y (hFY_ne_zero y)).symm
    _ = (∫ x : ℝ, fXY (x, y) ∂volume) *
          thm_13_14_conditionalExpectationKernel fXY g y := by
          rw [thm_13_14_marginalDensity]
          ring
    _ = ∫ x : ℝ, fXY (x, y) *
          thm_13_14_conditionalExpectationKernel fXY g y ∂volume := by
          rw [integral_mul_const]

/-- The closed-interval Fubini calculation displayed before Eq. (13.16),
proved from explicit density regularity and weighted-integrability
prerequisites. -/
theorem thm_13_14_interval_fubini_from_joint_density
    (P : Measure (ℝ × ℝ)) [IsProbabilityMeasure P]
    (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ)
    (hDensity : thm_13_14_jointDensityLaw P fXY)
    (hDensityAEMeas :
      AEMeasurable (fun z : ℝ × ℝ => ENNReal.ofReal (fXY z)) volume)
    (hDensityNonneg : ∀ᵐ z ∂volume, 0 ≤ fXY z)
    (hGWeightedInt : Integrable (fun z : ℝ × ℝ => fXY z * g z.1) volume)
    (hKernelWeightedInt : Integrable
      (fun z : ℝ × ℝ =>
        fXY z * thm_13_14_conditionalExpectationKernel fXY g z.2) volume)
    (hFY_ne_zero : ∀ y : ℝ, thm_13_14_marginalDensity fXY y ≠ 0) :
    thm_13_14_intervalFubiniSupport P fXY g := by
  intro a b _hab
  unfold thm_13_14_integralIdentity
  rw [thm_13_14_setIntegral_jointDensity_eq P fXY (fun z : ℝ × ℝ => g z.1)
    (thm_13_14_closedIntervalCylinder a b)
    (thm_13_14_closedIntervalCylinder_measurable a b)
    hDensity hDensityAEMeas hDensityNonneg]
  rw [thm_13_14_setIntegral_jointDensity_eq P fXY
    (fun z : ℝ × ℝ => thm_13_14_conditionalExpectationKernel fXY g z.2)
    (thm_13_14_closedIntervalCylinder a b)
    (thm_13_14_closedIntervalCylinder_measurable a b)
    hDensity hDensityAEMeas hDensityNonneg]
  exact thm_13_14_interval_weighted_identity fXY g a b
    hGWeightedInt.integrableOn hKernelWeightedInt.integrableOn hFY_ne_zero

/-- The π-λ/generator extension step from the textbook proof, expressed as a
vector-measure extension over the y-coordinate. The integrability assumptions
are explicit analytic prerequisites for turning set integrals into vector
measures; they are not hidden proof packages. -/
theorem thm_13_14_piLambdaExtensionSupport_from_integrable
    (P : Measure (ℝ × ℝ)) (g h : ℝ → ℝ)
    (hGInt : Integrable (fun z : ℝ × ℝ => g z.1) P)
    (hHInt : Integrable (fun z : ℝ × ℝ => h z.2) P) :
    thm_13_14_piLambdaExtensionSupport P g h := by
  intro hIntervals S hS
  let vG : VectorMeasure ℝ ℝ :=
    (P.withDensityᵥ (fun z : ℝ × ℝ => g z.1)).map Prod.snd
  let vH : VectorMeasure ℝ ℝ :=
    (P.withDensityᵥ (fun z : ℝ × ℝ => h z.2)).map Prod.snd
  have hIcc : ∀ a b : ℝ, a ≤ b → vG (Set.Icc a b) = vH (Set.Icc a b) := by
    intro a b hab
    dsimp [vG, vH]
    rw [VectorMeasure.map_apply
        (v := P.withDensityᵥ (fun z : ℝ × ℝ => g z.1))
        measurable_snd measurableSet_Icc,
      VectorMeasure.map_apply
        (v := P.withDensityᵥ (fun z : ℝ × ℝ => h z.2))
        measurable_snd measurableSet_Icc]
    change (P.withDensityᵥ (fun z : ℝ × ℝ => g z.1))
        (thm_13_14_closedIntervalCylinder a b) =
      (P.withDensityᵥ (fun z : ℝ × ℝ => h z.2))
        (thm_13_14_closedIntervalCylinder a b)
    rw [withDensityᵥ_apply hGInt (thm_13_14_closedIntervalCylinder_measurable a b),
      withDensityᵥ_apply hHInt (thm_13_14_closedIntervalCylinder_measurable a b)]
    exact hIntervals a b hab
  have hvEq : vG = vH := phase2_vectorMeasure_ext_of_Icc vG vH hIcc
  have hvG_S : vG S = ∫ z in thm_13_14_verticalCylinder S, g z.1 ∂P := by
    dsimp [vG]
    rw [VectorMeasure.map_apply
      (v := P.withDensityᵥ (fun z : ℝ × ℝ => g z.1)) measurable_snd hS]
    change (P.withDensityᵥ (fun z : ℝ × ℝ => g z.1))
      (thm_13_14_verticalCylinder S) = _
    exact withDensityᵥ_apply hGInt (thm_13_14_verticalCylinder_measurable hS)
  have hvH_S : vH S = ∫ z in thm_13_14_verticalCylinder S, h z.2 ∂P := by
    dsimp [vH]
    rw [VectorMeasure.map_apply
      (v := P.withDensityᵥ (fun z : ℝ × ℝ => h z.2)) measurable_snd hS]
    change (P.withDensityᵥ (fun z : ℝ × ℝ => h z.2))
      (thm_13_14_verticalCylinder S) = _
    exact withDensityᵥ_apply hHInt (thm_13_14_verticalCylinder_measurable hS)
  exact hvG_S.symm.trans
    ((congrArg (fun v : VectorMeasure ℝ ℝ => v S) hvEq).trans hvH_S)

/-- Final assembly for Theorem 13.14 from the two source proof steps: the
closed-interval Fubini calculation and the π-λ extension to all Borel
y-cylinders. -/
private theorem thm_13_14_from_intervalFubini_piLambda
    (P : Measure (ℝ × ℝ)) [IsProbabilityMeasure P]
    (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ)
    (hDensity : thm_13_14_jointDensityLaw P fXY)
    (hGMeas : Measurable g)
    (hDensityMeas : Measurable fXY)
    (hDensityNonneg : ∀ z : ℝ × ℝ, 0 ≤ fXY z)
    (hGWeightedInt : Integrable (fun z : ℝ × ℝ => fXY z * g z.1) volume)
    (hFY_ne_zero : ∀ y : ℝ, thm_13_14_marginalDensity fXY y ≠ 0) :
    thm_13_14_isConditionalExpectationVersion P g
      (thm_13_14_conditionalExpectationKernel fXY g) := by
  have hDensityAEMeas :
      AEMeasurable (fun z : ℝ × ℝ => ENNReal.ofReal (fXY z)) volume :=
    hDensityMeas.ennreal_ofReal.aemeasurable
  have hDensityNonnegAE : ∀ᵐ z ∂volume, 0 ≤ fXY z :=
    ae_of_all _ hDensityNonneg
  have hKernelMeas : Measurable (thm_13_14_conditionalExpectationKernel fXY g) :=
    (thm_13_14_kernel_stronglyMeasurable fXY g hGMeas hDensityMeas).measurable
  have hKernelWeightedInt : Integrable
      (fun z : ℝ × ℝ =>
        fXY z * thm_13_14_conditionalExpectationKernel fXY g z.2) volume :=
    thm_13_14_kernelWeighted_integrable_from_gWeighted P fXY g
      hDensity hGMeas hDensityMeas hDensityNonneg hGWeightedInt hFY_ne_zero
  have hGInt : Integrable (fun z : ℝ × ℝ => g z.1) P :=
    thm_13_14_integrable_under_jointDensity P fXY (fun z : ℝ × ℝ => g z.1)
      hDensity hDensityAEMeas hDensityNonnegAE hGWeightedInt
  have hKernelInt : Integrable
      (fun z : ℝ × ℝ => thm_13_14_conditionalExpectationKernel fXY g z.2) P :=
    thm_13_14_integrable_under_jointDensity P fXY
      (fun z : ℝ × ℝ => thm_13_14_conditionalExpectationKernel fXY g z.2)
      hDensity hDensityAEMeas hDensityNonnegAE hKernelWeightedInt
  have hIntervals : thm_13_14_intervalFubiniSupport P fXY g :=
    thm_13_14_interval_fubini_from_joint_density P fXY g
      hDensity hDensityAEMeas hDensityNonnegAE hGWeightedInt
      hKernelWeightedInt hFY_ne_zero
  have hExtend : thm_13_14_piLambdaExtensionSupport P g
      (thm_13_14_conditionalExpectationKernel fXY g) :=
    thm_13_14_piLambdaExtensionSupport_from_integrable P g
      (thm_13_14_conditionalExpectationKernel fXY g) hGInt hKernelInt
  refine ⟨hKernelMeas, hGInt, hKernelInt, ?_⟩
  intro C hC
  rcases hC with ⟨S, hS, rfl⟩
  exact hExtend hIntervals S hS

/-- Theorem 13.14: under a source-facing joint-density law, density
measurability/nonnegativity, `g(X)` integrability, and the source's nonzero
marginal simplification, the conditional-density integral is a version of
`E[g(X)|Y]`. The closed-interval Fubini calculation, kernel
measurability/integrability, and the π-λ/generator extension are internal
theorem steps. -/
theorem thm_13_14
    (P : Measure (ℝ × ℝ)) [IsProbabilityMeasure P]
    (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ)
    (hDensity : thm_13_14_jointDensityLaw P fXY)
    (hGMeas : Measurable g)
    (hDensityMeas : Measurable fXY)
    (hDensityNonneg : ∀ z : ℝ × ℝ, 0 ≤ fXY z)
    (hGWeightedInt : Integrable (fun z : ℝ × ℝ => fXY z * g z.1) volume)
    (hFY_ne_zero : ∀ y : ℝ, thm_13_14_marginalDensity fXY y ≠ 0) :
    thm_13_14_isConditionalExpectationVersion P g
      (thm_13_14_conditionalExpectationKernel fXY g) :=
  thm_13_14_from_intervalFubini_piLambda P fXY g
    hDensity hGMeas hDensityMeas hDensityNonneg hGWeightedInt
    hFY_ne_zero

/-- The particular identity case `g(x)=x`, corresponding to the displayed
formula for `E[X|Y]`. -/
theorem thm_13_14_identity
    (P : Measure (ℝ × ℝ)) [IsProbabilityMeasure P]
    (fXY : ℝ × ℝ → ℝ)
    (hDensity : thm_13_14_jointDensityLaw P fXY)
    (hXMeas : Measurable (fun x : ℝ => x))
    (hDensityMeas : Measurable fXY)
    (hDensityNonneg : ∀ z : ℝ × ℝ, 0 ≤ fXY z)
    (hXWeightedInt : Integrable (fun z : ℝ × ℝ => fXY z * z.1) volume)
    (hFY_ne_zero : ∀ y : ℝ, thm_13_14_marginalDensity fXY y ≠ 0) :
    thm_13_14_isConditionalExpectationVersion P (fun x : ℝ => x)
      (thm_13_14_identityConditionalExpectationKernel fXY) :=
  thm_13_14 P fXY (fun x : ℝ => x)
    hDensity hXMeas hDensityMeas hDensityNonneg hXWeightedInt
    hFY_ne_zero
