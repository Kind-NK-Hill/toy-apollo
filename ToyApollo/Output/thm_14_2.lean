import Mathlib
import ToyApollo.Output.def_10_4
import ToyApollo.Output.def_14_2
import ToyApollo.Output.thm_10_8
import ToyApollo.Output.thm_10_11
import ToyApollo.Output.thm_14_1

/-
TASK ID: thm_14_2
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter14-weak-convergence
TASK CONTENT:
\begin{thmbox}{14.2 (Weak Convergence and Convergence in Distribution)}
\end{thmbox}

Suppose .(Xn)\infty

n=1 is a sequence of random variables, and X be another

random variable. Denote the cumulative distribution function of. Xn byFn(x),

forn \geq 1, and the cumulative distribution function of X byF(x) We have

Xn

W

\to X if and only if Fn

D

\to F.

\textit{Proof} (. ) Suppose F(x) is continuous at x = a, ie., P({a}) = 0. The idea of

proof is to approximate an indicator function by piece-wise linear function. Define

a piece-wise linear function g by

g(x) =

1i f x<a - \epsilon,

\epsilon(a - x) if a - \epsilon\leq x \leq a,

0i f x>a .

The function g is linearly decreasing from 1 to 0 in the interval .[a - \epsilon,a] and is

continuous and bounded. We have

1(-\infty ,a-\epsilon](x) \leq g(x) \leq 1(-\infty ,a](x).

Substitute x by X and Xn in the above inequalities, and take expectation to get

F(a - \epsilon)\leq E[g(X)]= limn\to\infty E[g(Xn)]\leq lim infn\to\infty Fn(a). (14.1)

The last inequality in (14.1) follows from E[g(Xn)]\leq Fn(a) for all n.

Similarly, consider the function h(x) = g(x - \epsilon)The function h(x) satisfies

1(-\infty ,a](x) \leq h(x) \leq 1(-\infty ,a+\epsilon](x)

and is continuous and bounded. We thus obtain

lim sup

n\to\infty

Fn(a) \leq limn\to\infty E[h(Xn)]= E[h(X)]\leq F(a + \epsilon). (14.2)

Putting (14.1) and (14.2) together, we get

F(a - \epsilon)\leq lim infn\to\infty Fn(a) \leq lim sup

n\to\infty

Fn(a) \leq F(a + \epsilon).

Since F(x) is continuous at x = a, the limit of .(Fn(a))n\geq1 exists and equals F(a) .

(. ) We apply Skorokhod representation theorem (Theorem 10.8), and let

(Yn)n\geq1 be a sequence of random variables defined on the same probability space,

such that Yn and Xn have the same distribution and Yn's converge almost surely to

a random variable Y that has the same distribution as X.

Leth(y) be a continuous and bounded function on. R. Because h is continuous, by

the continuous mapping theorem (Theorem 10.11),h(Yn) converges toh(Y) almost

surely. Since h(Yn) is bounded, we can apply the dominated convergence theorem

to obtain

limn\to\infty E[h(Xn)]= limn\to\infty E[h(Yn)]= E[limn\to\infty h(Yn)]= E[h(Y)]= E[h(X)].

Because it holds for any continuous and bounded function h(x), this proves that Xn

converges weakly to X. \hfill $\square$

We can now prove that Condition 1 implies Condition 2 in Theorem 14.1.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set ProbabilityTheory Function
open scoped Topology

noncomputable section

/-- The cdf of a real random variable, written through its image measure. -/
def thm_14_2_randomVariableCdf
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) : ℝ → ℝ :=
  fun x => measureCdf (Measure.map X μ) x

/-- The cdf-convergence side of Theorem 14.2. -/
def thm_14_2_cdfConvergence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  CdfConvergesInDistribution
    (fun n => thm_14_2_randomVariableCdf μ (Xseq n))
    (thm_14_2_randomVariableCdf μ X)

/-- The weak-convergence side of Theorem 14.2, reusing Definition 14.2. -/
def thm_14_2_weakConvergence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X) : Prop :=
  def_14_2 μ Xseq X hXseq hX

/-- The cdf formulation agrees definitionally with the Chapter 10 convergence
in-distribution interface for random variables. -/
theorem thm_14_2_cdfConvergence_eq_def_10_4
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ) :
    thm_14_2_cdfConvergence μ Xseq X =
      RandomVariablesConvergeInDistribution μ Xseq X := by
  rfl

/-- The expectation form of the weak-convergence side, directly inherited from
Definition 14.2. -/
theorem thm_14_2_weak_iff_expectations
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Xseq : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X) :
    thm_14_2_weakConvergence μ Xseq X hXseq hX ↔
      ∀ h : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun n : ℕ => ∫ ω, h (Xseq n ω) ∂μ) atTop
          (𝓝 (∫ ω, h (X ω) ∂μ)) := by
  exact def_14_2_iff_expectations μ hXseq hX

/-- At a continuity point of a real cdf, the corresponding law has no atom.
This is the cdf-side form of the source phrase `P({a}) = 0`. -/
theorem thm_14_2_atom_zero_of_cdf_continuous
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {x : ℝ}
    (hcont : ContinuousAt (fun y : ℝ => measureCdf μ y) x) :
    μ {x} = 0 := by
  have hcont_cdf : ContinuousAt (fun y : ℝ => cdf μ y) x := by
    simpa [measureCdf, cdf_eq_real] using hcont
  have hleft : Function.leftLim (fun y : ℝ => cdf μ y) x = cdf μ x := by
    exact hcont_cdf.continuousWithinAt.leftLim_eq
  rw [← measure_cdf μ, StieltjesFunction.measure_singleton]
  simp [hleft]

/-- The first direction of Theorem 14.2: weak convergence of the induced laws
implies convergence of the cdfs at continuity points.  This packages the
textbook piecewise-linear sandwich through the local weak-convergence topology
and the Portmanteau boundary-null bridge for `(-∞, x]`. -/
theorem thm_14_2_weak_to_cdfConvergence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Xseq : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X)
    (hWeak : thm_14_2_weakConvergence μ Xseq X hXseq hX) :
    thm_14_2_cdfConvergence μ Xseq X := by
  let Pseq : ℕ → ProbabilityMeasure ℝ := def_14_1_laws μ Xseq hXseq
  let P : ProbabilityMeasure ℝ := def_14_1_law μ X hX
  have hLawWeak : def_14_1 Pseq P := by
    simpa [Pseq, P, thm_14_2_weakConvergence, def_14_2,
      def_14_1, def_14_1_weakConvergence,
      def_14_1_randomVariableWeakConvergence, def_14_1_laws, def_14_1_law] using hWeak
  have hTend : Tendsto Pseq atTop (𝓝 P) := (def_14_1_iff_tendsto).1 hLawWeak
  intro x hxcont
  have hAtom : (P : Measure ℝ) {x} = 0 := by
    haveI : IsProbabilityMeasure (Measure.map X μ) :=
      Measure.isProbabilityMeasure_map hX.aemeasurable
    simpa [P, def_14_1_law] using
      (thm_14_2_atom_zero_of_cdf_continuous (Measure.map X μ) hxcont)
  have hFrontier : (P : Measure ℝ) (frontier (Iic x)) = 0 := by
    simpa [frontier_Iic] using hAtom
  have hENN :
      Tendsto
        (fun n : ℕ => ((Pseq n : ProbabilityMeasure ℝ) : Measure ℝ) (Iic x))
        atTop (𝓝 (((P : ProbabilityMeasure ℝ) : Measure ℝ) (Iic x))) :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hTend hFrontier
  have hReal :
      Tendsto
        (fun n : ℕ =>
          (((Pseq n : ProbabilityMeasure ℝ) : Measure ℝ) (Iic x)).toReal)
        atTop
        (𝓝 ((((P : ProbabilityMeasure ℝ) : Measure ℝ) (Iic x)).toReal)) :=
    (ENNReal.tendsto_toReal
      (measure_ne_top (((P : ProbabilityMeasure ℝ) : Measure ℝ)) (Iic x))).comp hENN
  simpa [thm_14_2_cdfConvergence, thm_14_2_randomVariableCdf,
    CdfConvergesInDistribution, measureCdf, Pseq, P, def_14_1_laws,
    def_14_1_law, measureReal_def] using hReal

/-- The Skorokhod-representation step used in the reverse implication. -/
theorem thm_14_2_skorokhod_representation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Xseq : ℕ → Ω → ℝ} {X : Ω → ℝ}
    {hXseq : ∀ n : ℕ, Measurable (Xseq n)} {hX : Measurable X}
    (hDist : thm_14_2_cdfConvergence μ Xseq X) :
    SkorokhodRepresentation μ Xseq X := by
  exact thm_10_8 μ Xseq X hDist
    (fun n : ℕ => (hXseq n).aemeasurable) hX.aemeasurable

/-- The reverse implication in Theorem 14.2.  It follows the source proof by
using the local quantile coupling from Theorem 10.8, then applying Mathlib's
bridge from almost-sure convergence to convergence in distribution. -/
theorem thm_14_2_distribution_to_weak
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Xseq : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X)
    (hDist : thm_14_2_cdfConvergence μ Xseq X) :
    thm_14_2_weakConvergence μ Xseq X hXseq hX := by
  let Fseq : ℕ → thm_10_8_ProbabilityCdf := fun n : ℕ =>
    thm_10_8_probabilityCdfOfMeasure (Measure.map (Xseq n) μ)
  let F : thm_10_8_ProbabilityCdf :=
    thm_10_8_probabilityCdfOfMeasure (Measure.map X μ)
  let Yn : ℕ → ℝ → ℝ := fun n : ℕ =>
    thm_10_8_lowerQuantileVariable (Fseq n)
  let Y : ℝ → ℝ := thm_10_8_lowerQuantileVariable F
  have hCdfConv :
      CdfConvergesInDistribution
        (fun n x => (Fseq n).stieltjes x)
        (F.stieltjes : ℝ → ℝ) := by
    haveI hTarget : IsProbabilityMeasure (Measure.map X μ) :=
      Measure.isProbabilityMeasure_map hX.aemeasurable
    haveI hSeq (n : ℕ) : IsProbabilityMeasure (Measure.map (Xseq n) μ) :=
      Measure.isProbabilityMeasure_map (hXseq n).aemeasurable
    have hDistCdf :
        CdfConvergesInDistribution
          (fun n x => measureCdf (Measure.map (Xseq n) μ) x)
          (measureCdf (Measure.map X μ)) := by
      simpa [thm_14_2_cdfConvergence, thm_14_2_randomVariableCdf] using hDist
    intro x hcont
    have hcont_measure :
        ContinuousAt (measureCdf (Measure.map X μ)) x := by
      have hfun :
          (fun y : ℝ => measureCdf (Measure.map X μ) y) =
            (fun y : ℝ => F.stieltjes y) := by
        funext y
        simp [F, thm_10_8_probabilityCdfOfMeasure,
          measureCdf, ProbabilityTheory.cdf_eq_real]
      change ContinuousAt (fun y : ℝ => measureCdf (Measure.map X μ) y) x
      rw [hfun]
      exact hcont
    have htendsto := hDistCdf x hcont_measure
    simpa [Fseq, F, thm_10_8_probabilityCdfOfMeasure,
      measureCdf, ProbabilityTheory.cdf_eq_real] using htendsto
  have hAlmostSure :
      ∀ᵐ ω ∂thm_10_8_unitIntervalMeasure,
        Tendsto (fun n : ℕ => Yn n ω) atTop (nhds (Y ω)) := by
    simpa [Yn, Y, Fseq, F] using
      thm_10_8_almost_sure_lowerQuantile_tendsto Fseq F hCdfConv
  have hYnMeas : ∀ n : ℕ, Measurable (Yn n) := by
    intro n
    exact thm_10_8_lowerQuantileVariable_measurable (Fseq n)
  have hInMeasure : TendstoInMeasure thm_10_8_unitIntervalMeasure Yn atTop Y :=
    tendstoInMeasure_of_tendsto_ae
      (fun n : ℕ => (hYnMeas n).aestronglyMeasurable)
      hAlmostSure
  have hInDistribution :
      TendstoInDistribution Yn atTop Y
        (fun _ : ℕ => thm_10_8_unitIntervalMeasure)
        thm_10_8_unitIntervalMeasure :=
    hInMeasure.tendstoInDistribution
      (fun n : ℕ => (hYnMeas n).aemeasurable)
  have hYnLaw :
      ∀ n : ℕ,
        Measure.map (Yn n) thm_10_8_unitIntervalMeasure =
          Measure.map (Xseq n) μ := by
    intro n
    simpa [Yn, Fseq] using
      @thm_10_8_quantile_law_preservation_of_probabilityCdfOfMeasure
        (Measure.map (Xseq n) μ)
        (Measure.isProbabilityMeasure_map (hXseq n).aemeasurable)
  have hYLaw :
      Measure.map Y thm_10_8_unitIntervalMeasure = Measure.map X μ := by
    simpa [Y, F] using
      @thm_10_8_quantile_law_preservation_of_probabilityCdfOfMeasure
        (Measure.map X μ)
        (Measure.isProbabilityMeasure_map hX.aemeasurable)
  let Pseq : ℕ → ProbabilityMeasure ℝ := def_14_1_laws μ Xseq hXseq
  let P : ProbabilityMeasure ℝ := def_14_1_law μ X hX
  have hLawTendsto : Tendsto Pseq atTop (𝓝 P) := by
    have hPseq :
        (fun n : ℕ =>
          (⟨Measure.map (Yn n) thm_10_8_unitIntervalMeasure,
            Measure.isProbabilityMeasure_map
              (hInDistribution.forall_aemeasurable n)⟩ :
            ProbabilityMeasure ℝ)) = Pseq := by
      funext n
      apply Subtype.ext
      simpa [Pseq, def_14_1_laws, def_14_1_law] using hYnLaw n
    have hP :
        (⟨Measure.map Y thm_10_8_unitIntervalMeasure,
          Measure.isProbabilityMeasure_map hInDistribution.aemeasurable_limit⟩ :
          ProbabilityMeasure ℝ) = P := by
      apply Subtype.ext
      simpa [P, def_14_1_law] using hYLaw
    rw [← hPseq, ← hP]
    exact hInDistribution.tendsto
  have hLawWeak : def_14_1 Pseq P := (def_14_1_iff_tendsto).2 hLawTendsto
  simpa [thm_14_2_weakConvergence, def_14_2,
    def_14_1_randomVariableWeakConvergence, Pseq, P, def_14_1_laws,
    def_14_1_law, def_14_1, def_14_1_weakConvergence] using hLawWeak

/-- The final equivalence of Theorem 14.2. -/
theorem thm_14_2
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xseq : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXseq : ∀ n : ℕ, Measurable (Xseq n)) (hX : Measurable X) :
    thm_14_2_weakConvergence μ Xseq X hXseq hX ↔
      thm_14_2_cdfConvergence μ Xseq X := by
  constructor
  · intro hWeak
    exact thm_14_2_weak_to_cdfConvergence μ hXseq hX hWeak
  · intro hDist
    exact thm_14_2_distribution_to_weak μ hXseq hX hDist

/-- The post-Theorem-14.2 step announced in the text: weak convergence of laws
implies condition 2 in Levy's continuity theorem. -/
theorem thm_14_2_levy_condition_one_to_two
    {P : ℕ → ProbabilityMeasure ℝ} {φ : ℝ → ℂ}
    (hφ : thm_14_1_pointwiseCharFunConvergence P φ) :
    thm_14_1_weakLimit P → thm_14_1_limitIsCharacteristic φ :=
  (thm_14_1_weak_iff_characteristic hφ).mp
