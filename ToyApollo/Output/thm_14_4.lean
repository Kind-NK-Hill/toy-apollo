import Mathlib
import ToyApollo.Output.def_14_1
import ToyApollo.Output.thm_14_4_density_support

/-
TASK ID: thm_14_4
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter14-weak-convergence
TASK CONTENT:
\begin{thmbox}{14.4}
\end{thmbox}

If probability measures \mun,f o r n= 1 ,2,3,... , defined on the measurable

space .(R,\mathcal{B}(R)) converge in total variation distance, then they converge

weakly.

\textit{Proof} Suppose that .(\mun)\infty

n=1 converges in total variation to. \mu, ie.,dTV (\mun,\mu )\to 0

as n\to\infty For any fixed index n, define a measure \nun \coloneqq(\mu n +\mu)/ 2We have

\mun \ll \nun and \mu\ll \nun. By applying Radon-Nikodym theorem (Theorem 13.5), we

can represent \mun by density fn, and \mu by density f, relative to the measure \nun.

Leth: R \to R denote a bounded and continuous function, andhmax be an upper

bound of h(x) over all x. By triangle inequality (Theorem 7.1), we get

\vert\vert\vert

\int

R

h(x) d\mun(x) -

\int

R

h(x) d\mu(x)

\vert\vert\vert =

\vert\vert\vert

\int

R

h(x)fn(x)d\nun(x)

-

\int

R

h(x)f(x)d\nu n(x)

\vert\vert\vert

\leq hmax

\int

R

\vertfn(x) - f( x)\vert d\nun(x).

The proof of Theorem 8.6 can be adapted to probability measures that are absolutely

continuous with respect to any probability measure. Indeed, we can use similar

argument to prove that

dTV (\mun,\mu )= 1

\int

R

\vertfn(x) - f( x)\vert d\nun(x),

which yields

\vert\vert\vert

\int

R

h(x) d\mun(x) -

\int

R

h(x) d\mu(x)

\vert\vert\vert \leq 2hmaxdTV (\mun,\mu ) .

Since dTV (\mun,\mu )converges to 0, we also have .

\int

hd\mu n \to

\int

hd\mu as n \to\infty .

The function h(x) can be any continuous and bounded function in the previous

paragraphs. This proves that probability measure \mun converges weakly to \mu. \hfill $\square$

We note that the converse of Theorem 14.4 does not hold in general. This is

because the total variation distance between a discrete distribution and a continuous

distribution is always equal to 1. For instance, the total variation distance between

a binomial distribution and a normal distribution is equal to 1. However, there

exist examples where binomial distribution converges in distribution to the normal

distribution, despite having a total variation distance of 1 between them. (see

example 10.3.1)
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set Metric
open scoped Topology ENNReal

noncomputable section

/-- Total-variation convergence of probability measures, using the Chapter 8
definition of total variation distance. -/
def thm_14_4_totalVariationConvergence
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ) : Prop :=
  Tendsto
    (fun n : ℕ => totalVariationDistance (Pseq n : Measure ℝ) (P : Measure ℝ))
    atTop (𝓝 (0 : ℝ))

/-- If the textbook quantitative bound is available, convergence in total
variation implies convergence of every bounded continuous test integral. -/
theorem thm_14_4_of_boundedContinuousTestDifferenceBound
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ)
    (hTV : thm_14_4_totalVariationConvergence Pseq P)
    (hBound : thm_14_4_boundedContinuousTestDifferenceBound Pseq P) :
    def_14_1 Pseq P := by
  intro h
  let L : ℝ := ∫ x, h x ∂(P : Measure ℝ)
  have hRhs :
      Tendsto
        (fun n : ℕ =>
          (2 * ‖h‖) * totalVariationDistance (Pseq n : Measure ℝ) (P : Measure ℝ))
        atTop (𝓝 (0 : ℝ)) := by
    simpa using hTV.const_mul (2 * ‖h‖)
  have hAbs :
      Tendsto
        (fun n : ℕ => |(∫ x, h x ∂(Pseq n : Measure ℝ)) - L|)
        atTop (𝓝 (0 : ℝ)) := by
    refine squeeze_zero (fun n => abs_nonneg _) ?_ hRhs
    intro n
    simpa [L] using hBound n h
  have hSub :
      Tendsto
        (fun n : ℕ => (∫ x, h x ∂(Pseq n : Measure ℝ)) - L)
        atTop (𝓝 (0 : ℝ)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Real.norm_eq_abs] using hAbs
  have hConst : Tendsto (fun _n : ℕ => L) atTop (𝓝 L) :=
    tendsto_const_nhds
  have hAdd :
      Tendsto
        (fun n : ℕ => ((∫ x, h x ∂(Pseq n : Measure ℝ)) - L) + L)
        atTop (𝓝 (0 + L)) :=
    hSub.add hConst
  simpa [L, sub_add_cancel] using hAdd

/-- Theorem 14.4: total-variation convergence of probability measures on
`(ℝ, Borel ℝ)` implies weak convergence.  The proof follows the source route:
dominate `μ_n` and `μ` by `ν_n = (μ_n + μ) / 2`, use Radon-Nikodym densities,
identify the density `L¹` difference with total variation, and then test
against bounded continuous functions. -/
theorem thm_14_4
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ)
    (hTV : thm_14_4_totalVariationConvergence Pseq P) :
    def_14_1 Pseq P := by
  exact thm_14_4_of_boundedContinuousTestDifferenceBound Pseq P hTV
    (thm_14_4_boundedContinuousTestDifferenceBound_from_rn Pseq P)

/-- The textbook note after Theorem 14.4: weak convergence need not imply
total-variation convergence.  This packages the binomial-to-normal style
situation referenced in Example 10.3.1 without adding it as a dependency of the
forward theorem. -/
structure thm_14_4_ConverseFailureWitness where
  discrete_laws : ℕ → ProbabilityMeasure ℝ
  continuous_law : ProbabilityMeasure ℝ
  weak_convergence : def_14_1 discrete_laws continuous_law
  total_variation_distance_one :
    ∀ n : ℕ,
      totalVariationDistance (discrete_laws n : Measure ℝ) (continuous_law : Measure ℝ) = 1

theorem thm_14_4_converseFailure_not_totalVariation
    (W : thm_14_4_ConverseFailureWitness) :
    ¬ thm_14_4_totalVariationConvergence W.discrete_laws W.continuous_law := by
  intro hTV
  have hconst :
      Tendsto
        (fun n : ℕ =>
          totalVariationDistance
            (W.discrete_laws n : Measure ℝ) (W.continuous_law : Measure ℝ))
        atTop (𝓝 (1 : ℝ)) := by
    simp [W.total_variation_distance_one]
  have huniq := tendsto_nhds_unique hTV hconst
  exact one_ne_zero huniq.symm

theorem thm_14_4_converseFailure_note
    (W : thm_14_4_ConverseFailureWitness) :
    def_14_1 W.discrete_laws W.continuous_law ∧
      ¬ thm_14_4_totalVariationConvergence W.discrete_laws W.continuous_law :=
  ⟨W.weak_convergence, thm_14_4_converseFailure_not_totalVariation W⟩
