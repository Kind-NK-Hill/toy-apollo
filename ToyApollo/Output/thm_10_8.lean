import Mathlib
import ToyApollo.Output.def_10_4
import ToyApollo.Output.prob_3_5
import ToyApollo.Output.thm_10_8_quantile_defs
import ToyApollo.Output.thm_10_8_quantile_convergence
import ToyApollo.Output.thm_10_8_quantile_law

/-
TASK ID: thm_10_8
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter10-distribution-total-variation
TASK CONTENT:
\begin{thmbox}{10.8 (Skorokhod's Representation Theorem)}
If $X_n\xrightarrow{D}X$, then we can construct random variables $Y$ and $Y_n$, for $n\geq 1$, on a common probability space, such that $Y_n\xrightarrow{\mathrm{a.s.}}Y$, $Y_n$ has the same distribution as $X_n$ for all $n$, and $Y$ has the same distribution as $X$.
\end{thmbox}

\textit{Proof}
We need to construct random variables $Y_n$'s and $Y$, defined on a common probability space, so that (i) $Y_n(\omega)$'s converge to $Y(\omega)$ almost surely, (ii) $Y_n$ and $X_n$ are identically distributed for all $n$, and (iii) $Y$ and $X$ are identically distributed. The proof is an application of coupling argument.

To construct $Y_n$ and $Y$, we take the probability space $([0,1],\mathcal{B}([0,1]),\lambda)$, where $\lambda$ represents the Lebesgue measure on $[0,1]$, as the common probability space. Using the distribution function $F_n(x)$, we define a function $Y_n:[0,1]\to\mathbb{R}$, for $n=1,2,3,\ldots$, by
\[
Y_n(\omega)\coloneqq \sup\{y:F_n(y)<\omega\},
\tag{10.4}
\]
and define
\[
Y(\omega)\coloneqq \sup\{y:F(y)<\omega\}.
\tag{10.5}
\]
We take the supremums in the definitions of $Y_n$ and $Y$ to handle the potential discontinuities of the distribution functions $F_n$ and $F$. If $F_n$ and $F$ are continuous and one-to-one such that the inverses $F_n^{-1}$ and $F^{-1}$ exist, then we can simply define $Y_n$ and $Y$ by the inverse functions.

One can verify that
\[
\{\omega:Y_n(\omega)\leq y\}=\{\omega:\omega\leq F_n(y)\}
\qquad\text{and}\qquad
\{\omega:Y(\omega)\leq y\}=\{\omega:\omega\leq F(y)\}.
\]
These calculations show that $F_n(y)$ is the cdf of $Y_n$, and $F(y)$ is the cdf of $Y$. Hence, $Y_n$ and $X_n$ are identically distributed for all $n$, and the random variables $X$ and $Y$ are also identically distributed.

To show that $Y_n(\omega)\to Y(\omega)$ for all $\omega\in(0,1)$, we further define
\[
Y_n^+(\omega)\coloneqq \inf\{y:F_n(y)>\omega\}
\quad\text{for }n\geq 1,
\]
and
\[
Y^+(\omega)\coloneqq \inf\{y:F(y)>\omega\}.
\]
By construction, we have $Y_n\leq Y_n^+$ and $Y\leq Y^+$. But $Y_n$ and $Y_n^+$ are equal almost surely for all $n$, and $Y$ and $Y^+$ are also equal almost surely.

We fix $\omega$ in $(0,1)$. Take a continuity point $y_0$ of $F(y)$ such that $y_0>Y^+(\omega)$. Then $F(y_0)>\omega$, and for all sufficiently large $n$, we have $F_n(y_0)>\omega$. From the definition of $Y_n^+$, we have $Y_n^+(\omega)<y_0$ for all sufficiently large $n$. Hence,
\[
\limsup_n Y_n^+(\omega)\leq y_0.
\]
Because $F$ has at most countably many discontinuity points (see Exercise 3.5), we can take a sequence $(y_i)_{i=1}^{\infty}$ such that $F$ is continuous at $y_i$ for all $i$, and $y_i\downarrow Y^+(\omega)$. This gives
\[
\limsup_n Y_n^+(\omega)\leq Y^+(\omega).
\]
Similarly, we can prove that $\liminf_n Y_n(\omega)\geq Y(\omega)$. For each $\omega$, we have the inequalities
\[
Y(\omega)\leq \liminf_n Y_n(\omega)
\leq \limsup_n Y_n^+(\omega)\leq Y^+(\omega).
\]
Since $Y$ and $Y^+$ are equal almost surely, $Y_n^+$ converges to $Y$ almost surely. Therefore, we have $Y_n(\omega)\to Y(\omega)$ for $\omega$ in a subset of $(0,1)$ with probability $1$.
\hfill $\square$
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- The representation conclusion in Theorem 10.8, expressed without committing
the repository to a particular implementation of the common probability space.
The witness space carries random variables with the original laws and almost
sure convergence on that witness space. -/
def SkorokhodRepresentation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
    ∃ (Yn : ℕ → ℝ → ℝ) (Y : ℝ → ℝ),
      (∀ᵐ ω ∂ν, Tendsto (fun n : ℕ => Yn n ω) atTop (nhds (Y ω))) ∧
      (∀ n : ℕ, Measure.map (Yn n) ν = Measure.map (Xn n) μ) ∧
      Measure.map Y ν = Measure.map X μ

/-- Auditable support for the quantile construction in the source proof of
Skorokhod representation. The CDF-to-law and a.s.-convergence quantile bridges
are proved locally; the support structure only carries probability-measure
instances for the source and target laws. -/
structure SkorokhodQuantileSupport {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (_hDist : RandomVariablesConvergeInDistribution μ Xn X) where
  target_seq_isProbability : ∀ n : ℕ, IsProbabilityMeasure (Measure.map (Xn n) μ)
  target_isProbability : IsProbabilityMeasure (Measure.map X μ)

/-- The quantile-construction support used below follows from the ordinary
random-variable measurability assumptions and the fact that the source measure
is a probability measure.  This keeps the public theorem interface in the
textbook form instead of asking callers to provide a proof package. -/
theorem mkSkorokhodQuantileSupport {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hDist : RandomVariablesConvergeInDistribution μ Xn X)
    (hXn : ∀ n : ℕ, AEMeasurable (Xn n) μ)
    (hX : AEMeasurable X μ) :
    SkorokhodQuantileSupport μ Xn X hDist where
  target_seq_isProbability := fun n : ℕ =>
    Measure.isProbabilityMeasure_map (hXn n)
  target_isProbability := Measure.isProbabilityMeasure_map hX

/-- Theorem 10.8, with the CDF-to-law part discharged by the local lower-ray
bridge and the a.s. quantile convergence discharged by the local
lower/upper-quantile sandwich bridge. -/
theorem thm_10_8 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hDist : RandomVariablesConvergeInDistribution μ Xn X)
    (hXn : ∀ n : ℕ, AEMeasurable (Xn n) μ)
    (hX : AEMeasurable X μ) :
    SkorokhodRepresentation μ Xn X := by
  let h_quantile_support :=
    mkSkorokhodQuantileSupport μ Xn X hDist hXn hX
  have hCdfConv :
      CdfConvergesInDistribution
        (fun n x =>
          (thm_10_8_probabilityCdfOfMeasure
            (Measure.map (Xn n) μ)).stieltjes x)
        ((thm_10_8_probabilityCdfOfMeasure
          (Measure.map X μ)).stieltjes : ℝ → ℝ) := by
    haveI hTarget : IsProbabilityMeasure (Measure.map X μ) :=
      h_quantile_support.target_isProbability
    haveI hSeq (n : ℕ) : IsProbabilityMeasure (Measure.map (Xn n) μ) :=
      h_quantile_support.target_seq_isProbability n
    have hDistCdf :
        CdfConvergesInDistribution
          (fun n x => measureCdf (Measure.map (Xn n) μ) x)
          (measureCdf (Measure.map X μ)) := by
      simpa [RandomVariablesConvergeInDistribution,
        MeasuresConvergeInDistribution] using hDist
    intro x hcont
    have hcont_measure :
        ContinuousAt (measureCdf (Measure.map X μ)) x := by
      have hfun :
          (fun y : ℝ => measureCdf (Measure.map X μ) y) =
            (fun y : ℝ =>
              (thm_10_8_probabilityCdfOfMeasure
                (Measure.map X μ)).stieltjes y) := by
        funext y
        simp [measureCdf, thm_10_8_probabilityCdfOfMeasure,
          ProbabilityTheory.cdf_eq_real]
      change ContinuousAt
        (fun y : ℝ => measureCdf (Measure.map X μ) y) x
      rw [hfun]
      exact hcont
    have htendsto := hDistCdf x hcont_measure
    simpa [measureCdf, thm_10_8_probabilityCdfOfMeasure,
      ProbabilityTheory.cdf_eq_real] using htendsto
  have hAlmostSure :
      ∀ᵐ ω ∂thm_10_8_unitIntervalMeasure,
        Tendsto
          (fun n : ℕ =>
            thm_10_8_lowerQuantileVariable
              (thm_10_8_probabilityCdfOfMeasure (Measure.map (Xn n) μ)) ω)
          atTop
          (nhds
            (thm_10_8_lowerQuantileVariable
              (thm_10_8_probabilityCdfOfMeasure (Measure.map X μ)) ω)) :=
    thm_10_8_almost_sure_lowerQuantile_tendsto
      (fun n : ℕ =>
        thm_10_8_probabilityCdfOfMeasure (Measure.map (Xn n) μ))
      (thm_10_8_probabilityCdfOfMeasure (Measure.map X μ))
      hCdfConv
  have hYnLaw :
      ∀ n : ℕ,
        Measure.map
          (thm_10_8_lowerQuantileVariable
            (thm_10_8_probabilityCdfOfMeasure (Measure.map (Xn n) μ)))
          thm_10_8_unitIntervalMeasure =
        Measure.map (Xn n) μ :=
    fun n : ℕ =>
      @thm_10_8_quantile_law_preservation_of_probabilityCdfOfMeasure
        (Measure.map (Xn n) μ)
        (h_quantile_support.target_seq_isProbability n)
  have hYLaw :
      Measure.map
        (thm_10_8_lowerQuantileVariable
          (thm_10_8_probabilityCdfOfMeasure (Measure.map X μ)))
        thm_10_8_unitIntervalMeasure =
      Measure.map X μ :=
    @thm_10_8_quantile_law_preservation_of_probabilityCdfOfMeasure
      (Measure.map X μ)
      h_quantile_support.target_isProbability
  exact
    ⟨thm_10_8_unitIntervalMeasure,
      thm_10_8_unitIntervalMeasure_isProbabilityMeasure,
      fun n : ℕ =>
        thm_10_8_lowerQuantileVariable
          (thm_10_8_probabilityCdfOfMeasure (Measure.map (Xn n) μ)),
      thm_10_8_lowerQuantileVariable
        (thm_10_8_probabilityCdfOfMeasure (Measure.map X μ)),
      hAlmostSure,
      hYnLaw,
      hYLaw⟩
