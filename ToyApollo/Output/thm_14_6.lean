import Mathlib
import ToyApollo.Output.def_14_3
import ToyApollo.Output.thm_10_8
import ToyApollo.Output.thm_14_3
import ToyApollo.Output.thm_9_5

/-
TASK ID: thm_14_6
TYPE: Theorem_Statement
SOURCE PLAN: chapter14-prokhorov-sequential-compactness
TASK CONTENT:
\begin{thmbox}{14.6 (Prokhorov)}
\end{thmbox}

If.(Fn)\infty

n=1 is a sequence of tight cumulative distribution functions, then there

exists a subsequence converging in distribution to the cumulative distribution

of a probability measure.

The Prokhorov theorem is analogous to the Bolzano-Weierstrass theorem. In

real analysis, a subset S in Rn is said to be sequentially compact if any infinite

sequence in S has a convergent subsequence that converges to an element in SThe

Prokhorov theorem says that the space of tight distributions with topology defined

by weak convergence is sequentially compact. For a proof of this theorem, see [ 4,

Thm 3.2.12 and 3.2.13].

We now complete the proof of Levy's theorem. Consider a sequence .(Pn)n\geq1 of

probability measure that is a tight, and let.(Fn)n\geq1 be the corresponding cumulative

distribution functions. In Levy's continuity theorem, the characteristic function

\phin(t) of Pn is assumed to converge pointwise, with the limit function denoted by

\phi(n).

By the Prokhorov theorem, there exists a subsequence .(an)n\geq1 of N such that

Fan(x) converges pointwise to the cumulative distribution function F(x) of a

probability measure P at every continuity point of F(x) Using Theorem 14.3

and the equivalence of weak convergence and convergence in distribution, we can

show that the characteristic functions\phian (t) converge pointwise to the characteristic

function of P. Since we assume that limn\to\infty \phian(t)= \phi(t) , we can conclude that

\phi(t) is the characteristic function of P.

We now demonstrate that the entire sequence .(Pn)n\geq1 of probability measures

weakly converges to PLeth(x) be a bounded and continuous function. We must

show that

limn\to\infty

\int

R

h(x) dPn(x)=

\int

R

f (x) dP(x).

To prove this, we use the following fact from real analysis:

Given a numerical sequence .(\alphan)n\geq1, if every subsequence of .(\alphan)n\geq1 contains

a further subsequence that is convergent to \beta, then the original sequence .(\alphan)n\geq1 is

convergent to \beta.

Let i1, i2,i 3,.be a subsequence of N. We consider the subsequence

( \int

h(x) dPij (x)

)

j\geq 1

(14.8)

Since any subsequence of a tight sequence is tight, the sequence of probability

measures .(Pij )j\geq 1 is tight. By Prokhorov theorem, there exists a sub-subsequence

ijk , where j1 <j 2 <j 3 <\cdot\cdot\cdot , such that Fijk (x) converges pointwise to

the distribution function G(x) of a probability measure Q at every continuity

point of G(x)By Theorem 14.3, the characteristic functions associated to this

sub-subsequence converge to the characteristic function of Q , which is also the

characteristic function of P due to the assumption that limk\to\infty \phiijk (t)= \phi(t) .

By the inversion formula in Theorem 9.5, Q and P have the same distribution.

Hence,

( \int

h(x) dPijk (x)

)

k\geq 1

is a sub-subsequence of (14.8) converging to

lim

k\to\infty

\int

h(x) dPijk (x)=

\int

h(x) dQ(x)=

\int

h(x) dP(x).

Therefore,.

\int

hdP n converges to.

\int

hdP asn\to\infty , and this completes the proof of

Levy's continuity theorem.

We illustrate Levy's continuity theorem with two classic examples. The first

example involves discrete random variables converging to another discrete random

variable, while the second example involves discrete random variables converging

to a continuous random variable.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- Distribution-function convergence along a subsequence, in the exact
continuity-point sense used in the statement of Prokhorov's theorem. -/
def thm_14_6_cdfSubsequenceConvergesInDistribution
    (Fseq : ℕ → ℝ → ℝ) (index : ℕ → ℕ) (P : ProbabilityMeasure ℝ) : Prop :=
  ∀ x : ℝ, ContinuousAt (def_14_3_cdfOfMeasure P) x →
    Tendsto (fun k : ℕ => Fseq (index k) x) atTop
      (𝓝 (def_14_3_cdfOfMeasure P x))

/-- The subsequence and limiting probability measure produced by Prokhorov's
theorem for a tight sequence of cumulative distribution functions. -/
structure thm_14_6_ProkhorovSubsequence
    (Fseq : ℕ → ℝ → ℝ) where
  index : ℕ → ℕ
  strictMono_index : StrictMono index
  limitMeasure : ProbabilityMeasure ℝ
  converges_at_continuity_points :
    thm_14_6_cdfSubsequenceConvergesInDistribution
      Fseq index limitMeasure

/-- Theorem 14.6 as the external Prokhorov statement cited by the textbook:
tight CDFs have a distribution-convergent subsequence whose limit is the CDF
of a probability measure. -/
def thm_14_6_prokhorovStatement
    (Fseq : ℕ → ℝ → ℝ) : Prop :=
  def_14_3_tightCdfs Fseq →
    Nonempty (thm_14_6_ProkhorovSubsequence Fseq)

/-- Tightness of CDFs is inherited by subsequences; this is the elementary
step used when the Levy proof applies Prokhorov to an arbitrary subsequence. -/
theorem thm_14_6_tightCdfs_subsequence
    {Fseq : ℕ → ℝ → ℝ} (hF : def_14_3_tightCdfs Fseq)
    (index : ℕ → ℕ) :
    def_14_3_tightCdfs (fun k : ℕ => Fseq (index k)) := by
  intro ε hε
  rcases hF ε hε with ⟨M, hM_nonneg, hM⟩
  exact ⟨M, hM_nonneg, fun k => hM (index k)⟩

/-- The weak-convergence form of the Prokhorov conclusion for probability
measures.  This is the topology-level version described immediately after the
boxed theorem. -/
def thm_14_6_weaklyConvergentSubsequence
    (Pseq : ℕ → ProbabilityMeasure ℝ) : Prop :=
  ∃ P : ProbabilityMeasure ℝ, ∃ index : ℕ → ℕ,
    StrictMono index ∧ def_14_1 (fun k : ℕ => Pseq (index k)) P

/-- Characteristic function of a probability measure on `ℝ`, reused in the
post-Prokhorov completion of Levy's theorem. -/
def thm_14_6_characteristicFunction
    (P : ProbabilityMeasure ℝ) (t : ℝ) : ℂ :=
  charFun (P : Measure ℝ) t

/-- Pointwise convergence of characteristic functions to the source limit
function appearing in Levy's continuity theorem. -/
def thm_14_6_characteristicConvergence
    (Pseq : ℕ → ProbabilityMeasure ℝ) (φ : ℝ → ℂ) : Prop :=
  ∀ t : ℝ,
    Tendsto (fun n : ℕ => thm_14_6_characteristicFunction (Pseq n) t)
      atTop (𝓝 (φ t))

/-- The real-analysis subsequence principle used in the final paragraph of
the source proof. -/
def thm_14_6_everySubsequenceHasSubsubsequenceLimit
    (α : ℕ → ℝ) (β : ℝ) : Prop :=
  ∀ index : ℕ → ℕ, StrictMono index →
    ∃ subindex : ℕ → ℕ, StrictMono subindex ∧
      Tendsto (fun k : ℕ => α (index (subindex k))) atTop (𝓝 β)

/-- Pointwise characteristic-function convergence is inherited by every
strictly increasing subsequence. -/
theorem thm_14_6_subsequence_inherits_characteristic_limit
    (Pseq : ℕ → ProbabilityMeasure ℝ) (φ : ℝ → ℂ)
    (hφ : thm_14_6_characteristicConvergence Pseq φ)
    (index : ℕ → ℕ) (hindex : StrictMono index) :
    ∀ t : ℝ,
      Tendsto (fun k : ℕ =>
        thm_14_6_characteristicFunction (Pseq (index k)) t)
        atTop (𝓝 (φ t)) := by
  intro t
  exact (hφ t).comp hindex.tendsto_atTop

/-- Law-level CDF convergence along a subsequence implies weak convergence of
the corresponding probability measures.  This is the law-side bridge needed
when the post-Prokhorov proof invokes Theorem 14.3. -/
theorem thm_14_6_cdfSubsequenceConvergence_to_weak
    {Pseq : ℕ → ProbabilityMeasure ℝ} {index : ℕ → ℕ}
    {Q : ProbabilityMeasure ℝ}
    (h :
      thm_14_6_cdfSubsequenceConvergesInDistribution
        (def_14_3_cdfsOfMeasures Pseq) index Q) :
    Tendsto (fun k : ℕ => Pseq (index k)) atTop (𝓝 Q) := by
  let Fseq : ℕ → thm_10_8_ProbabilityCdf := fun k : ℕ =>
    thm_10_8_probabilityCdfOfMeasure
      (((Pseq (index k) : ProbabilityMeasure ℝ) : Measure ℝ))
  let F : thm_10_8_ProbabilityCdf :=
    thm_10_8_probabilityCdfOfMeasure ((Q : ProbabilityMeasure ℝ) : Measure ℝ)
  let Yn : ℕ → ℝ → ℝ := fun k : ℕ =>
    thm_10_8_lowerQuantileVariable (Fseq k)
  let Y : ℝ → ℝ := thm_10_8_lowerQuantileVariable F
  have hCdfConv :
      CdfConvergesInDistribution
        (fun k x => (Fseq k).stieltjes x)
        (F.stieltjes : ℝ → ℝ) := by
    have hDist :
        CdfConvergesInDistribution
          (fun k x => measureCdf (((Pseq (index k) : ProbabilityMeasure ℝ) : Measure ℝ)) x)
          (measureCdf (((Q : ProbabilityMeasure ℝ) : Measure ℝ))) := by
      simpa [thm_14_6_cdfSubsequenceConvergesInDistribution,
        def_14_3_cdfsOfMeasures, def_14_3_cdfOfMeasure,
        CdfConvergesInDistribution, measureCdf, measureReal_def] using h
    intro x hcont
    have hcont_measure :
        ContinuousAt (measureCdf (((Q : ProbabilityMeasure ℝ) : Measure ℝ))) x := by
      have hfun :
          (fun y : ℝ =>
              measureCdf (((Q : ProbabilityMeasure ℝ) : Measure ℝ)) y) =
            (fun y : ℝ => F.stieltjes y) := by
        funext y
        simp [F, thm_10_8_probabilityCdfOfMeasure, measureCdf,
          ProbabilityTheory.cdf_eq_real]
      change ContinuousAt
        (fun y : ℝ => measureCdf (((Q : ProbabilityMeasure ℝ) : Measure ℝ)) y) x
      rw [hfun]
      exact hcont
    have htendsto := hDist x hcont_measure
    simpa [Fseq, F, thm_10_8_probabilityCdfOfMeasure, measureCdf,
      ProbabilityTheory.cdf_eq_real] using htendsto
  have hAlmostSure :
      ∀ᵐ ω ∂thm_10_8_unitIntervalMeasure,
        Tendsto (fun k : ℕ => Yn k ω) atTop (nhds (Y ω)) := by
    simpa [Yn, Y, Fseq, F] using
      thm_10_8_almost_sure_lowerQuantile_tendsto Fseq F hCdfConv
  have hYnMeas : ∀ k : ℕ, Measurable (Yn k) := by
    intro k
    exact thm_10_8_lowerQuantileVariable_measurable (Fseq k)
  have hInMeasure : TendstoInMeasure thm_10_8_unitIntervalMeasure Yn atTop Y :=
    tendstoInMeasure_of_tendsto_ae
      (fun k : ℕ => (hYnMeas k).aestronglyMeasurable)
      hAlmostSure
  have hInDistribution :
      TendstoInDistribution Yn atTop Y
        (fun _ : ℕ => thm_10_8_unitIntervalMeasure)
        thm_10_8_unitIntervalMeasure :=
    hInMeasure.tendstoInDistribution
      (fun k : ℕ => (hYnMeas k).aemeasurable)
  have hYnLaw :
      ∀ k : ℕ,
        Measure.map (Yn k) thm_10_8_unitIntervalMeasure =
          ((Pseq (index k) : ProbabilityMeasure ℝ) : Measure ℝ) := by
    intro k
    haveI : IsProbabilityMeasure
        (((Pseq (index k) : ProbabilityMeasure ℝ) : Measure ℝ)) :=
      (Pseq (index k)).property
    simpa [Yn, Fseq] using
      (@thm_10_8_quantile_law_preservation_of_probabilityCdfOfMeasure
        (((Pseq (index k) : ProbabilityMeasure ℝ) : Measure ℝ))
        (Pseq (index k)).property)
  have hYLaw :
      Measure.map Y thm_10_8_unitIntervalMeasure =
        ((Q : ProbabilityMeasure ℝ) : Measure ℝ) := by
    haveI : IsProbabilityMeasure (((Q : ProbabilityMeasure ℝ) : Measure ℝ)) :=
      Q.property
    simpa [Y, F] using
      (@thm_10_8_quantile_law_preservation_of_probabilityCdfOfMeasure
        (((Q : ProbabilityMeasure ℝ) : Measure ℝ))
        Q.property)
  have hLawTendsto : Tendsto (fun k : ℕ => Pseq (index k)) atTop (𝓝 Q) := by
    have hPseq :
        (fun k : ℕ =>
          (⟨Measure.map (Yn k) thm_10_8_unitIntervalMeasure,
            Measure.isProbabilityMeasure_map
              (hInDistribution.forall_aemeasurable k)⟩ :
            ProbabilityMeasure ℝ)) = fun k : ℕ => Pseq (index k) := by
      funext k
      apply Subtype.ext
      simpa using hYnLaw k
    have hP :
        (⟨Measure.map Y thm_10_8_unitIntervalMeasure,
          Measure.isProbabilityMeasure_map hInDistribution.aemeasurable_limit⟩ :
          ProbabilityMeasure ℝ) = Q := by
      apply Subtype.ext
      simpa using hYLaw
    rw [← hPseq, ← hP]
    exact hInDistribution.tendsto
  exact hLawTendsto

/-- The law-level Theorem 14.3 bridge used after Prokhorov: convergence of
CDFs at continuity points gives weak convergence, hence pointwise convergence
of characteristic functions. -/
theorem thm_14_6_theorem_14_3_characteristic_limit
    (Pseq : ℕ → ProbabilityMeasure ℝ)
    (Q : ProbabilityMeasure ℝ) (index : ℕ → ℕ) (_hindex : StrictMono index)
    (hCdf :
      thm_14_6_cdfSubsequenceConvergesInDistribution
        (def_14_3_cdfsOfMeasures Pseq) index Q) :
    ∀ t : ℝ,
      Tendsto (fun k : ℕ =>
        thm_14_6_characteristicFunction (Pseq (index k)) t)
        atTop (𝓝 (thm_14_6_characteristicFunction Q t)) := by
  have hWeak :
      Tendsto (fun k : ℕ => Pseq (index k)) atTop (𝓝 Q) :=
    thm_14_6_cdfSubsequenceConvergence_to_weak hCdf
  have hChar :=
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun
      (μ := fun k : ℕ => Pseq (index k)) (μ₀ := Q)).mp hWeak
  intro t
  simpa [thm_14_6_characteristicFunction] using hChar t

/-- Characteristic functions identify probability measures on `ℝ`.  This is
the law-level uniqueness step used in the post-Prokhorov completion of Lévy's
theorem. -/
theorem thm_14_6_inversion_formula_identifies_limit
    (P Q : ProbabilityMeasure ℝ)
    (hchar : ∀ t : ℝ,
      thm_14_6_characteristicFunction Q t =
        thm_14_6_characteristicFunction P t) :
    Q = P := by
  have hmeasure : (Q : Measure ℝ) = (P : Measure ℝ) := by
    exact Measure.ext_of_charFun (funext hchar)
  exact ProbabilityMeasure.toMeasure_injective hmeasure

/-- A real sequence converges to `β` if every subsequence has a further
subsequence converging to `β`. -/
theorem thm_14_6_real_analysis_subsequence_principle
    (α : ℕ → ℝ) (β : ℝ)
    (h : thm_14_6_everySubsequenceHasSubsubsequenceLimit α β) :
    Tendsto α atTop (𝓝 β) := by
  refine tendsto_of_subseq_tendsto ?_
  intro ns hns
  rcases strictMono_subseq_of_tendsto_atTop hns with ⟨φ, _hφ, hnsφ⟩
  rcases h (ns ∘ φ) hnsφ with ⟨subindex, _hsubindex, hlim⟩
  exact ⟨φ ∘ subindex, by simpa [Function.comp_def] using hlim⟩

/-- If the pointwise characteristic-function limit has already been identified
as the characteristic function of `P`, then every subsequence has a further
subsequence whose bounded-continuous test integrals converge to those of `P`.
This is the theorem-level version of the final post-Prokhorov support step. -/
theorem thm_14_6_subsubsequence_test_integral_limit
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ)
    (φ : ℝ → ℂ)
    (hφ : thm_14_6_characteristicConvergence Pseq φ)
    (hφP : ∀ t : ℝ, φ t = thm_14_6_characteristicFunction P t) :
    ∀ h : BoundedContinuousFunction ℝ ℝ,
      thm_14_6_everySubsequenceHasSubsubsequenceLimit
        (fun n : ℕ => ∫ x, h x ∂(Pseq n : Measure ℝ))
        (∫ x, h x ∂(P : Measure ℝ)) := by
  have hWeak : Tendsto Pseq atTop (𝓝 P) := by
    exact (ProbabilityMeasure.tendsto_iff_tendsto_charFun
      (μ := Pseq) (μ₀ := P)).mpr (fun t : ℝ => by
        simpa [thm_14_6_characteristicFunction, hφP t] using hφ t)
  intro h index hindex
  refine ⟨id, (fun _ _ hlt => hlt), ?_⟩
  have hSubWeak : Tendsto (fun k : ℕ => Pseq (index k)) atTop (𝓝 P) :=
    hWeak.comp hindex.tendsto_atTop
  exact ((def_14_1_iff_tendsto).2 hSubWeak) h

/-- The exact sequence of obligations in the textbook completion of Levy's
theorem after Prokhorov: pass to sub-subsequences, use Theorem 14.3 to identify
characteristic functions, use Theorem 9.5 to identify the limiting laws, and
then apply the elementary subsequence principle to each bounded continuous
test integral. -/
structure thm_14_6_LevyCompletionSpine
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ)
    (φ : ℝ → ℂ)
    (hφ : thm_14_6_characteristicConvergence Pseq φ) : Prop where
  tight_cdfs :
    def_14_3_tightCdfs (def_14_3_cdfsOfMeasures Pseq)
  prokhorov_subsubsequence :
    ∀ index : ℕ → ℕ, StrictMono index →
      Nonempty (thm_14_6_ProkhorovSubsequence
        (fun j : ℕ => def_14_3_cdfOfMeasure (Pseq (index j))))
  subsubsequence_test_integral_limit :
    ∀ h : BoundedContinuousFunction ℝ ℝ,
      thm_14_6_everySubsequenceHasSubsubsequenceLimit
        (fun n : ℕ => ∫ x, h x ∂(Pseq n : Measure ℝ))
        (∫ x, h x ∂(P : Measure ℝ))

/-- Applying the cited CDF version of Prokhorov to a tight CDF sequence. -/
theorem thm_14_6_cdf_of_reference
    (Fseq : ℕ → ℝ → ℝ)
    (hF : def_14_3_tightCdfs Fseq)
    (hProkhorov_reference : thm_14_6_prokhorovStatement Fseq) :
    Nonempty (thm_14_6_ProkhorovSubsequence Fseq) :=
  hProkhorov_reference hF

/-- Theorem 14.6 in the weak-topology form described by the textbook:
a tight sequence of probability measures has a weakly convergent subsequence.
Mathlib supplies the Prokhorov compactness theorem for tight sets of
probability measures; Definition 14.1 supplies the weak-convergence interface. -/
theorem thm_14_6
    (Pseq : ℕ → ProbabilityMeasure ℝ)
    (hTight : def_14_3_mathlibTight Pseq) :
    thm_14_6_weaklyConvergentSubsequence Pseq := by
  have hcompact : IsCompact (closure (range Pseq)) := by
    refine isCompact_closure_of_isTightMeasureSet (S := range Pseq) ?_
    have hset :
        {((P : ProbabilityMeasure ℝ) : Measure ℝ) | P ∈ range Pseq} =
          range (fun n : ℕ => ((Pseq n : ProbabilityMeasure ℝ) : Measure ℝ)) := by
      ext μ
      constructor
      · rintro ⟨P, hP, rfl⟩
        rcases hP with ⟨n, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨Pseq n, ⟨n, rfl⟩, rfl⟩
    rw [hset]
    exact hTight
  rcases hcompact.tendsto_subseq
      (x := Pseq)
      (fun n : ℕ => subset_closure (mem_range_self n)) with
    ⟨P, _hP, index, hindex, hconv⟩
  refine ⟨P, index, hindex, ?_⟩
  exact (def_14_1_iff_tendsto).2 (by
    simpa [Function.comp_def] using hconv)

/-- The interval formulation of tightness from Definition 14.3 gives the same
Prokhorov conclusion through the theorem-level bridge in Definition 14.3. -/
theorem thm_14_6_of_interval_tight
    (Pseq : ℕ → ProbabilityMeasure ℝ)
    (hTight : def_14_3 Pseq) :
    thm_14_6_weaklyConvergentSubsequence Pseq :=
  thm_14_6 Pseq (def_14_3_to_mathlibTight Pseq hTight)

/-- The post-Prokhorov completion of Levy's theorem: once the source proof
obligations are supplied, the whole sequence converges weakly. -/
private theorem thm_14_6_levy_completion
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ)
    (φ : ℝ → ℂ)
    (hφ : thm_14_6_characteristicConvergence Pseq φ)
    (hspine : thm_14_6_LevyCompletionSpine Pseq P φ hφ) :
    def_14_1 Pseq P := by
  intro h
  exact thm_14_6_real_analysis_subsequence_principle
    (fun n : ℕ => ∫ x, h x ∂(Pseq n : Measure ℝ))
    (∫ x, h x ∂(P : Measure ℝ))
    (hspine.subsubsequence_test_integral_limit h)
