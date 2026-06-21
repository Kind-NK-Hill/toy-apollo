import Mathlib
import ToyApollo.Output.def_14_3
import ToyApollo.Output.thm_14_5
import ToyApollo.Output.prob_14_12_mean_convergence_support

/-
TASK ID: prob_14_12
TYPE: Problem
SOURCE PLAN: chapter14-problems
TASK CONTENT:
\textbf{14.12.} (Uniform integrability) A sequence of random variables (Xn)\infty

n=1 is said to

be uniformly integrable if for every \epsilon> 0, there is a sufficiently large M such that

E[Xn1\vertXn\vert\geqM]\leq \epsilonfor all n. Prove the followings:

(a) A uniformly integrable sequence of random variables is tight.

(b) If a sequence of random variables is uniformly integrable and is converging in

probability, then it is converging in the mean.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal

noncomputable section

/-- The tail expectation `E[|X| 1{|X| >= M}]` for a law on `ℝ`, in the same
nonnegative extended-real form as the reviewed part (b) truncation route. -/
def prob_14_12_tailExpectation
    (P : ProbabilityMeasure ℝ) (M : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, Set.indicator {x : ℝ | M ≤ |x|} (fun y : ℝ => ENNReal.ofReal |y|) x
    ∂((P : ProbabilityMeasure ℝ) : Measure ℝ)

/-- Uniform integrability for a sequence of laws, in the form used to prove
tightness. -/
def prob_14_12_uniformIntegrableLaws
    (laws : ℕ → ProbabilityMeasure ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 ≤ M ∧
    ∀ n : ℕ, prob_14_12_tailExpectation (laws n) M ≤ ENNReal.ofReal ε

/-- The tail expectation of a push-forward law is the corresponding
variable-level tail expectation. -/
theorem prob_14_12_variable_tailExpectation_eq_law_tailExpectation
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (hμ : IsProbabilityMeasure μ)
    (X : Ω → ℝ) (hX : Measurable X) (M : ℝ) :
    prob_14_12_tailExpectation
      (ProbabilityMeasure.map (⟨μ, hμ⟩ : ProbabilityMeasure Ω) hX.aemeasurable) M =
      prob_14_12_variableTailExpectation μ X M := by
  let f : ℝ → ℝ≥0∞ :=
    fun x => Set.indicator {x : ℝ | M ≤ |x|}
      (fun y : ℝ => ENNReal.ofReal |y|) x
  have hf : Measurable f := by
    have hset : MeasurableSet {x : ℝ | M ≤ |x|} :=
      measurableSet_le measurable_const measurable_abs
    exact (ENNReal.measurable_ofReal.comp measurable_abs).indicator hset
  have hmap := MeasureTheory.lintegral_map (μ := μ) (f := f) (g := X) hf hX
  simpa [prob_14_12_tailExpectation, prob_14_12_variableTailExpectation, f,
    Function.comp_def, ProbabilityMeasure.map, Set.indicator] using hmap

/-- If the displayed laws are the push-forward laws of the random variables,
variable-level uniform integrability transfers to law-level uniform
integrability. -/
theorem prob_14_12_variable_ui_to_law_ui_of_distributions
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (hμ : IsProbabilityMeasure μ)
    (Xseq : ℕ → Ω → ℝ) (laws : ℕ → ProbabilityMeasure ℝ)
    (hXseq : ∀ n : ℕ, Measurable (Xseq n))
    (hlaws : ∀ n : ℕ,
      laws n =
        ProbabilityMeasure.map (⟨μ, hμ⟩ : ProbabilityMeasure Ω)
          (hXseq n).aemeasurable)
    (hUI : prob_14_12_uniformIntegrableVariables μ Xseq) :
    prob_14_12_uniformIntegrableLaws laws := by
  intro ε hε
  rcases hUI ε hε with ⟨M, hM, htail⟩
  refine ⟨M, hM, ?_⟩
  intro n
  rw [hlaws n,
    prob_14_12_variable_tailExpectation_eq_law_tailExpectation
      μ hμ (Xseq n) (hXseq n) M]
  exact htail n

/-- Source-level setup for part (a): the random variables induce the displayed
laws and their absolute tails are uniformly integrable. -/
structure prob_14_12_TightnessSetup (Ω : Type*) [MeasurableSpace Ω] where
  μ : Measure Ω
  Xseq : ℕ → Ω → ℝ
  laws : ℕ → ProbabilityMeasure ℝ
  μ_isProbability : IsProbabilityMeasure μ
  Xseq_measurable : ∀ n : ℕ, Measurable (Xseq n)
  laws_are_distributions :
    ∀ n : ℕ,
      laws n =
        ProbabilityMeasure.map (⟨μ, μ_isProbability⟩ : ProbabilityMeasure Ω)
          (Xseq_measurable n).aemeasurable
  uniform_integrable_variables :
    prob_14_12_uniformIntegrableVariables μ Xseq

/-- Tail expectations are monotone decreasing in the threshold. -/
theorem prob_14_12_tailExpectation_antitone
    (P : ProbabilityMeasure ℝ) {M N : ℝ} (hMN : M ≤ N) :
    prob_14_12_tailExpectation P N ≤ prob_14_12_tailExpectation P M := by
  refine lintegral_mono ?_
  intro x
  by_cases hN : N ≤ |x|
  · have hM : M ≤ |x| := le_trans hMN hN
    simp [Set.indicator, hN, hM]
  · simp [Set.indicator, hN]

/-- Markov's elementary pointwise estimate on the absolute-value tail. -/
theorem prob_14_12_tailMeasure_le_tailExpectation
    (P : ProbabilityMeasure ℝ) {M : ℝ} (hM : 1 ≤ M) :
    (P : Measure ℝ) {x : ℝ | M ≤ |x|} ≤
      prob_14_12_tailExpectation P M := by
  let s : Set ℝ := {x : ℝ | M ≤ |x|}
  have hs : MeasurableSet s :=
    measurableSet_le measurable_const measurable_abs
  have hmono :
      (∫⁻ x, Set.indicator s (fun _ : ℝ => (1 : ℝ≥0∞)) x ∂(P : Measure ℝ)) ≤
        ∫⁻ x, Set.indicator s (fun y : ℝ => ENNReal.ofReal |y|) x
          ∂(P : Measure ℝ) := by
    refine lintegral_mono ?_
    intro x
    by_cases hx : x ∈ s
    · have hxabs : 1 ≤ |x| := le_trans hM hx
      have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal |x| := by
        simpa using (ENNReal.ofReal_le_ofReal hxabs)
      simp [Set.indicator, hx, hone]
    · simp [Set.indicator, hx]
  have hmeasure_eq :
      (∫⁻ x, Set.indicator s (fun _ : ℝ => (1 : ℝ≥0∞)) x ∂(P : Measure ℝ)) =
        (P : Measure ℝ) s := by
    simpa using
      (MeasureTheory.lintegral_indicator_one (μ := (P : Measure ℝ)) hs)
  rw [hmeasure_eq] at hmono
  simpa [prob_14_12_tailExpectation, s] using hmono

/-- Convert a uniform tail-expectation bound into the strict real tail-mass
bound used by Theorem 14.5's elementary tightness bridge. -/
theorem prob_14_12_tailMass_lt_of_tailExpectation_bound
    (P : ProbabilityMeasure ℝ) {M ε δ : ℝ}
    (hM : 1 ≤ M) (hδpos : 0 < δ) (hδlt : δ < ε)
    (hbound : prob_14_12_tailExpectation P M ≤ ENNReal.ofReal δ) :
    thm_14_5_tailMass P M < ε := by
  have hstrict_sub : {x : ℝ | M < |x|} ⊆ {x : ℝ | M ≤ |x|} := by
    intro x hx
    exact le_of_lt (show M < |x| from hx)
  have hmeasure_le_ge :
      (P : Measure ℝ) {x : ℝ | M < |x|} ≤
        (P : Measure ℝ) {x : ℝ | M ≤ |x|} :=
    measure_mono hstrict_sub
  have hge_le_tail := prob_14_12_tailMeasure_le_tailExpectation P hM
  have hstrict_le_tail :
      (P : Measure ℝ) {x : ℝ | M < |x|} ≤
        prob_14_12_tailExpectation P M :=
    le_trans hmeasure_le_ge hge_le_tail
  have hstrict_le_delta :
      (P : Measure ℝ) {x : ℝ | M < |x|} ≤ ENNReal.ofReal δ :=
    le_trans hstrict_le_tail hbound
  have hεpos : 0 < ε := lt_trans hδpos hδlt
  have hlt_delta_eps : ENNReal.ofReal δ < ENNReal.ofReal ε :=
    (ENNReal.ofReal_lt_ofReal_iff hεpos).mpr hδlt
  have hlt : (P : Measure ℝ) {x : ℝ | M < |x|} < ENNReal.ofReal ε :=
    lt_of_le_of_lt hstrict_le_delta hlt_delta_eps
  rw [thm_14_5_tailMass, chapter14_tailMass, measureReal_def]
  exact ENNReal.toReal_lt_of_lt_ofReal hlt

/-- Law-level uniform integrability gives the uniform tail bound required by
Theorem 14.5's elementary tightness bridge. -/
theorem prob_14_12_uniformTailBound_of_uniformIntegrableLaws
    (laws : ℕ → ProbabilityMeasure ℝ)
    (hUI : prob_14_12_uniformIntegrableLaws laws) :
    thm_14_5_uniformTailBound laws := by
  intro ε hε
  have hδpos : 0 < ε / 2 := by linarith
  rcases hUI (ε / 2) hδpos with ⟨M, _hM_nonneg, htail⟩
  let R : ℝ := max M 1
  have hR_nonneg : 0 ≤ R :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right M 1)
  refine ⟨R, hR_nonneg, ?_⟩
  intro n
  have hMR : M ≤ R := le_max_left M 1
  have hR1 : 1 ≤ R := le_max_right M 1
  have htailR :
      prob_14_12_tailExpectation (laws n) R ≤
        prob_14_12_tailExpectation (laws n) M :=
    prob_14_12_tailExpectation_antitone (laws n) hMR
  have hbound :
      prob_14_12_tailExpectation (laws n) R ≤ ENNReal.ofReal (ε / 2) :=
    le_trans htailR (htail n)
  exact prob_14_12_tailMass_lt_of_tailExpectation_bound
    (laws n) hR1 hδpos (by linarith) hbound

/-- The Markov tail argument in Problem 14.12(a), now as theorem-level
evidence rather than a public setup field. -/
theorem prob_14_12_markov_tail_uniform_integrability_to_tightness
    (laws : ℕ → ProbabilityMeasure ℝ)
    (hUI : prob_14_12_uniformIntegrableLaws laws) :
    def_14_3 laws :=
  thm_14_5_of_uniformTailBound laws
    (prob_14_12_uniformTailBound_of_uniformIntegrableLaws laws hUI)

/-- Part (a): a uniformly integrable sequence is tight. -/
theorem prob_14_12_uniformIntegrable_tight
    {Ω : Type*} [MeasurableSpace Ω]
    (S : prob_14_12_TightnessSetup Ω) :
    def_14_3 S.laws :=
  prob_14_12_markov_tail_uniform_integrability_to_tightness S.laws
    (prob_14_12_variable_ui_to_law_ui_of_distributions
      S.μ S.μ_isProbability S.Xseq S.laws
      S.Xseq_measurable S.laws_are_distributions
      S.uniform_integrable_variables)

/-- Source-level setup for part (b): uniform integrability plus convergence in
probability, with the concrete measurability and finite-measure hypotheses
used by the reviewed truncation-route obligation. -/
structure prob_14_12_MeanConvergenceSetup
    (Ω : Type*) [MeasurableSpace Ω] where
  μ : Measure Ω
  Xseq : ℕ → Ω → ℝ
  X : Ω → ℝ
  μ_finite : IsFiniteMeasure μ
  Xseq_measurable : ∀ n : ℕ, Measurable (Xseq n)
  X_measurable : Measurable X
  uniform_integrable_variables :
    prob_14_12_uniformIntegrableVariables μ Xseq
  convergence_in_probability :
    prob_14_12_convergesInProbability μ Xseq X

/-- Problem 14.12: uniform integrability implies tightness, and together with
convergence in probability it implies convergence in mean. -/
theorem prob_14_12
    {Ω : Type*} [MeasurableSpace Ω]
    (T : prob_14_12_TightnessSetup Ω)
    (M : prob_14_12_MeanConvergenceSetup Ω) :
    def_14_3 T.laws ∧
      prob_14_12_convergesInMean M.μ M.Xseq M.X := by
  constructor
  · exact prob_14_12_uniformIntegrable_tight T
  · haveI : IsFiniteMeasure M.μ := M.μ_finite
    exact prob_14_12_uniformIntegrable_probability_to_mean
      M.μ M.Xseq M.X M.Xseq_measurable M.X_measurable
      M.uniform_integrable_variables M.convergence_in_probability
