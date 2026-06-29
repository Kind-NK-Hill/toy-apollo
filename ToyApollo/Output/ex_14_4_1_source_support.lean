import Mathlib
import ToyApollo.Output.thm_14_7

/-
TASK ID: ex_14_4_1
TYPE: Example_Proof
SOURCE PLAN: chapter14-central-limit-theorems
TASK CONTENT:
\textbf{Example 14.4.1 (Normal Approximation of Binomial Distribution)} \\

Suppose Xn's are iid. Bernoulli random variables with success probability p The mean and

variance of. Xn are p andp(1- p), respectively.
The sumSn =X 1 +X2 +\cdot\cdot\cdot+ Xn has distribution

Binom(n, p)By the central limit theorem,

Sn -np\sqrt np(1- p)

D

-\to N( 0,1).
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

/-- The Bernoulli mean in Example 14.4.1. -/
def ex_14_4_1_bernoulliMean (p : ℝ) : ℝ :=
  p

/-- The Bernoulli variance in Example 14.4.1. -/
def ex_14_4_1_bernoulliVariance (p : ℝ) : ℝ :=
  p * (1 - p)

theorem ex_14_4_1_bernoulliVariance_pos
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    0 < ex_14_4_1_bernoulliVariance p := by
  unfold ex_14_4_1_bernoulliVariance
  exact mul_pos hp (sub_pos.mpr hp1)

/-- Positivity of the Bernoulli standard deviation in Example 14.4.1. -/
theorem ex_14_4_1_sigma_pos
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    0 < Real.sqrt (ex_14_4_1_bernoulliVariance p) := by
  exact Real.sqrt_pos.2 (ex_14_4_1_bernoulliVariance_pos hp hp1)

/-- The textbook normalizing denominator `sqrt((n+1)p(1-p))`, with `n+1`
used for Lean's zero-based sequence. -/
def ex_14_4_1_binomialNormalizer (p : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt ((n + 1 : ℝ) * p * (1 - p))

/-- The Bernoulli characteristic function `1 - p + p e^{it}`. -/
def ex_14_4_1_bernoulliCharacteristic (p t : ℝ) : ℂ :=
  1 - (p : ℂ) + (p : ℂ) * Complex.exp (Complex.I * (t : ℂ))

/-- The characteristic function of a `Bin(n+1,p)` finite Bernoulli sum. -/
def ex_14_4_1_binomialCharacteristic
    (p : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (ex_14_4_1_bernoulliCharacteristic p t) ^ (n + 1)

/-- The point-mass formula for `Bin(n,p)` on `ℕ`. -/
def ex_14_4_1_binomialPMF (p : ℝ) (n k : ℕ) : ℝ :=
  if k ≤ n then (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) else 0

/-- Source-level Bernoulli atom statement for a real-valued `{0,1}` random
variable with success probability `p`.

This is the textbook hypothesis "`X_k` is Bernoulli(p)".  The derived moment
and finite-sum facts below are intentionally not setup fields. -/
def ex_14_4_1_hasBernoulliAtomLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (p : ℝ) : Prop :=
  (P {ω | X ω = 1}).toReal = p ∧
    (P {ω | X ω = 0}).toReal = 1 - p ∧
      P {ω | X ω ≠ 0 ∧ X ω ≠ 1} = 0

/-- Source-level data for the iid sequence and parameter in Example 14.4.1.

The fields deliberately stop before the Bernoulli law and its consequences.
Those are named below as concrete source/bridge propositions rather than setup
fields, so semantic review can track the remaining theorem-level work. -/
structure ex_14_4_1_BernoulliSourceSetup
    (Ω : Type*) [MeasurableSpace Ω] where
  P : Measure Ω
  isProbabilityMeasure : IsProbabilityMeasure P
  X : ℕ → Ω → ℝ
  p : ℝ
  p_pos : 0 < p
  p_lt_one : p < 1
  hX : ∀ k : ℕ, AEMeasurable (X k) P
  hIndep : ProbabilityTheory.iIndepFun X P
  hIdent : ∀ k : ℕ, IdentDistrib (X k) (X 0) P P

/-- Source proposition: every variable in the iid sequence has the Bernoulli(p)
atom law.  This is separated from the setup structure so it is not hidden as a
public field. -/
def ex_14_4_1_bernoulliSourceLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω) : Prop :=
  ∀ k : ℕ, ex_14_4_1_hasBernoulliAtomLaw S.P (S.X k) S.p

/-- If the representative variable `X_0` has the Bernoulli(p) atom law, then
the identical-distribution part of the iid source setup transports that law to
every `X_k`.  This records the source assumption as theorem-level evidence
without making the Bernoulli law a setup field. -/
theorem ex_14_4_1_bernoulliSourceLaw_of_zero_atomLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω)
    (hAtom0 : ex_14_4_1_hasBernoulliAtomLaw S.P (S.X 0) S.p) :
    ex_14_4_1_bernoulliSourceLaw S := by
  intro k
  rcases hAtom0 with ⟨hOne, hZero, hSupport⟩
  have hIdent := S.hIdent k
  have hOneMeasure :
      S.P {ω | S.X k ω = 1} = S.P {ω | S.X 0 ω = 1} := by
    simpa using
      hIdent.measure_preimage_eq (s := ({1} : Set ℝ)) (by measurability)
  have hZeroMeasure :
      S.P {ω | S.X k ω = 0} = S.P {ω | S.X 0 ω = 0} := by
    simpa using
      hIdent.measure_preimage_eq (s := ({0} : Set ℝ)) (by measurability)
  have hSupportMeasure :
      S.P {ω | S.X k ω ≠ 0 ∧ S.X k ω ≠ 1} =
        S.P {ω | S.X 0 ω ≠ 0 ∧ S.X 0 ω ≠ 1} := by
    simpa using
      hIdent.measure_preimage_eq
        (s := {x : ℝ | x ≠ 0 ∧ x ≠ 1}) (by measurability)
  exact ⟨by rw [hOneMeasure, hOne],
    by rw [hZeroMeasure, hZero],
    by rw [hSupportMeasure, hSupport]⟩

/-- A measurable version of the Bernoulli success event `{X = 1}`. -/
def ex_14_4_1_bernoulliSuccessEvent
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) : Set Ω :=
  toMeasurable P {ω | X ω = 1}

/-- The `{0,1}` indicator associated to the Bernoulli success event. -/
def ex_14_4_1_bernoulliSuccessIndicator
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) : Ω → ℝ :=
  (ex_14_4_1_bernoulliSuccessEvent P X).indicator (fun _ => (1 : ℝ))

theorem ex_14_4_1_bernoulli_ae_eq_successIndicator
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {p : ℝ}
    (hX : AEMeasurable X P)
    (hAtom : ex_14_4_1_hasBernoulliAtomLaw P X p) :
    X =ᵐ[P] ex_14_4_1_bernoulliSuccessIndicator P X := by
  rcases hAtom with ⟨_hOne, _hZero, hSupport⟩
  have hSupportAe : ∀ᵐ ω ∂P, X ω = 0 ∨ X ω = 1 := by
    rw [ae_iff]
    simpa [not_or] using hSupport
  have hSuccessNullMeasurable :
      NullMeasurableSet {ω | X ω = 1} P := by
    simpa [Set.preimage, Set.mem_singleton_iff] using
      hX.nullMeasurableSet_preimage (measurableSet_singleton (1 : ℝ))
  have hSuccessAe :
      ex_14_4_1_bernoulliSuccessEvent P X =ᵐ[P] {ω | X ω = 1} := by
    exact hSuccessNullMeasurable.toMeasurable_ae_eq
  filter_upwards [hSupportAe, hSuccessAe] with ω hSupportω hSuccessω
  rcases hSupportω with hZero | hOne
  · have hNotMem : ω ∉ ex_14_4_1_bernoulliSuccessEvent P X := by
      intro hmem
      have hx1 : X ω = 1 := hSuccessω.mp hmem
      linarith
    simp [ex_14_4_1_bernoulliSuccessIndicator, hZero, Set.indicator,
      hNotMem]
  · have hMem : ω ∈ ex_14_4_1_bernoulliSuccessEvent P X :=
      hSuccessω.mpr hOne
    simp [ex_14_4_1_bernoulliSuccessIndicator, hOne, Set.indicator, hMem]

theorem ex_14_4_1_bernoulli_memLp_two_of_atomLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} {p : ℝ}
    (hX : AEMeasurable X P)
    (hAtom : ex_14_4_1_hasBernoulliAtomLaw P X p) :
    MemLp X (2 : ENNReal) P := by
  rcases hAtom with ⟨_hOne, _hZero, hSupport⟩
  have hBound : ∀ᵐ ω ∂P, X ω ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    refine measure_mono_null ?_ hSupport
    intro ω hω
    constructor
    · intro hZero
      exact hω (by simp [Set.mem_Icc, hZero])
    · intro hOne
      exact hω (by simp [Set.mem_Icc, hOne])
  exact memLp_of_bounded hBound hX.aestronglyMeasurable (2 : ENNReal)

theorem ex_14_4_1_bernoulli_integrable_of_atomLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} {p : ℝ}
    (hX : AEMeasurable X P)
    (hAtom : ex_14_4_1_hasBernoulliAtomLaw P X p) :
    Integrable X P := by
  exact (ex_14_4_1_bernoulli_memLp_two_of_atomLaw hX hAtom).integrable
    (by norm_num)

theorem ex_14_4_1_bernoulli_square_ae_eq_successIndicator
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {p : ℝ}
    (hX : AEMeasurable X P)
    (hAtom : ex_14_4_1_hasBernoulliAtomLaw P X p) :
    (fun ω => (X ω) ^ 2) =ᵐ[P]
      ex_14_4_1_bernoulliSuccessIndicator P X := by
  have hAe :=
    ex_14_4_1_bernoulli_ae_eq_successIndicator (P := P) hX hAtom
  filter_upwards [hAe] with ω hω
  rw [hω]
  by_cases hMem : ω ∈ ex_14_4_1_bernoulliSuccessEvent P X
  · simp [ex_14_4_1_bernoulliSuccessIndicator, Set.indicator, hMem]
  · simp [ex_14_4_1_bernoulliSuccessIndicator, Set.indicator, hMem]

theorem ex_14_4_1_bernoulli_square_integrable_of_atomLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} {p : ℝ}
    (hX : AEMeasurable X P)
    (hAtom : ex_14_4_1_hasBernoulliAtomLaw P X p) :
    Integrable (fun ω => (X ω) ^ 2) P := by
  have hEventMeasurable :
      MeasurableSet (ex_14_4_1_bernoulliSuccessEvent P X) := by
    exact measurableSet_toMeasurable P {ω | X ω = 1}
  have hIndicatorIntegrable :
      Integrable (ex_14_4_1_bernoulliSuccessIndicator P X) P := by
    simpa [ex_14_4_1_bernoulliSuccessIndicator] using
      (integrable_const (μ := P) (1 : ℝ)).indicator hEventMeasurable
  exact hIndicatorIntegrable.congr
    (ex_14_4_1_bernoulli_square_ae_eq_successIndicator
      (P := P) hX hAtom).symm

theorem ex_14_4_1_bernoulli_mean_of_atomLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {p : ℝ}
    (hX : AEMeasurable X P)
    (hAtom : ex_14_4_1_hasBernoulliAtomLaw P X p) :
    P[X] = ex_14_4_1_bernoulliMean p := by
  rcases hAtom with ⟨hOne, _hZero, _hSupport⟩
  have hAe :=
    ex_14_4_1_bernoulli_ae_eq_successIndicator (P := P) hX
      (show ex_14_4_1_hasBernoulliAtomLaw P X p from ⟨hOne, _hZero, _hSupport⟩)
  calc
    P[X] = ∫ ω, ex_14_4_1_bernoulliSuccessIndicator P X ω ∂P := by
      exact integral_congr_ae hAe
    _ = P.real (ex_14_4_1_bernoulliSuccessEvent P X) := by
      simpa [ex_14_4_1_bernoulliSuccessIndicator] using
        (integral_indicator_one
          (μ := P) (s := ex_14_4_1_bernoulliSuccessEvent P X)
          (measurableSet_toMeasurable P {ω | X ω = 1}))
    _ = (P {ω | X ω = 1}).toReal := by
      rw [measureReal_def, ex_14_4_1_bernoulliSuccessEvent,
        measure_toMeasurable]
    _ = ex_14_4_1_bernoulliMean p := by
      simpa [ex_14_4_1_bernoulliMean] using hOne

theorem ex_14_4_1_bernoulli_secondMoment_of_atomLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {p : ℝ}
    (hX : AEMeasurable X P)
    (hAtom : ex_14_4_1_hasBernoulliAtomLaw P X p) :
    P[fun ω => (X ω) ^ 2] = ex_14_4_1_bernoulliMean p := by
  rcases hAtom with ⟨hOne, _hZero, _hSupport⟩
  have hSqAe :=
    ex_14_4_1_bernoulli_square_ae_eq_successIndicator (P := P) hX
      (show ex_14_4_1_hasBernoulliAtomLaw P X p from ⟨hOne, _hZero, _hSupport⟩)
  calc
    P[fun ω => (X ω) ^ 2] =
        ∫ ω, ex_14_4_1_bernoulliSuccessIndicator P X ω ∂P := by
      exact integral_congr_ae hSqAe
    _ = P.real (ex_14_4_1_bernoulliSuccessEvent P X) := by
      simpa [ex_14_4_1_bernoulliSuccessIndicator] using
        (integral_indicator_one
          (μ := P) (s := ex_14_4_1_bernoulliSuccessEvent P X)
          (measurableSet_toMeasurable P {ω | X ω = 1}))
    _ = (P {ω | X ω = 1}).toReal := by
      rw [measureReal_def, ex_14_4_1_bernoulliSuccessEvent,
        measure_toMeasurable]
    _ = ex_14_4_1_bernoulliMean p := by
      simpa [ex_14_4_1_bernoulliMean] using hOne

theorem ex_14_4_1_bernoulli_variance_of_atomLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} {p : ℝ}
    (hX : AEMeasurable X P)
    (hAtom : ex_14_4_1_hasBernoulliAtomLaw P X p)
    (hp : 0 < p) (hp1 : p < 1) :
    ProbabilityTheory.variance X P =
      (Real.sqrt (ex_14_4_1_bernoulliVariance p)) ^ 2 := by
  have hLp := ex_14_4_1_bernoulli_memLp_two_of_atomLaw hX hAtom
  have hMean := ex_14_4_1_bernoulli_mean_of_atomLaw (P := P) hX hAtom
  have hSecond :=
    ex_14_4_1_bernoulli_secondMoment_of_atomLaw (P := P) hX hAtom
  calc
    ProbabilityTheory.variance X P =
        P[fun ω => (X ω) ^ 2] - P[X] ^ 2 := by
      simpa [Pi.pow_apply] using
        (ProbabilityTheory.variance_eq_sub (μ := P) (X := X) hLp)
    _ = p * (1 - p) := by
      rw [hSecond, hMean]
      simp [ex_14_4_1_bernoulliMean]
      ring
    _ = (Real.sqrt (ex_14_4_1_bernoulliVariance p)) ^ 2 := by
      rw [Real.sq_sqrt (le_of_lt (ex_14_4_1_bernoulliVariance_pos hp hp1))]
      rfl

/-- The finite Bernoulli sum `X_0 + ... + X_n`, corresponding to the book's
`S_(n+1)` under zero-based indexing. -/
def ex_14_4_1_partialSum
    {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ k : Fin (n + 1), X k.val ω

theorem ex_14_4_1_partialSum_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℕ → Ω → ℝ) (hX : ∀ k : ℕ, AEMeasurable (X k) P) (n : ℕ) :
    AEMeasurable (ex_14_4_1_partialSum X n) P := by
  unfold ex_14_4_1_partialSum
  fun_prop

/-- The actual laws of the finite Bernoulli sums from the source sequence. -/
def ex_14_4_1_binomialSumLaws
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω) :
    ℕ → ProbabilityMeasure ℝ :=
  letI : IsProbabilityMeasure S.P := S.isProbabilityMeasure
  fun n =>
    thm_14_7_law S.P (ex_14_4_1_partialSum S.X n)
      (ex_14_4_1_partialSum_aemeasurable S.X S.hX n)

/-- The actual standardized finite-sum laws consumed by `thm_14_7`.  This is
defined directly rather than supplied by a public equality field. -/
def ex_14_4_1_standardizedBinomialLaws
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω) :
    ℕ → ProbabilityMeasure ℝ :=
  letI : IsProbabilityMeasure S.P := S.isProbabilityMeasure
  thm_14_7_standardizedSumLaws S.P S.X
    (ex_14_4_1_bernoulliMean S.p)
    (Real.sqrt (ex_14_4_1_bernoulliVariance S.p)) S.hX

/-- Open bridge obligation: derive integrability, mean `p`, and variance
`p(1-p)` from the Bernoulli atom law of `X_0`. -/
def ex_14_4_1_bernoulliMomentBridge
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω) : Prop :=
  Integrable (S.X 0) S.P ∧
    Integrable (fun ω => (S.X 0 ω) ^ 2) S.P ∧
      S.P[S.X 0] = ex_14_4_1_bernoulliMean S.p ∧
        ProbabilityTheory.variance (S.X 0) S.P =
          (Real.sqrt (ex_14_4_1_bernoulliVariance S.p)) ^ 2

/-- Bernoulli moment bridge derived from the source atom law, rather than
assumed as setup data. -/
theorem ex_14_4_1_bernoulliMomentBridge_of_sourceLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω)
    (hSource : ex_14_4_1_bernoulliSourceLaw S) :
    ex_14_4_1_bernoulliMomentBridge S := by
  letI : IsProbabilityMeasure S.P := S.isProbabilityMeasure
  have hAtom0 : ex_14_4_1_hasBernoulliAtomLaw S.P (S.X 0) S.p :=
    hSource 0
  exact ⟨
    ex_14_4_1_bernoulli_integrable_of_atomLaw (P := S.P)
      (S.hX 0) hAtom0,
    ex_14_4_1_bernoulli_square_integrable_of_atomLaw (P := S.P)
      (S.hX 0) hAtom0,
    ex_14_4_1_bernoulli_mean_of_atomLaw (P := S.P)
      (S.hX 0) hAtom0,
    ex_14_4_1_bernoulli_variance_of_atomLaw (P := S.P)
      (S.hX 0) hAtom0 S.p_pos S.p_lt_one⟩

/-- Bridge obligation: derive that the finite Bernoulli sums have the
`Bin(n+1,p)` point-mass law. -/
def ex_14_4_1_binomialFiniteSumBridge
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω) : Prop :=
  ∀ n k : ℕ,
    (S.P {ω | ex_14_4_1_partialSum S.X n ω = (k : ℝ)}).toReal =
      ex_14_4_1_binomialPMF S.p (n + 1) k

/-- The concrete source bridges still open for Example 14.4.1.  This replaces
the previous public setup fields for Bernoulli law, binomial sums, and
standardized/normal transport equalities.  The moment bridge is now proved from
the source Bernoulli law above. -/
def ex_14_4_1_resolvedSourceBridges
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω) : Prop :=
  ex_14_4_1_bernoulliSourceLaw S ∧
    ex_14_4_1_binomialFiniteSumBridge S

/-- The final source conclusion, using the actual standardized finite-sum laws
associated to the Bernoulli sequence. -/
def ex_14_4_1_sourceConclusion
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω) : Prop :=
  Tendsto (ex_14_4_1_standardizedBinomialLaws S)
    atTop (𝓝 thm_14_7_standardNormalLaw)

/-- The source route as a reviewable object: source Bernoulli data,
theorem-level Bernoulli/binomial bridges, and the CLT conclusion. -/
def ex_14_4_1_sourceRoute
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω) : Prop :=
  ex_14_4_1_resolvedSourceBridges S ∧
    ex_14_4_1_sourceConclusion S

/-- The CLT step once the explicit Bernoulli moment and finite-sum bridges have
been supplied by future theorem-level work. -/
theorem ex_14_4_1_normalApproximation_of_resolvedSourceBridges
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω)
    (hBridge : ex_14_4_1_resolvedSourceBridges S) :
    ex_14_4_1_sourceConclusion S := by
  letI : IsProbabilityMeasure S.P := S.isProbabilityMeasure
  rcases hBridge with ⟨hBernoulliSource, _hBinomial⟩
  have hMoment :
      ex_14_4_1_bernoulliMomentBridge S :=
    ex_14_4_1_bernoulliMomentBridge_of_sourceLaw S hBernoulliSource
  rcases hMoment with ⟨hIntegrable, hSquareIntegrable, hMean, hVariance⟩
  simpa [ex_14_4_1_sourceConclusion,
    ex_14_4_1_standardizedBinomialLaws] using
    thm_14_7 S.P S.X (ex_14_4_1_bernoulliMean S.p)
      (Real.sqrt (ex_14_4_1_bernoulliVariance S.p))
      S.hX S.hIndep S.hIdent hIntegrable hSquareIntegrable hMean hVariance
      (ex_14_4_1_sigma_pos S.p_pos S.p_lt_one)

/-- The CLT step directly from the Bernoulli source atom law. -/
theorem ex_14_4_1_normalApproximation_of_sourceLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω)
    (hSource : ex_14_4_1_bernoulliSourceLaw S) :
    ex_14_4_1_sourceConclusion S := by
  letI : IsProbabilityMeasure S.P := S.isProbabilityMeasure
  have hMoment :
      ex_14_4_1_bernoulliMomentBridge S :=
    ex_14_4_1_bernoulliMomentBridge_of_sourceLaw S hSource
  rcases hMoment with ⟨hIntegrable, hSquareIntegrable, hMean, hVariance⟩
  simpa [ex_14_4_1_sourceConclusion,
    ex_14_4_1_standardizedBinomialLaws] using
    thm_14_7 S.P S.X (ex_14_4_1_bernoulliMean S.p)
      (Real.sqrt (ex_14_4_1_bernoulliVariance S.p))
      S.hX S.hIndep S.hIdent hIntegrable hSquareIntegrable hMean hVariance
      (ex_14_4_1_sigma_pos S.p_pos S.p_lt_one)

/-- The same conclusion in the weak-limit form exported by Theorem 14.7 and
Theorem 14.1, still conditional on the explicit source bridge obligations. -/
theorem ex_14_4_1_weakLimit_by_CLT_of_resolvedSourceBridges
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω)
    (hBridge : ex_14_4_1_resolvedSourceBridges S) :
    thm_14_1_weakLimit (ex_14_4_1_standardizedBinomialLaws S) := by
  refine ⟨thm_14_7_standardNormalLaw, ?_⟩
  exact ex_14_4_1_normalApproximation_of_resolvedSourceBridges S hBridge

theorem ex_14_4_1_sourceRoute_of_resolvedSourceBridges
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω)
    (hBridge : ex_14_4_1_resolvedSourceBridges S) :
    ex_14_4_1_sourceRoute S := by
  exact ⟨hBridge,
    ex_14_4_1_normalApproximation_of_resolvedSourceBridges S hBridge⟩

/-- Example 14.4.1: for iid Bernoulli variables with success probability `p`,
the standardized binomial finite-sum laws converge in distribution to the
standard normal law, once the concrete Bernoulli moment and binomial finite-sum
bridges are proved.  The bridge obligations are named above rather than hidden
as public setup fields or private axioms. -/
theorem ex_14_4_1_support_result
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω)
    (hSource : ex_14_4_1_bernoulliSourceLaw S) :
    Tendsto (ex_14_4_1_standardizedBinomialLaws S)
      atTop (𝓝 thm_14_7_standardNormalLaw) :=
  ex_14_4_1_normalApproximation_of_sourceLaw S hSource


