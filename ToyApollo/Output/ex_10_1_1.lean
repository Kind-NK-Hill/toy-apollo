import Mathlib
import ToyApollo.Output.def_10_1
import ToyApollo.Output.def_10_2
import ToyApollo.Output.thm_5_9

/-
TASK ID: ex_10_1_1
TYPE: Example_Proof
SOURCE PLAN: chapter10-almost-sure-probability
TASK CONTENT:
\textbf{Example 10.1.1 (An Example of Convergence in Probability But Not a.s.)} \\
Let $X_n$ be a sequence of independent binary random variables, with probability distribution specified by
\[
P(X_n=1)=\frac{1}{n}, \qquad P(X_n=0)=1-\frac{1}{n}.
\]
This sequence converges to $0$ in probability. However, by the Borel--Cantelli lemma (Theorem 5.9), $X_n$ is equal to $1$ infinitely often with probability $1$. Hence, with probability $1$, it does not converge to $0$.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

/-- The harmonic probabilities in Example 10.1.1 diverge as an `ENNReal` series. -/
theorem ex_10_1_1_harmonic_ennreal_tsum :
    (∑' n : ℕ, ((n.succ : ℝ≥0∞)⁻¹)) = ∞ := by
  have hnot :
      ¬ Summable (fun n : ℕ => (((n.succ : ℝ≥0)⁻¹ : ℝ≥0) : ℝ)) := by
    have hreal : ¬ Summable (fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ))) := by
      exact
        mt (_root_.summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).1
          Real.not_summable_one_div_natCast
    simpa [Nat.succ_eq_add_one, one_div] using hreal
  have htop :
      (∑' n : ℕ, (((n.succ : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞)) = ∞ :=
    (ENNReal.tsum_coe_eq_top_iff_not_summable_coe).2 hnot
  simpa using htop

/--
For a binary sequence, if `P(X_n = 1) = 1 / (n + 1)`, then `X_n -> 0`
in probability. The `n + 1` indexing is the Lean zero-based version of the
textbook's `n >= 1` convention.
-/
theorem ex_10_1_1_convergesInProbability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xn : ℕ → Ω → ℝ)
    (h_binary : ∀ n : ℕ, ∀ ω : Ω, Xn n ω = 0 ∨ Xn n ω = 1)
    (h_prob_one :
      ∀ n : ℕ, μ {ω : Ω | Xn n ω = 1} = ((n.succ : ℝ≥0∞)⁻¹)) :
    ConvergesInProbability μ Xn (fun _ => 0) := by
  intro ε hε
  have hmodel :
      Tendsto (fun n : ℕ => ((n.succ : ℝ≥0∞)⁻¹)) atTop (nhds 0) := by
    simpa [Function.comp_def, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
      (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
  have hsuccess :
      Tendsto (fun n : ℕ => μ {ω : Ω | Xn n ω = 1}) atTop (nhds 0) :=
    hmodel.congr' (Eventually.of_forall fun n => (h_prob_one n).symm)
  have hle :
      ∀ n : ℕ,
        μ (deviationEvent Xn (fun _ => 0) n ε) ≤
          μ {ω : Ω | Xn n ω = 1} := by
    intro n
    apply measure_mono
    intro ω hω
    rcases h_binary n ω with hzero | hone
    · exfalso
      have hnot : ¬ |Xn n ω - (0 : ℝ)| > ε := by
        rw [hzero]
        simpa using not_lt.mpr hε.le
      exact hnot hω
    · exact hone
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsuccess
    (Eventually.of_forall fun n => zero_le _)
    (Eventually.of_forall hle)

/-- Borel-Cantelli applied to the source success events `{X_n = 1}`. -/
theorem ex_10_1_1_limsup_one {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Xn : ℕ → Ω → ℝ)
    (h_meas_one : ∀ n : ℕ, MeasurableSet {ω : Ω | Xn n ω = 1})
    (h_indep_one : ProbabilityTheory.iIndepSet (fun n : ℕ => {ω : Ω | Xn n ω = 1}) μ)
    (h_prob_one :
      ∀ n : ℕ, μ {ω : Ω | Xn n ω = 1} = ((n.succ : ℝ≥0∞)⁻¹)) :
    μ (limsup (fun n : ℕ => {ω : Ω | Xn n ω = 1}) atTop) = 1 := by
  have hseries : (∑' n : ℕ, μ {ω : Ω | Xn n ω = 1}) = ∞ := by
    simpa [h_prob_one] using ex_10_1_1_harmonic_ennreal_tsum
  exact thm_5_9 (P := μ) (A := fun n : ℕ => {ω : Ω | Xn n ω = 1})
    h_meas_one h_indep_one hseries

/-- Infinitely many visits to the value `1` rule out pointwise convergence to `0`. -/
theorem ex_10_1_1_limsup_one_subset_not_tendsto_zero {Ω : Type*} (Xn : ℕ → Ω → ℝ) :
    limsup (fun n : ℕ => {ω : Ω | Xn n ω = 1}) atTop ⊆
      {ω : Ω | ¬ Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (0 : ℝ))} := by
  intro ω hω hlim
  rw [mem_limsup_iff_frequently_mem, frequently_atTop] at hω
  have hsmall :
      ∀ᶠ n : ℕ in atTop, Xn n ω ∈ Metric.ball (0 : ℝ) (1 / 2 : ℝ) :=
    hlim.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num))
  rw [eventually_atTop] at hsmall
  rcases hsmall with ⟨N, hN⟩
  rcases hω N with ⟨n, hnN, hn_one⟩
  have hnsmall : Xn n ω ∈ Metric.ball (0 : ℝ) (1 / 2 : ℝ) := hN n hnN
  have hdist : dist (Xn n ω) 0 < (1 / 2 : ℝ) := by
    simpa [Metric.mem_ball] using hnsmall
  rw [hn_one] at hdist
  norm_num [Real.dist_eq] at hdist

/--
The Borel-Cantelli infinitely-often conclusion contradicts almost-sure
convergence to zero; this is the source's final pointwise step, not a premise.
-/
theorem ex_10_1_1_not_convergesAlmostSurely_of_limsup_one {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (Xn : ℕ → Ω → ℝ)
    (h_limsup_one : μ (limsup (fun n : ℕ => {ω : Ω | Xn n ω = 1}) atTop) = 1) :
    ¬ ConvergesAlmostSurely μ Xn (fun _ => 0) := by
  intro hAS
  have hbad_zero :
      μ {ω : Ω | ¬ Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (0 : ℝ))} = 0 :=
    ae_iff.1 hAS
  have hio_zero :
      μ (limsup (fun n : ℕ => {ω : Ω | Xn n ω = 1}) atTop) = 0 :=
    MeasureTheory.measure_mono_null
      (ex_10_1_1_limsup_one_subset_not_tendsto_zero Xn) hbad_zero
  rw [h_limsup_one] at hio_zero
  exact one_ne_zero hio_zero

/--
Example 10.1.1, stated from the source data: a zero-based sequence of
independent binary random variables with `P(X_n = 1) = 1/(n+1)` and
`P(X_n = 0) = 1 - 1/(n+1)` converges to `0` in probability but not almost surely.
-/
theorem ex_10_1_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Xn : ℕ → Ω → ℝ)
    (h_binary : ∀ n : ℕ, ∀ ω : Ω, Xn n ω = 0 ∨ Xn n ω = 1)
    (h_meas_one : ∀ n : ℕ, MeasurableSet {ω : Ω | Xn n ω = 1})
    (h_indep_one : ProbabilityTheory.iIndepSet (fun n : ℕ => {ω : Ω | Xn n ω = 1}) μ)
    (h_prob_one :
      ∀ n : ℕ, μ {ω : Ω | Xn n ω = 1} = ((n.succ : ℝ≥0∞)⁻¹))
    (h_prob_zero :
      ∀ n : ℕ, μ {ω : Ω | Xn n ω = 0} = 1 - ((n.succ : ℝ≥0∞)⁻¹)) :
    ConvergesInProbability μ Xn (fun _ => 0) ∧
      ¬ ConvergesAlmostSurely μ Xn (fun _ => 0) := by
  have _source_zero_mass := h_prob_zero
  have h_in_prob : ConvergesInProbability μ Xn (fun _ => 0) :=
    ex_10_1_1_convergesInProbability μ Xn h_binary h_prob_one
  have h_limsup_one :
      μ (limsup (fun n : ℕ => {ω : Ω | Xn n ω = 1}) atTop) = 1 :=
    ex_10_1_1_limsup_one μ Xn h_meas_one h_indep_one h_prob_one
  exact ⟨h_in_prob, ex_10_1_1_not_convergesAlmostSurely_of_limsup_one μ Xn h_limsup_one⟩
