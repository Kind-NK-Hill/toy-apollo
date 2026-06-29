import Mathlib
import ToyApollo.Output.def_10_1
import ToyApollo.Output.def_10_3

/-
TASK ID: ex_10_2_1
TYPE: Example_Proof
SOURCE PLAN: chapter10-mean
TASK CONTENT:
\textbf{Example 10.2.1 (Almost Sure Convergence But Not in the Mean)} \\
Let $\Omega=[0,1]$, and let $P$ be the Lebesgue measure on $[0,1]$. For $n=1,2,3,\ldots$, define
\[
X_n(\omega)\coloneqq n\cdot \mathbf{1}_{[0,1/n]}(\omega).
\]
The sequence of random variables $(X_n)_{n\geq 1}$ does not converge to $0$ in the mean, because
\[
\mathbb{E}[X_n-0]=\int_{[0,1/n]}n\,dP=1
\]
for all $n$. However, the sequence converges to $0$ a.s., because for each $\omega>0$, the sequence $(X_n(\omega))_{n\geq 1}$ will eventually be equal to $0$.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set
open scoped Topology ENNReal

noncomputable section

/-- The Lebesgue probability measure on the textbook sample space `[0,1]`,
represented as restricted Lebesgue measure on `ℝ`. -/
def ex_10_2_1_unitIntervalMeasure : Measure ℝ :=
  volume.restrict (Icc (0 : ℝ) 1)

/-- The textbook sequence `X_n(ω) = n * 1_[0,1/n](ω)`, with Lean's zero-based
index `n` representing the textbook index `n+1`. -/
def ex_10_2_1_sequence (n : ℕ) (ω : ℝ) : ℝ :=
  ((n : ℝ) + 1) *
    (Icc (0 : ℝ) (((n : ℝ) + 1)⁻¹)).indicator (fun _ => (1 : ℝ)) ω

/-- Away from the single exceptional point `0`, the textbook sequence is
eventually zero. -/
theorem ex_10_2_1_eventually_zero_at (ω : ℝ) (hω : ω ≠ 0) :
    Tendsto (fun n : ℕ => ex_10_2_1_sequence n ω) atTop (𝓝 0) := by
  have hEventually :
      ∀ᶠ n : ℕ in atTop, ex_10_2_1_sequence n ω = 0 := by
    by_cases hω_pos : 0 < ω
    · have hEventuallyBound :
          ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1)⁻¹ < ω := by
        have hlim :
            Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
          simpa [one_div] using
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        exact hlim.eventually_lt_const hω_pos
      filter_upwards [hEventuallyBound] with n hn
      unfold ex_10_2_1_sequence
      have hnot : ω ∉ Icc (0 : ℝ) (((n : ℝ) + 1)⁻¹) := by
        intro h
        exact not_le_of_gt hn h.2
      simp [Set.indicator, hnot]
    · have hω_neg : ω < 0 := lt_of_le_of_ne (not_lt.mp hω_pos) hω
      filter_upwards with n
      unfold ex_10_2_1_sequence
      have hnot : ω ∉ Icc (0 : ℝ) (((n : ℝ) + 1)⁻¹) := by
        intro h
        exact (not_le_of_gt hω_neg) h.1
      simp [Set.indicator, hnot]
  exact (tendsto_congr' hEventually).2 (tendsto_const_nhds (x := (0 : ℝ)))

/-- The sequence converges to zero almost surely; the only exceptional point is
`ω = 0`, which has restricted Lebesgue measure zero. -/
theorem ex_10_2_1_almost_sure :
    ConvergesAlmostSurely ex_10_2_1_unitIntervalMeasure
      ex_10_2_1_sequence (fun _ => 0) := by
  unfold ConvergesAlmostSurely
  have hAeNe : ∀ᵐ ω ∂ex_10_2_1_unitIntervalMeasure, ω ≠ 0 := by
    rw [ae_iff]
    change ex_10_2_1_unitIntervalMeasure {ω : ℝ | ¬ ω ≠ 0} = 0
    have hbad : {ω : ℝ | ¬ ω ≠ 0} = ({0} : Set ℝ) := by
      ext ω
      simp
    rw [hbad, ex_10_2_1_unitIntervalMeasure,
      Measure.restrict_apply (measurableSet_singleton (0 : ℝ))]
    have hinter : ({0} : Set ℝ) ∩ Icc (0 : ℝ) 1 = ({0} : Set ℝ) := by
      ext ω
      simp
    rw [hinter, measure_singleton]
  filter_upwards [hAeNe] with ω hω
  exact ex_10_2_1_eventually_zero_at ω hω

/-- The first absolute deviation moment is constantly one, matching the
textbook integral calculation `∫_[0,1/n] n dP = 1`. -/
theorem ex_10_2_1_meanDeviationMoment_eq_one (n : ℕ) :
    meanDeviationMoment ex_10_2_1_unitIntervalMeasure
      ex_10_2_1_sequence (fun _ => 0) 1 n = (1 : ENNReal) := by
  unfold meanDeviationMoment ex_10_2_1_unitIntervalMeasure ex_10_2_1_sequence
  let A : Set ℝ := Icc (0 : ℝ) (((n : ℝ) + 1)⁻¹)
  have hNpos : 0 < (n : ℝ) + 1 := by positivity
  have hNnonneg : 0 ≤ (n : ℝ) + 1 := hNpos.le
  have hfun :
      (fun ω : ℝ =>
          ENNReal.ofReal
            (|((n : ℝ) + 1) * A.indicator (fun _ => (1 : ℝ)) ω - 0| ^ (1 : ℝ))) =
        fun ω : ℝ => A.indicator (fun _ => ENNReal.ofReal ((n : ℝ) + 1)) ω := by
    funext ω
    by_cases hω : ω ∈ A
    · simp [Set.indicator, hω, abs_of_nonneg hNnonneg, Real.rpow_one]
    · simp [Set.indicator, hω, Real.rpow_one]
  change
    (∫⁻ ω,
      ENNReal.ofReal
        (|((n : ℝ) + 1) * A.indicator (fun _ => (1 : ℝ)) ω - 0| ^ (1 : ℝ))
        ∂volume.restrict (Icc (0 : ℝ) 1)) = 1
  rw [hfun]
  rw [lintegral_indicator measurableSet_Icc]
  rw [lintegral_const]
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
  rw [Measure.restrict_apply measurableSet_Icc]
  have hinter :
      A ∩ Icc (0 : ℝ) 1 = A := by
    ext ω
    constructor
    · intro h
      exact h.1
    · intro h
      refine ⟨h, ?_⟩
      constructor
      · exact h.1
      · have hle : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
          have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          exact inv_le_one_of_one_le₀ (by nlinarith : (1 : ℝ) ≤ (n : ℝ) + 1)
        exact h.2.trans hle
  rw [hinter, Real.volume_Icc]
  have hdiff : ((n : ℝ) + 1)⁻¹ - 0 = ((n : ℝ) + 1)⁻¹ := by ring
  rw [hdiff]
  have hofReal_inv :
      ENNReal.ofReal (((n : ℝ) + 1)⁻¹) =
        (ENNReal.ofReal ((n : ℝ) + 1))⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hNpos]
  rw [hofReal_inv]
  have h_ofReal_ne_zero : ENNReal.ofReal ((n : ℝ) + 1) ≠ 0 := by
    intro hzero
    have hle : (n : ℝ) + 1 ≤ 0 := ENNReal.ofReal_eq_zero.mp hzero
    exact (not_le_of_gt hNpos) hle
  exact ENNReal.mul_inv_cancel h_ofReal_ne_zero (by simp)

/-- Since the first moment stays equal to one, the sequence cannot converge to
zero in the mean. -/
theorem ex_10_2_1_not_mean :
    ¬ ConvergesInMean ex_10_2_1_unitIntervalMeasure
      ex_10_2_1_sequence (fun _ => 0) := by
  intro hmean
  rw [ConvergesInMean, ConvergesInRthMean] at hmean
  rcases hmean with ⟨_, hlim⟩
  have hconst :
      Tendsto
        (fun n : ℕ => meanDeviationMoment ex_10_2_1_unitIntervalMeasure
          ex_10_2_1_sequence (fun _ => 0) 1 n)
        atTop (nhds (1 : ENNReal)) := by
    simpa [ex_10_2_1_meanDeviationMoment_eq_one] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ENNReal)) atTop
        (nhds (1 : ENNReal)))
  have huniq := tendsto_nhds_unique hlim hconst
  exact one_ne_zero huniq.symm

/-- Example 10.2.1: the concrete sequence `n * 1_[0,1/n]` on `[0,1]`
converges to zero almost surely but not in the mean. -/
theorem ex_10_2_1 :
    ConvergesAlmostSurely ex_10_2_1_unitIntervalMeasure
      ex_10_2_1_sequence (fun _ => 0) ∧
      ¬ ConvergesInMean ex_10_2_1_unitIntervalMeasure
        ex_10_2_1_sequence (fun _ => 0) := by
  exact ⟨ex_10_2_1_almost_sure, ex_10_2_1_not_mean⟩
