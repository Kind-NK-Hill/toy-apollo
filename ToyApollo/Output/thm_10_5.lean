import Mathlib
import ToyApollo.Output.def_10_2
import ToyApollo.Output.def_10_3
import ToyApollo.Output.thm_10_3

/-
TASK ID: thm_10_5
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter10-mean
TASK CONTENT:
\begin{thmbox}{10.5}
Convergence in $L^r$ norm implies convergence in probability.
\end{thmbox}

\textit{Proof}
Suppose $(X_n)_{n\geq 1}$ converges to $X$ in the $r$-th mean for some positive number $r$, i.e.,
\[
\mathbb{E}[\lvert X_n-X\rvert^r]\to 0
\]
as $n\to\infty$. For any $\epsilon>0$, we apply the Markov inequality to obtain
\[
P(\lvert X_n-X\rvert>\epsilon)
=P(\lvert X_n-X\rvert^r>\epsilon^r)
\leq
\frac{\mathbb{E}[\lvert X_n-X\rvert^r]}{\epsilon^r}
\to 0
\]
as $n\to\infty$. This proves that the sequence $(X_n)_{n=1}^{\infty}$ is converging to $X$ in probability.
\hfill $\square$
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped ENNReal

/-- Mathlib convergence in measure implies the local Definition 10.2 predicate. -/
theorem convergesInProbability_of_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (h : TendstoInMeasure μ Xn atTop X) :
    ConvergesInProbability μ Xn X := by
  intro ε hε
  have hnorm :=
    (MeasureTheory.tendstoInMeasure_iff_norm (μ := μ) (f := Xn) (g := X)).mp h ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hnorm
    (fun n => zero_le _) ?_
  intro n
  apply measure_mono
  intro ω hω
  have hle : ε ≤ |Xn n ω - X ω| := le_of_lt hω
  simpa [deviationEvent, Real.norm_eq_abs] using hle

/-- A compatibility bridge from Mathlib convergence in `L^p` to the local
Definition 10.2 predicate.  The source theorem below uses the textbook
`ConvergesInRthMean` interface. -/
theorem thm_10_5_of_tendsto_eLpNorm {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) {p : ENNReal} (hp_ne_zero : p ≠ 0)
    (hXn : ∀ n, AEStronglyMeasurable (Xn n) μ) (hX : AEStronglyMeasurable X μ)
    (hLp : Tendsto (fun n : ℕ => eLpNorm (Xn n - X) p μ) atTop (nhds 0)) :
    ConvergesInProbability μ Xn X :=
  convergesInProbability_of_tendstoInMeasure μ Xn X <|
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm hp_ne_zero hXn hX hLp

/-- The moment integrand from Definition 10.3 is measurable for random
variables. -/
theorem thm_10_5_moment_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) {r : ℝ}
    (hr : 1 ≤ r)
    (hXn : ∀ n, AEStronglyMeasurable (Xn n) μ) (hX : AEStronglyMeasurable X μ)
    (n : ℕ) :
    AEMeasurable
      (fun ω : Ω => ENNReal.ofReal (|Xn n ω - X ω| ^ r)) μ := by
  have hr_nonneg : 0 ≤ r := le_trans zero_le_one hr
  have hdiff : AEStronglyMeasurable (fun ω : Ω => Xn n ω - X ω) μ :=
    (hXn n).sub hX
  have hpow : AEMeasurable (fun ω : Ω => |Xn n ω - X ω| ^ r) μ := by
    simpa [Real.norm_eq_abs] using (hdiff.norm.aemeasurable.pow_const r)
  exact hpow.ennreal_ofReal

/-- The Markov step used in the textbook proof of Theorem 10.5, written
directly against the local `meanDeviationMoment` interface. -/
theorem thm_10_5_markov_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) {r ε : ℝ}
    (hr : 1 ≤ r) (hε : 0 < ε)
    (hXn : ∀ n, AEStronglyMeasurable (Xn n) μ) (hX : AEStronglyMeasurable X μ)
    (n : ℕ) :
    μ (deviationEvent Xn X n ε) ≤
      meanDeviationMoment μ Xn X r n / ENNReal.ofReal (ε ^ r) := by
  have hr_nonneg : 0 ≤ r := le_trans zero_le_one hr
  have hεr_pos : 0 < ε ^ r := Real.rpow_pos_of_pos hε r
  have hthreshold_ne_zero : ENNReal.ofReal (ε ^ r) ≠ 0 :=
    (ENNReal.ofReal_pos.2 hεr_pos).ne'
  have hthreshold_ne_top : ENNReal.ofReal (ε ^ r) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  have hmarkov :=
    MeasureTheory.meas_ge_le_lintegral_div
      (μ := μ)
      (f := fun ω : Ω => ENNReal.ofReal (|Xn n ω - X ω| ^ r))
      (thm_10_5_moment_aemeasurable μ Xn X hr hXn hX n)
      hthreshold_ne_zero hthreshold_ne_top
  let A : Set Ω :=
    {ω : Ω | ENNReal.ofReal (ε ^ r) ≤ ENNReal.ofReal (|Xn n ω - X ω| ^ r)}
  have hsubset : deviationEvent Xn X n ε ⊆ A := by
    intro ω hω
    have hle : ε ≤ |Xn n ω - X ω| := le_of_lt hω
    have hpow_le : ε ^ r ≤ |Xn n ω - X ω| ^ r :=
      Real.rpow_le_rpow hε.le hle hr_nonneg
    simpa using ENNReal.ofReal_le_ofReal hpow_le
  have hmeasure : μ (deviationEvent Xn X n ε) ≤ μ A :=
    measure_mono hsubset
  exact hmeasure.trans (by simpa [A, meanDeviationMoment] using hmarkov)

/-- Theorem 10.5: convergence in the local `r`-th mean of Definition 10.3
implies convergence in probability. -/
theorem thm_10_5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) {r : ℝ}
    (hXn : ∀ n, AEStronglyMeasurable (Xn n) μ) (hX : AEStronglyMeasurable X μ)
    (hMean : ConvergesInRthMean μ Xn X r) :
    ConvergesInProbability μ Xn X := by
  rcases hMean with ⟨hr, hmoment⟩
  intro ε hε
  have hbound : ∀ n : ℕ,
      μ (deviationEvent Xn X n ε) ≤
        meanDeviationMoment μ Xn X r n / ENNReal.ofReal (ε ^ r) := by
    intro n
    exact thm_10_5_markov_moment_bound μ Xn X hr hε hXn hX n
  have hscale :
      Tendsto
        (fun n : ℕ => meanDeviationMoment μ Xn X r n / ENNReal.ofReal (ε ^ r))
        atTop (nhds 0) := by
    have hεr_pos : 0 < ε ^ r := Real.rpow_pos_of_pos hε r
    have hthreshold_ne_zero : ENNReal.ofReal (ε ^ r) ≠ 0 :=
      (ENNReal.ofReal_pos.2 hεr_pos).ne'
    have hthreshold_ne_top : ENNReal.ofReal (ε ^ r) ≠ ∞ :=
      ENNReal.ofReal_ne_top
    have hinv_ne_top : (ENNReal.ofReal (ε ^ r))⁻¹ ≠ ∞ := by
      simp [hthreshold_ne_zero]
    have hmul :=
      ENNReal.Tendsto.mul_const hmoment
        (b := (ENNReal.ofReal (ε ^ r))⁻¹) (Or.inr hinv_ne_top)
    simpa [div_eq_mul_inv] using hmul
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hscale
    (fun _ => zero_le _) hbound
