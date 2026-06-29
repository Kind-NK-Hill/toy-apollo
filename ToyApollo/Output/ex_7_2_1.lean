import Mathlib

/-
TASK ID: ex_7_2_1
TYPE: Example_Proof
SOURCE PLAN: 26_chap7_fatou_dct
TASK CONTENT:
\textbf{Example 7.2.1 (An Example That Illustrates Fatou's Lemma)} \\
We give an example to help us remember the direction of the inequality in Fatou's lemma. Consider an example with sample space $\Omega=\mathbb{R}$ with the Lebesgue measure on $\mathbb{R}$. For $n\ge 1$, let $X_n$ be the simple function $n1_{[0,1/n]}$. The integral of $X_n$ over $\mathbb{R}$ is equal to $1$ for all $n$. Therefore $\liminf_n \int X_n\, d\mu = 1$.

However for each nonzero $\omega \in \mathbb{R}$, $\liminf_n X_n(\omega)=0$, and at the point $\omega=0$, the liminf is equal to $\infty$. Thus, we see that $X(\omega)=\limsup_n X_n(\omega)$ is equal to
\[
X(\omega)=
\begin{cases}
0 & \text{if } \omega \neq 0,\\
\infty & \text{if } \omega = 0.
\end{cases}
\]

This yields $\int X\, d\mu = 0$. Informally, Fatou's lemma says that the integral becomes larger if we pull the liminf operator outside of the integral sign.

The next example demonstrates the importance of understanding the conditions under which the limit and integral can be interchanged.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Filter Set
open scoped ENNReal

/--
Zero-based reindexing of the textbook sequence `n 1_[0,1/n]`.
The Lean index `n` corresponds to the textbook index `n + 1`.
-/
noncomputable def fatouIllustrationSeq (n : ℕ) (x : ℝ) : ℝ≥0∞ :=
  (Set.Icc (0 : ℝ) (1 / (n + 1 : ℝ))).indicator (fun _ => ((n + 1 : ℕ) : ℝ≥0∞)) x

/-- The pointwise limit profile described in Example 7.2.1. -/
noncomputable def fatouIllustrationLimit (x : ℝ) : ℝ≥0∞ :=
  ({(0 : ℝ)} : Set ℝ).indicator (fun _ => (∞ : ℝ≥0∞)) x

/-- A faithful package for the Fatou-lemma counterexample in Example 7.2.1. -/
structure FatouLemmaIllustration where
  seq : ℕ → ℝ → ℝ≥0∞
  seq_def : seq = fatouIllustrationSeq
  integral_eq_one : ∀ n, ∫⁻ x, seq n x ∂volume = 1
  eventually_zero_off_zero : ∀ ⦃x : ℝ⦄, x ≠ 0 → ∀ᶠ n in atTop, seq n x = 0
  at_zero_eq : ∀ n, seq n 0 = ((n + 1 : ℕ) : ℝ≥0∞)
  limitProfile : ℝ → ℝ≥0∞
  limitProfile_def : limitProfile = fatouIllustrationLimit
  limitProfile_eq_if : ∀ x, limitProfile x = if x = 0 then (∞ : ℝ≥0∞) else 0
  limitProfile_integral_zero : ∫⁻ x, limitProfile x ∂volume = 0

theorem fatouIllustrationSeq_integral_eq_one (n : ℕ) :
    ∫⁻ x, fatouIllustrationSeq n x ∂volume = 1 := by
  simp only [fatouIllustrationSeq, lintegral_indicator measurableSet_Icc]
  rw [MeasureTheory.setLIntegral_const]
  have hpos : (0 : ℝ) < n + 1 := by positivity
  have hsucc_ne : (((n + 1 : ℕ) : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have h_inv :
      ENNReal.ofReal (1 / (n + 1 : ℝ)) = (((n + 1 : ℕ) : ℝ≥0∞))⁻¹ := by
    have h_inv0 := ENNReal.ofReal_inv_of_pos hpos
    have h_nat : ENNReal.ofReal (n + 1 : ℝ) = (((n + 1 : ℕ) : ℝ≥0∞)) := by
      simpa using ENNReal.ofReal_natCast (n + 1)
    rw [h_nat] at h_inv0
    simpa [one_div] using h_inv0
  rw [Real.volume_Icc, sub_zero, h_inv]
  simpa using ENNReal.mul_inv_cancel hsucc_ne

theorem fatouIllustrationSeq_eventually_zero_off_zero {x : ℝ} (hx : x ≠ 0) :
    ∀ᶠ n in atTop, fatouIllustrationSeq n x = 0 := by
  by_cases hxneg : x < 0
  · filter_upwards [Filter.Eventually.of_forall fun n => True.intro] with n _
    have hxnot : x ∉ Set.Icc (0 : ℝ) (1 / (n + 1 : ℝ)) := by
      intro hmem
      exact not_lt_of_ge hmem.1 hxneg
    rw [fatouIllustrationSeq, Set.indicator_of_notMem hxnot]
  · have hxpos : 0 < x := lt_of_le_of_ne (le_of_not_gt hxneg) hx.symm
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hxpos
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hle : (1 / (n + 1 : ℝ)) ≤ 1 / (N + 1 : ℝ) := by
      have hsucc : (N + 1 : ℝ) ≤ (n + 1 : ℝ) := by
        exact_mod_cast Nat.succ_le_succ hn
      have hNpos : (0 : ℝ) < N + 1 := by positivity
      exact one_div_le_one_div_of_le hNpos hsucc
    have hxnot : x ∉ Set.Icc (0 : ℝ) (1 / (n + 1 : ℝ)) := by
      intro hmem
      exact not_lt_of_ge hmem.2 (lt_of_le_of_lt hle hN)
    rw [fatouIllustrationSeq, Set.indicator_of_notMem hxnot]

theorem fatouIllustrationSeq_at_zero (n : ℕ) :
    fatouIllustrationSeq n 0 = ((n + 1 : ℕ) : ℝ≥0∞) := by
  have hmem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / (n + 1 : ℝ)) := by
    constructor <;> positivity
  rw [fatouIllustrationSeq, Set.indicator_of_mem hmem]

theorem fatouIllustrationLimit_eq_if (x : ℝ) :
    fatouIllustrationLimit x = if x = 0 then (∞ : ℝ≥0∞) else 0 := by
  by_cases hx : x = 0 <;> simp [fatouIllustrationLimit, hx]

theorem fatouIllustrationLimit_integral_zero :
    ∫⁻ x, fatouIllustrationLimit x ∂volume = 0 := by
  change ∫⁻ x, ({(0 : ℝ)} : Set ℝ).indicator (fun _ => (∞ : ℝ≥0∞)) x ∂volume = 0
  rw [lintegral_indicator (measurableSet_singleton (0 : ℝ))]
  rw [MeasureTheory.setLIntegral_const]
  simp

/-- Exported declaration for Example 7.2.1. -/
noncomputable def ex_7_2_1 : FatouLemmaIllustration where
  seq := fatouIllustrationSeq
  seq_def := rfl
  integral_eq_one := fatouIllustrationSeq_integral_eq_one
  eventually_zero_off_zero := fun {x} hx =>
    fatouIllustrationSeq_eventually_zero_off_zero (x := x) hx
  at_zero_eq := fatouIllustrationSeq_at_zero
  limitProfile := fatouIllustrationLimit
  limitProfile_def := rfl
  limitProfile_eq_if := fatouIllustrationLimit_eq_if
  limitProfile_integral_zero := fatouIllustrationLimit_integral_zero
