import Mathlib
import ToyApollo.Output.def_10_1
import ToyApollo.Output.thm_10_1

/-
TASK ID: prob_10_1
TYPE: Problem
SOURCE PLAN: chapter10-problems
TASK CONTENT:
\textbf{10.1.} Prove that a sequence of random variables $(X_k)_{k\geq 1}$ converges to $X$ a.s. if and only if for each $\epsilon>0$,
\[
\lim_{n\to\infty}P(\lvert X_k-X\rvert\leq \epsilon\text{ for all }k\geq n)=1.
\]
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory

/-- The event in Problem 10.1: after index `n`, all deviations stay within
`ε`. -/
def tailCloseEvent {Ω : Type*} (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (n : ℕ) (ε : ℝ) : Set Ω :=
  {ω : Ω | ∀ k : ℕ, n ≤ k → |Xn k ω - X ω| ≤ ε}

/-- The deviation event from Theorem 10.1 is measurable for random variables. -/
theorem almostSureDeviationEvent_measurable {Ω : Type*} [MeasurableSpace Ω]
    {Xn : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (hXn : ∀ n : ℕ, Measurable (Xn n)) (hX : Measurable X)
    (n : ℕ) (ε : ℝ) :
    MeasurableSet (almostSureDeviationEvent Xn X n ε) := by
  exact measurableSet_Ioi.preimage (((hXn n).sub hX).abs)

/-- The infinitely-often deviation event is measurable. -/
theorem deviationInfinitelyOften_measurable {Ω : Type*} [MeasurableSpace Ω]
    {Xn : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (hXn : ∀ n : ℕ, Measurable (Xn n)) (hX : Measurable X)
    (ε : ℝ) :
    MeasurableSet (deviationInfinitelyOften Xn X ε) := by
  exact MeasurableSet.measurableSet_limsup fun n =>
    almostSureDeviationEvent_measurable hXn hX n ε

/-- The tail-close events increase with the starting index. -/
theorem tailCloseEvent_mono {Ω : Type*} (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (ε : ℝ) :
    Monotone fun n : ℕ => tailCloseEvent Xn X n ε := by
  intro n m hnm ω hω k hmk
  exact hω k (le_trans hnm hmk)

/-- The union of eventual `ε`-close tail events is the complement of the
event that the `ε`-deviation occurs infinitely often. -/
theorem iUnion_tailCloseEvent_eq_compl_deviationInfinitelyOften {Ω : Type*}
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (ε : ℝ) :
    (⋃ n : ℕ, tailCloseEvent Xn X n ε) =
      (deviationInfinitelyOften Xn X ε)ᶜ := by
  ext ω
  rw [Set.mem_iUnion, Set.mem_compl_iff, deviationInfinitelyOften,
    mem_limsup_iff_frequently_mem, frequently_atTop]
  constructor
  · intro htail hfreq
    rcases htail with ⟨n, hn⟩
    rcases hfreq n with ⟨k, hkn, hkdev⟩
    have hle : |Xn k ω - X ω| ≤ ε := hn k hkn
    exact not_lt_of_ge hle hkdev
  · intro hnot
    classical
    by_contra hno
    have hfreq :
        ∀ n : ℕ, ∃ k ≥ n, ω ∈ almostSureDeviationEvent Xn X k ε := by
      intro n
      by_contra hn
      apply hno
      refine ⟨n, ?_⟩
      intro k hkn
      have hknot : ¬ ω ∈ almostSureDeviationEvent Xn X k ε := by
        intro hk
        exact hn ⟨k, hkn, hk⟩
      exact not_lt.mp (by simpa [almostSureDeviationEvent] using hknot)
    exact hnot hfreq

/-- Continuity from below for the increasing tail-close events. -/
theorem tendsto_measure_tailCloseEvent {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (ε : ℝ) :
    Tendsto (fun n : ℕ => μ (tailCloseEvent Xn X n ε)) atTop
      (nhds (μ ((deviationInfinitelyOften Xn X ε)ᶜ))) := by
  have hmono := tailCloseEvent_mono Xn X ε
  have hlim := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [iUnion_tailCloseEvent_eq_compl_deviationInfinitelyOften Xn X ε] at hlim
  exact hlim

/-- The Theorem 10.1 null infinitely-often condition is equivalent to the
Problem 10.1 tail-close probability limit. -/
theorem deviationInfinitelyOften_zero_iff_tendsto_tailClose {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXn : ∀ n : ℕ, Measurable (Xn n)) (hX : Measurable X)
    (ε : ℝ) :
    μ (deviationInfinitelyOften Xn X ε) = 0 ↔
      Tendsto (fun n : ℕ => μ (tailCloseEvent Xn X n ε)) atTop
        (nhds (1 : ENNReal)) := by
  have hDmeas := deviationInfinitelyOften_measurable hXn hX ε
  constructor
  · intro hzero
    have hcompl : μ ((deviationInfinitelyOften Xn X ε)ᶜ) = 1 :=
      (prob_compl_eq_one_iff (μ := μ) hDmeas).2 hzero
    simpa [hcompl] using tendsto_measure_tailCloseEvent μ Xn X ε
  · intro htail
    have hlim := tendsto_measure_tailCloseEvent μ Xn X ε
    have hcompl : μ ((deviationInfinitelyOften Xn X ε)ᶜ) = 1 :=
      tendsto_nhds_unique hlim htail
    exact (prob_compl_eq_one_iff (μ := μ) hDmeas).1 hcompl

/-- Problem 10.1: almost-sure convergence is equivalent to the probabilities
of the eventual `ε`-close tail events tending to one. -/
theorem prob_10_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXn : ∀ n : ℕ, Measurable (Xn n)) (hX : Measurable X) :
    ConvergesAlmostSurely μ Xn X ↔
        ∀ ε : ℝ, 0 < ε →
          Tendsto (fun n : ℕ => μ (tailCloseEvent Xn X n ε)) atTop
            (nhds (1 : ENNReal)) := by
  rw [thm_10_1 μ Xn X]
  constructor
  · intro hio ε hε
    exact (deviationInfinitelyOften_zero_iff_tendsto_tailClose μ Xn X hXn hX ε).1
      (hio ε hε)
  · intro htail ε hε
    exact (deviationInfinitelyOften_zero_iff_tendsto_tailClose μ Xn X hXn hX ε).2
      (htail ε hε)
