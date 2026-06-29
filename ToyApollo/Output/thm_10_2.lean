import Mathlib
import ToyApollo.Output.thm_10_1
import ToyApollo.Output.def_10_2

/-
TASK ID: thm_10_2
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter10-almost-sure-probability
TASK CONTENT:
\begin{thmbox}{10.2}
If $X_n\xrightarrow{\mathrm{a.s.}}X$, then $X_n\xrightarrow{P}X$.
\end{thmbox}

\textit{Proof}
Assume $(X_n)_{n\geq 1}$ converges to $X$ almost surely. By (10.1), we obtain, for all $\epsilon>0$,
\[
0=\lim_{n\to\infty}P\left(\bigcup_{m=n}^{\infty}\{\lvert X_m-X\rvert>\epsilon\}\right)
\geq
\lim_{n\to\infty}P(\{\lvert X_n-X\rvert>\epsilon\}).
\]
We have inequality in the last step because the event becomes a smaller set. Thus,
\[
\lim_{n\to\infty}P(\{\lvert X_n-X\rvert>\epsilon\})=0.
\]
Because it holds for any $\epsilon>0$, we have convergence in probability.
\hfill $\square$
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set

/-- The source tail-union estimate in Theorem 10.2: the events
`{|Xₙ - X| > ε}` are contained in the tail unions whose intersection is the
Theorem 10.1 infinitely-often event, so continuity from above gives the
probability limit. -/
private theorem convergesInProbability_of_tail_null {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXn : ∀ n : ℕ, AEStronglyMeasurable (Xn n) μ)
    (hAS : ConvergesAlmostSurely μ Xn X) :
    ConvergesInProbability μ Xn X := by
  intro ε hε
  let A : ℕ → Set Ω := fun n => deviationEvent Xn X n ε
  let B : ℕ → Set Ω := fun n => {ω : Ω | ∃ m : ℕ, n ≤ m ∧ ω ∈ A m}
  have htail_null : μ (deviationInfinitelyOften Xn X ε) = 0 :=
    (thm_10_1 μ Xn X).1 hAS ε hε
  have hX : AEStronglyMeasurable X μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hXn hAS
  have hA_null : ∀ n, NullMeasurableSet (A n) μ := by
    intro n
    have hdiff : AEStronglyMeasurable (fun ω => Xn n ω - X ω) μ := (hXn n).sub hX
    have habs : AEStronglyMeasurable (fun ω => |Xn n ω - X ω|) μ := by
      simpa [Real.norm_eq_abs] using hdiff.norm
    simpa [A, deviationEvent] using
      (AEStronglyMeasurable.nullMeasurableSet_lt
        (stronglyMeasurable_const.aestronglyMeasurable :
          AEStronglyMeasurable (fun _ : Ω => ε) μ)
        habs)
  have hB_null : ∀ n, NullMeasurableSet (B n) μ := by
    intro n
    have hB_eq : B n = ⋃ m : ℕ, if n ≤ m then A m else ∅ := by
      ext ω
      simp [B]
    rw [hB_eq]
    exact NullMeasurableSet.iUnion fun m => by
      by_cases hnm : n ≤ m
      · simpa [hnm] using hA_null m
      · simp [hnm]
  have hB_anti : Antitone B := by
    intro n k hnk ω hω
    rcases hω with ⟨m, hm, hAm⟩
    exact ⟨m, le_trans hnk hm, hAm⟩
  have hInter_eq : {ω : Ω | ∀ n : ℕ, ω ∈ B n} = deviationInfinitelyOften Xn X ε := by
    ext ω
    constructor
    · intro h
      rw [deviationInfinitelyOften, mem_limsup_iff_frequently_mem]
      rw [frequently_atTop]
      intro n
      have hn : ω ∈ B n := by exact h n
      rcases hn with ⟨m, hnm, hAm⟩
      exact ⟨m, hnm, by simpa [A] using hAm⟩
    · intro h
      rw [deviationInfinitelyOften, mem_limsup_iff_frequently_mem] at h
      rw [frequently_atTop] at h
      intro n
      rcases h n with ⟨m, hnm, hAm⟩
      exact ⟨m, hnm, by simpa [A] using hAm⟩
  have hB_tendsto :
      Tendsto (fun n : ℕ => μ (B n)) atTop (nhds 0) := by
    have hcont :=
      tendsto_measure_iInter_atTop (μ := μ) (s := B) hB_null hB_anti
        ⟨0, measure_ne_top μ (B 0)⟩
    have hSetEq : (⋂ n : ℕ, B n) = deviationInfinitelyOften Xn X ε := by
      rw [← hInter_eq]
      ext ω
      simp only [mem_iInter, mem_setOf_eq]
    simpa [hSetEq, htail_null] using hcont
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB_tendsto
    (fun n => zero_le _) ?_
  intro n
  exact measure_mono (by
    intro ω hω
    exact ⟨n, le_rfl, hω⟩)

/-- Theorem 10.2: almost sure convergence implies convergence in probability. -/
theorem thm_10_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXn : ∀ n : ℕ, AEStronglyMeasurable (Xn n) μ)
    (hAS : ConvergesAlmostSurely μ Xn X) :
    ConvergesInProbability μ Xn X := by
  exact convergesInProbability_of_tail_null μ Xn X hXn hAS
