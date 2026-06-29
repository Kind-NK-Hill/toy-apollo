import Mathlib

/-
TASK ID: prob_5_9
TYPE: Problem
SOURCE PLAN: 18_chap5_problems
TASK CONTENT:
\item Let $(\Omega, \mathcal{F}, P)$ denote a probability space and let $\mathcal{G}$ and $\mathcal{H}$ be two independent sub-$\sigma$-algebras of $\mathcal{F}$. Prove that any random variable $X$ that is measurable with respect to both $\mathcal{G}$ and $\mathcal{H}$ is a constant with probability 1, i.e., there exists a constant $c$ such that $P(X=c)=1$.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory

/-- If an event is measurable with respect to two independent sub-sigma-algebras,
then it has probability zero or one. -/
lemma prob_5_9_event_zero_or_one {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (G H : MeasurableSpace Ω) (h_indep : Indep G H P) (A : Set Ω)
    (hAG : @MeasurableSet Ω G A) (hAH : @MeasurableSet Ω H A) :
    P A = 0 ∨ P A = 1 := by
  exact measure_eq_zero_or_one_of_indepSet_self
    (h_indep.indepSet_of_measurableSet hAG hAH)

/-- Problem 5.9: a real random variable measurable with respect to two
independent sub-sigma-algebras is almost surely constant. -/
theorem prob_5_9 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (G H : MeasurableSpace Ω) (hG_le : G ≤ mΩ) (_hH_le : H ≤ mΩ)
    (h_indep : Indep G H P) (X : Ω → ℝ)
    (hX_G : @Measurable Ω ℝ G _ X) (hX_H : @Measurable Ω ℝ H _ X) :
    ∃ c : ℝ, P {ω | X ω = c} = 1 := by
  have h_zero_one :
      ∀ U : Set ℝ, MeasurableSet U → P (X ⁻¹' U) = 0 ∨ P (X ⁻¹' U) = 1 := by
    intro U hU
    exact @prob_5_9_event_zero_or_one Ω mΩ P _ G H h_indep
      (X ⁻¹' U) (hX_G hU) (hX_H hU)
  have h_decides :
      ∀ U : Set ℝ, MeasurableSet U →
        (∀ᵐ ω ∂P, X ω ∈ U) ∨ (∀ᵐ ω ∂P, X ω ∉ U) := by
    intro U hU
    have h_preimage_mΩ : @MeasurableSet Ω mΩ (X ⁻¹' U) := hG_le _ (hX_G hU)
    rcases h_zero_one U hU with h0 | h1
    · right
      have h_compl : (X ⁻¹' U)ᶜ ∈ ae P := compl_mem_ae_iff.mpr h0
      simpa [Set.preimage_compl] using h_compl
    · left
      exact (mem_ae_iff_prob_eq_one (μ := P) h_preimage_mΩ).mpr h1
  obtain ⟨c, hc⟩ :=
    Filter.exists_eventuallyEq_const_of_forall_separating
      (l := ae P) (f := X) (p := (MeasurableSet : Set ℝ → Prop)) h_decides
  refine ⟨c, ?_⟩
  have h_eq_ae : ∀ᵐ ω ∂P, X ω = c := by
    simpa [Filter.EventuallyEq, Function.const] using hc
  have h_eq_meas : @MeasurableSet Ω mΩ {ω | X ω = c} := by
    have h_preimage_singleton : @MeasurableSet Ω mΩ (X ⁻¹' ({c} : Set ℝ)) :=
      hG_le _ (hX_G (measurableSet_singleton c))
    simpa [Set.preimage, Set.mem_singleton_iff] using h_preimage_singleton
  have h_eq_mem : {ω | X ω = c} ∈ ae P := by
    simpa [Filter.Eventually] using h_eq_ae
  exact (mem_ae_iff_prob_eq_one (μ := P) h_eq_meas).mp h_eq_mem
