import Mathlib
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import ToyApollo.Output.thm_11_6

/-
TASK ID: prob_11_3
TYPE: Problem
SOURCE PLAN: chapter11-problems
TASK CONTENT:
\textbf{11.3.} Let X1,X 2,...,X n be iid. random variables uniformly distributed between

0 and 1. Show that the sequence of random variables

Yn \coloneqq X1 + X2 +\cdot\cdot\cdot+ Xn

X2

1 + X2

2 +\cdot\cdot\cdot+ X2n

converges to a constant in probability as n \to\infty .
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

/-- The uniform probability law on `[0,1]`, represented as Lebesgue measure
restricted to the closed unit interval. -/
noncomputable def prob_11_3_uniform01Measure : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

theorem prob_11_3_uniform01_integrable_id :
    Integrable (fun x : ℝ => x) prob_11_3_uniform01Measure := by
  rw [prob_11_3_uniform01Measure]
  exact ContinuousOn.integrableOn_compact isCompact_Icc continuousOn_id

theorem prob_11_3_uniform01_integral_id :
    ∫ x : ℝ, x ∂prob_11_3_uniform01Measure = (1 / 2 : ℝ) := by
  rw [prob_11_3_uniform01Measure]
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [integral_id]
  norm_num

theorem prob_11_3_uniform01_integrable_sq :
    Integrable (fun x : ℝ => x ^ 2) prob_11_3_uniform01Measure := by
  rw [prob_11_3_uniform01Measure]
  exact ContinuousOn.integrableOn_compact isCompact_Icc (continuousOn_id.pow 2)

theorem prob_11_3_uniform01_integral_sq :
    ∫ x : ℝ, x ^ 2 ∂prob_11_3_uniform01Measure = (1 / 3 : ℝ) := by
  rw [prob_11_3_uniform01Measure]
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [integral_pow]
  norm_num

/-- The squared sample sequence appearing in the denominator of Problem 11.3. -/
def prob_11_3_squareSeq {Ω : Type*} (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun i ω => (X i ω) ^ 2

/-- The random ratio in Problem 11.3, written as the ratio of the two sample
means.  This is algebraically the same as the displayed ratio of sums, because
the common factor `n + 1` cancels. -/
noncomputable def prob_11_3_Yn {Ω : Type*} (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n ω =>
    thm_11_5_sampleMean X n ω /
      thm_11_5_sampleMean (prob_11_3_squareSeq X) n ω

/-- The two weak-law conclusions needed for the numerator and denominator in
Problem 11.3. -/
def prob_11_3_WLLNInputs {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ConvergesInProbability P (fun n => thm_11_5_sampleMean X n) (fun _ => (1 / 2 : ℝ)) ∧
    ConvergesInProbability P
      (fun n => thm_11_5_sampleMean (prob_11_3_squareSeq X) n)
      (fun _ => (1 / 3 : ℝ))

theorem prob_11_3_identDistrib_of_uniform01_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (hLaw : ∀ i, HasLaw (X i) prob_11_3_uniform01Measure P) :
    ∀ i, IdentDistrib (X i) (X 0) P P := by
  intro i
  exact {
    aemeasurable_fst := (hLaw i).aemeasurable
    aemeasurable_snd := (hLaw 0).aemeasurable
    map_eq := by rw [(hLaw i).map_eq, (hLaw 0).map_eq] }

theorem prob_11_3_integrable_of_uniform01_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (hLaw : ∀ i, HasLaw (X i) prob_11_3_uniform01Measure P) (i : ℕ) :
    Integrable (X i) P := by
  have hmap : Integrable (fun x : ℝ => x) (Measure.map (X i) P) := by
    rw [(hLaw i).map_eq]
    exact prob_11_3_uniform01_integrable_id
  simpa [Function.comp_def] using
    ((integrable_map_measure aestronglyMeasurable_id (hLaw i).aemeasurable).1 hmap)

theorem prob_11_3_mean_of_uniform01_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (hLaw : ∀ i, HasLaw (X i) prob_11_3_uniform01Measure P) (i : ℕ) :
    P[X i] = (1 / 2 : ℝ) := by
  calc
    P[X i] = ∫ x : ℝ, x ∂prob_11_3_uniform01Measure := by
      simpa using (hLaw i).integral_eq
    _ = (1 / 2 : ℝ) := prob_11_3_uniform01_integral_id

theorem prob_11_3_square_integrable_of_uniform01_law {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (hLaw : ∀ i, HasLaw (X i) prob_11_3_uniform01Measure P) (i : ℕ) :
    Integrable ((prob_11_3_squareSeq X) i) P := by
  have hmap : Integrable (fun x : ℝ => x ^ 2) (Measure.map (X i) P) := by
    rw [(hLaw i).map_eq]
    exact prob_11_3_uniform01_integrable_sq
  simpa [prob_11_3_squareSeq, Function.comp_def] using
    ((integrable_map_measure
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ 2) (Measure.map (X i) P))
      (hLaw i).aemeasurable).1 hmap)

theorem prob_11_3_square_mean_of_uniform01_law {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (hLaw : ∀ i, HasLaw (X i) prob_11_3_uniform01Measure P) (i : ℕ) :
    P[(prob_11_3_squareSeq X) i] = (1 / 3 : ℝ) := by
  have hcomp :=
    (hLaw i).integral_comp
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ 2) prob_11_3_uniform01Measure)
  calc
    P[(prob_11_3_squareSeq X) i] =
        ∫ x : ℝ, x ^ 2 ∂prob_11_3_uniform01Measure := by
      simpa [prob_11_3_squareSeq, Function.comp_def] using hcomp
    _ = (1 / 3 : ℝ) := prob_11_3_uniform01_integral_sq

theorem prob_11_3_squareSeq_independent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (hInd : def_5_10_randomVariables P X) :
    def_5_10_randomVariables P (prob_11_3_squareSeq X) := by
  have h : iIndepFun X P := by
    simpa [def_5_10_randomVariables] using hInd
  simpa [def_5_10_randomVariables, prob_11_3_squareSeq, Function.comp_def] using
    (h.comp (fun _ => fun x : ℝ => x ^ 2) (fun _ => by fun_prop))

theorem prob_11_3_squareSeq_identDistrib {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ i, IdentDistrib
      ((prob_11_3_squareSeq X) i) ((prob_11_3_squareSeq X) 0) P P := by
  intro i
  simpa [prob_11_3_squareSeq, Function.comp_def] using
    (hIdent i).comp (by fun_prop : Measurable (fun x : ℝ => x ^ 2))

theorem prob_11_3_sampleMean_aestronglyMeasurable {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (hInt : ∀ i, Integrable (X i) P) :
    ∀ n, AEStronglyMeasurable (thm_11_5_sampleMean X n) P := by
  intro n
  change AEStronglyMeasurable
    (fun ω => (1 / ((n : ℝ) + 1)) * (∑ i : Fin (n + 1), X i.1 ω)) P
  simpa using
    (AEStronglyMeasurable.const_mul
      (Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin (n + 1)))
        (fun i _hi => (hInt i.1).aestronglyMeasurable))
      (1 / ((n : ℝ) + 1)))

/-- Khinchin's weak law supplies the numerator and squared-denominator limits
from the source iid Uniform `[0,1]` assumptions. -/
theorem prob_11_3_wlln_inputs_of_uniform01 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hIndX : def_5_10_randomVariables P X)
    (hLaw : ∀ i, HasLaw (X i) prob_11_3_uniform01Measure P) :
    prob_11_3_WLLNInputs P X := by
  have hIdentX : ∀ i, IdentDistrib (X i) (X 0) P P :=
    prob_11_3_identDistrib_of_uniform01_law P X hLaw
  have hIntX0 : Integrable (X 0) P :=
    prob_11_3_integrable_of_uniform01_law P X hLaw 0
  have hMeanX0 : P[X 0] = (1 / 2 : ℝ) :=
    prob_11_3_mean_of_uniform01_law P X hLaw 0
  have hIndSq : def_5_10_randomVariables P (prob_11_3_squareSeq X) :=
    prob_11_3_squareSeq_independent P X hIndX
  have hIdentSq : ∀ i, IdentDistrib
      ((prob_11_3_squareSeq X) i) ((prob_11_3_squareSeq X) 0) P P :=
    prob_11_3_squareSeq_identDistrib P X hIdentX
  have hIntSq0 : Integrable ((prob_11_3_squareSeq X) 0) P :=
    prob_11_3_square_integrable_of_uniform01_law P X hLaw 0
  have hMeanSq0 : P[(prob_11_3_squareSeq X) 0] = (1 / 3 : ℝ) :=
    prob_11_3_square_mean_of_uniform01_law P X hLaw 0
  exact ⟨
    thm_11_6 P X (1 / 2) hIntX0 hIndX hIdentX hMeanX0,
    thm_11_6 P (prob_11_3_squareSeq X) (1 / 3)
      hIntSq0 hIndSq hIdentSq hMeanSq0⟩

/-- Auxiliary form of Problem 11.3 once Khinchin's weak-law inputs have been
established for the numerator and squared denominator. -/
theorem prob_11_3_of_wlln_inputs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hInputs : prob_11_3_WLLNInputs P X) :
    ConvergesInProbability P (prob_11_3_Yn X) (fun _ => (3 / 2 : ℝ)) := by
  rcases hInputs with ⟨hNum, hDen⟩
  intro ε hε
  let δ : ℝ := min (1 / 6) (ε / 30)
  have hδ_pos : 0 < δ := by
    exact lt_min (by norm_num) (div_pos hε (by norm_num))
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
  have hδ_le_six : δ ≤ 1 / 6 := min_le_left _ _
  have hδ_le_eps : δ ≤ ε / 30 := min_le_right _ _
  let numDev : ℕ → Set Ω :=
    fun n => deviationEvent
      (fun n => thm_11_5_sampleMean X n) (fun _ => (1 / 2 : ℝ)) n δ
  let denDev : ℕ → Set Ω :=
    fun n => deviationEvent
      (fun n => thm_11_5_sampleMean (prob_11_3_squareSeq X) n)
      (fun _ => (1 / 3 : ℝ)) n δ
  have hBad_subset :
      ∀ n,
        deviationEvent (prob_11_3_Yn X) (fun _ : Ω => (3 / 2 : ℝ)) n ε
          ⊆ numDev n ∪ denDev n := by
    intro n ω hω
    by_contra hnot
    have hnum_not : ω ∉ numDev n := by
      intro hmem
      exact hnot (Or.inl hmem)
    have hden_not : ω ∉ denDev n := by
      intro hmem
      exact hnot (Or.inr hmem)
    have hA :
        |thm_11_5_sampleMean X n ω - (1 / 2 : ℝ)| ≤ δ := by
      exact le_of_not_gt hnum_not
    have hB :
        |thm_11_5_sampleMean (prob_11_3_squareSeq X) n ω - (1 / 3 : ℝ)| ≤ δ := by
      exact le_of_not_gt hden_not
    let A : ℝ := thm_11_5_sampleMean X n ω
    let B : ℝ := thm_11_5_sampleMean (prob_11_3_squareSeq X) n ω
    have hA' : |A - (1 / 2 : ℝ)| ≤ δ := by simpa [A] using hA
    have hB' : |B - (1 / 3 : ℝ)| ≤ δ := by simpa [B] using hB
    have hB_low : (1 / 6 : ℝ) ≤ B := by
      have hleft : (1 / 3 : ℝ) - B ≤ δ := (abs_sub_le_iff.mp hB').2
      nlinarith
    have hB_pos : 0 < B := by nlinarith
    have hA_le : A - (1 / 2 : ℝ) ≤ δ := (abs_sub_le_iff.mp hA').1
    have hA_ge : (1 / 2 : ℝ) - A ≤ δ := (abs_sub_le_iff.mp hA').2
    have hB_le : B - (1 / 3 : ℝ) ≤ δ := (abs_sub_le_iff.mp hB').1
    have hB_ge : (1 / 3 : ℝ) - B ≤ δ := (abs_sub_le_iff.mp hB').2
    have hnum_bound :
        |(A - (1 / 2 : ℝ)) - (3 / 2 : ℝ) * (B - (1 / 3 : ℝ))|
          ≤ δ + (3 / 2 : ℝ) * δ := by
      rw [abs_sub_le_iff]
      constructor <;> nlinarith
    have hrepr :
        A / B - (3 / 2 : ℝ) =
          ((A - (1 / 2 : ℝ)) - (3 / 2 : ℝ) * (B - (1 / 3 : ℝ))) / B := by
      field_simp [hB_pos.ne']
      ring
    have hratio_bound :
        |A / B - (3 / 2 : ℝ)| ≤ 15 * δ := by
      rw [hrepr, abs_div, abs_of_pos hB_pos, div_le_iff₀ hB_pos]
      nlinarith
    have hratio_le_eps : |A / B - (3 / 2 : ℝ)| ≤ ε := by
      nlinarith
    have hnot_bad :
        ¬ |prob_11_3_Yn X n ω - (3 / 2 : ℝ)| > ε := by
      simpa [prob_11_3_Yn, A, B] using not_lt.mpr hratio_le_eps
    exact hnot_bad hω
  have hMeasure_le :
      ∀ n,
        P (deviationEvent (prob_11_3_Yn X) (fun _ : Ω => (3 / 2 : ℝ)) n ε)
          ≤ P (numDev n) + P (denDev n) := by
    intro n
    exact (measure_mono (hBad_subset n)).trans
      (MeasureTheory.measure_union_le (numDev n) (denDev n))
  have hUpper :
      Filter.Tendsto (fun n => P (numDev n) + P (denDev n)) Filter.atTop (nhds 0) := by
    have hsum :=
      (hNum δ hδ_pos).add (hDen δ hδ_pos)
    simpa [numDev, denDev] using hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa using (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) Filter.atTop (nhds 0)))
    hUpper
    (fun n => zero_le _)
    hMeasure_le

/-- Problem 11.3: iid Uniform `[0,1]` variables have ratio of sample sums
converging in probability to `(1/2)/(1/3) = 3/2`. -/
theorem prob_11_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hIndX : def_5_10_randomVariables P X)
    (hLaw : ∀ i, HasLaw (X i) prob_11_3_uniform01Measure P) :
    ConvergesInProbability P (prob_11_3_Yn X) (fun _ => (3 / 2 : ℝ)) := by
  have hInputs : prob_11_3_WLLNInputs P X :=
    prob_11_3_wlln_inputs_of_uniform01 P X hIndX hLaw
  exact prob_11_3_of_wlln_inputs P X hInputs
