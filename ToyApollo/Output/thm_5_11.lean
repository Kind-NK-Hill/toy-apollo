/-
TASK ID: thm_5_11
TYPE: Theorem_with_Proof
SOURCE PLAN: 17_chap5_model_kolmogorov
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open Filter

@[reducible] def coordinateSigmaAlgebra {Ω β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β]
    (X : ℕ → Ω → β) (n : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (X n) ‹MeasurableSpace β›

@[reducible] def prefixSigmaAlgebra {Ω β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β]
    (X : ℕ → Ω → β) (n : ℕ) : MeasurableSpace Ω :=
  ⨆ i ∈ Set.Iic n, coordinateSigmaAlgebra X i

@[reducible] def futureSigmaAlgebra {Ω β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β]
    (X : ℕ → Ω → β) (n : ℕ) : MeasurableSpace Ω :=
  ⨆ i ∈ Set.Ioi n, coordinateSigmaAlgebra X i

@[reducible] def fullCoordinateSigmaAlgebra {Ω β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β]
    (X : ℕ → Ω → β) : MeasurableSpace Ω :=
  ⨆ i, coordinateSigmaAlgebra X i

@[reducible] def tailSigmaAlgebra {Ω β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β]
    (X : ℕ → Ω → β) : MeasurableSpace Ω :=
  limsup (fun n => MeasurableSpace.comap (X n) ‹MeasurableSpace β›) atTop

theorem thm_5_11_prefix_indep_future
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : MeasureTheory.Measure Ω) (X : ℕ → Ω → β)
    (h_meas : ∀ n, Measurable (X n))
    (h_indep : ProbabilityTheory.iIndepFun X P) (n : ℕ) :
    ProbabilityTheory.Indep (prefixSigmaAlgebra X n) (futureSigmaAlgebra X n) P := by
  simpa [prefixSigmaAlgebra, futureSigmaAlgebra, coordinateSigmaAlgebra] using
    (ProbabilityTheory.indep_iSup_of_disjoint (μ := P)
      (fun i => (h_meas i).comap_le) h_indep.iIndep (Set.Iic_disjoint_Ioi le_rfl))

theorem thm_5_11_tail_le_future
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (X : ℕ → Ω → β) (n : ℕ) :
    tailSigmaAlgebra X ≤ futureSigmaAlgebra X n := by
  unfold tailSigmaAlgebra futureSigmaAlgebra coordinateSigmaAlgebra
  rw [limsup_eq_iInf_iSup_of_nat]
  refine (iInf_le _ (n + 1)).trans ?_
  refine iSup_le fun i => iSup_le fun hi => ?_
  exact le_iSup_of_le i <| le_iSup_of_le
    (show i ∈ Set.Ioi n by exact Nat.lt_of_succ_le hi) le_rfl

theorem thm_5_11_prefix_indep_tail
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : MeasureTheory.Measure Ω) (X : ℕ → Ω → β)
    (h_meas : ∀ n, Measurable (X n))
    (h_indep : ProbabilityTheory.iIndepFun X P) (n : ℕ) :
    ProbabilityTheory.Indep (prefixSigmaAlgebra X n) (tailSigmaAlgebra X) P :=
  ProbabilityTheory.indep_of_indep_of_le_right
    (thm_5_11_prefix_indep_future P X h_meas h_indep n)
    (thm_5_11_tail_le_future X n)

theorem thm_5_11_prefix_mono
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (X : ℕ → Ω → β) : Monotone (prefixSigmaAlgebra X) := by
  intro n m hnm
  refine iSup_le fun i => iSup_le fun hi => ?_
  exact le_iSup_of_le i <| le_iSup_of_le (show i ∈ Set.Iic m by exact hi.trans hnm) le_rfl

theorem thm_5_11_iSup_prefix_eq_full
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (X : ℕ → Ω → β) :
    (⨆ n, prefixSigmaAlgebra X n) = fullCoordinateSigmaAlgebra X := by
  apply le_antisymm
  · refine iSup_le fun n => ?_
    refine iSup_le fun i => iSup_le fun _ => ?_
    exact le_iSup (fun j => coordinateSigmaAlgebra X j) i
  · refine iSup_le fun i => ?_
    calc
      coordinateSigmaAlgebra X i ≤ prefixSigmaAlgebra X i :=
        le_iSup_of_le i <| le_iSup_of_le
          (show i ∈ Set.Iic i by exact (le_rfl : i ≤ i)) le_rfl
      _ ≤ ⨆ n, prefixSigmaAlgebra X n := le_iSup (prefixSigmaAlgebra X) i

theorem thm_5_11_tail_le_full
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (X : ℕ → Ω → β) :
    tailSigmaAlgebra X ≤ fullCoordinateSigmaAlgebra X := by
  unfold tailSigmaAlgebra fullCoordinateSigmaAlgebra coordinateSigmaAlgebra
  exact limsup_le_iSup

theorem thm_5_11_full_indep_tail
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (X : ℕ → Ω → β) (h_meas : ∀ n, Measurable (X n))
    (h_indep : ProbabilityTheory.iIndepFun X P) :
    ProbabilityTheory.Indep (fullCoordinateSigmaAlgebra X) (tailSigmaAlgebra X) P := by
  have hprefix : ∀ n, ProbabilityTheory.Indep
      (prefixSigmaAlgebra X n) (tailSigmaAlgebra X) P :=
    fun n => thm_5_11_prefix_indep_tail P X h_meas h_indep n
  have hprefix_le : ∀ n, prefixSigmaAlgebra X n ≤ ‹MeasurableSpace Ω› := by
    intro n
    refine iSup_le fun i => iSup_le fun _ => ?_
    exact (h_meas i).comap_le
  have htail_le : tailSigmaAlgebra X ≤ ‹MeasurableSpace Ω› :=
    (thm_5_11_tail_le_full X).trans (iSup_le fun i => (h_meas i).comap_le)
  have hprefix_directed : Directed (· ≤ ·) (prefixSigmaAlgebra X) :=
    (thm_5_11_prefix_mono X).directed_le
  have hsup := ProbabilityTheory.indep_iSup_of_directed_le
    hprefix hprefix_le htail_le hprefix_directed
  rw [thm_5_11_iSup_prefix_eq_full X] at hsup
  exact hsup

theorem thm_5_11_tail_indep_self
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (X : ℕ → Ω → β) (h_meas : ∀ n, Measurable (X n))
    (h_indep : ProbabilityTheory.iIndepFun X P) :
    ProbabilityTheory.Indep (tailSigmaAlgebra X) (tailSigmaAlgebra X) P :=
  ProbabilityTheory.indep_of_indep_of_le_left
    (thm_5_11_full_indep_tail P X h_meas h_indep)
    (thm_5_11_tail_le_full X)

theorem thm_5_11 {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (X : ℕ → Ω → β) (h_meas : ∀ n, Measurable (X n))
    (h_indep : ProbabilityTheory.iIndepFun X P) {t : Set Ω}
    (ht_tail : @MeasurableSet Ω (tailSigmaAlgebra X) t) :
    P t = 0 ∨ P t = 1 := by
  have hself := thm_5_11_tail_indep_self P X h_meas h_indep
  exact ProbabilityTheory.measure_eq_zero_or_one_of_indepSet_self
    (hself.indepSet_of_measurableSet ht_tail ht_tail)
